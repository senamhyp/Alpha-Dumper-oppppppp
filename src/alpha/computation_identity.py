import ast
import hashlib
import importlib.util
import sys
from pathlib import Path


def computation_digest(roots: tuple[tuple[str, str], ...], *, source_root: Path | None = None) -> str:
    source_root = source_root or Path(__file__).parent
    digest = hashlib.sha256(b'alpha.computation-source/v1\0')
    digest.update(Path(__file__).read_bytes())
    digest.update(sys.version.encode())
    modules = {}
    pending = list(roots)
    if (source_root / '__init__.py').exists():
        pending.append(('alpha.__init__', '*'))
    seen = set()
    externals = set()

    def load(module):
        if module in modules:
            return modules[module]
        if not module.startswith('alpha.') or '.' in module[6:]:
            raise ValueError('unsupported computation module')
        path = source_root / (module[6:] + '.py')
        tree = ast.parse(path.read_bytes(), filename=str(path))
        bindings = {}
        effects = []
        for node in tree.body:
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names = [node.name]
                if node.decorator_list or any(isinstance(n, ast.Call) for value in (
                    node.bases if isinstance(node, ast.ClassDef) else
                    [*node.args.defaults, *(v for v in node.args.kw_defaults if v is not None)]
                ) for n in ast.walk(value)):
                    effects.append(node)
            elif isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                names = [n.id for target in targets for n in ast.walk(target) if isinstance(n, ast.Name)]
                if node.value is not None and any(isinstance(n, ast.Call) for n in ast.walk(node.value)):
                    effects.append(node)
            elif isinstance(node, (ast.Import, ast.ImportFrom)):
                if isinstance(node, ast.ImportFrom) and node.module == '__future__':
                    effects.append(node)
                names = [alias.asname or alias.name.split('.')[0] for alias in node.names]
            else:
                names = []
                if not isinstance(node, ast.Expr) or not isinstance(node.value, ast.Constant):
                    effects.append(node)
            for name in names:
                bindings.setdefault(name, []).append(node)
        modules[module] = (bindings, effects)


        for node in tree.body:
            if isinstance(node, ast.ImportFrom):
                if node.level or any(a.name == '*' for a in node.names):
                    raise ValueError('unsupported computation import')
                imported = node.module or ''
                if imported.startswith('alpha.'):
                    pending.append((imported, '<initialize>'))
                elif imported == 'alpha':
                    pending.extend(('alpha.' + a.name, '<initialize>') for a in node.names)
                else:
                    externals.add(imported.split('.')[0])
            elif isinstance(node, ast.Import):
                for alias in node.names:
                    if alias.name.startswith('alpha.'):
                        pending.append((alias.name, '<initialize>'))
                    else:
                        externals.add(alias.name.split('.')[0])


        for index, node in enumerate(effects):
            visit(module, f'<effect:{index}>', node)
        return modules[module]

    def visit(module, name, node):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            aliases = [alias for alias in node.names
                       if (alias.asname or alias.name.split('.')[0]) == name]
            if aliases:
                node = (ast.Import(names=aliases) if isinstance(node, ast.Import) else
                        ast.ImportFrom(module=node.module, names=aliases, level=node.level))
        token = (module, name, ast.dump(node, include_attributes=False))
        if token in seen:
            return
        seen.add(token)
        digest.update(module.encode() + b'\0' + name.encode() + b'\0' + token[2].encode() + b'\0')
        bindings, _ = modules[module]
        for item in ast.walk(node):
            if isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load) and item.id in {
                'eval', 'exec', 'globals', 'locals', '__import__'
            }:
                raise ValueError('dynamic computation namespace requires full implementation seal')
            if isinstance(item, ast.ImportFrom):
                imported = item.module or ''
                if item.level or any(a.name == '*' for a in item.names):
                    raise ValueError('unsupported computation import')
                if imported.startswith('alpha.'):
                    pending.extend((imported, a.name) for a in item.names)
                elif imported == 'alpha':
                    pending.extend(('alpha.' + a.name, '*') for a in item.names)
                else:
                    externals.add(imported.split('.')[0])
            elif isinstance(item, ast.Import):
                for alias in item.names:
                    if alias.name.startswith('alpha.'):
                        pending.append((alias.name, '*'))
                    else:
                        externals.add(alias.name.split('.')[0])
            elif isinstance(item, ast.Name) and isinstance(item.ctx, ast.Load) and item.id in bindings:
                pending.append((module, item.id))

    while pending:
        module, name = pending.pop()
        bindings, _ = load(module)
        if name == '<initialize>':
            continue
        if name == '*':
            pending.extend((module, n) for n in bindings)
        elif name not in bindings:
            raise ValueError(f'unresolved computation dependency {module}.{name}')
        else:
            for node in bindings[name]:
                visit(module, name, node)


    for name in sorted(externals):
        if name in sys.stdlib_module_names or name == '__future__':
            continue
        spec = importlib.util.find_spec(name)
        if spec is None or spec.origin is None:
            raise ValueError('unresolved external computation dependency')
        paths = [Path(spec.origin)]
        if spec.submodule_search_locations:
            paths = [p for location in spec.submodule_search_locations
                     for p in Path(location).rglob('*')
                     if p.is_file() and p.suffix in {'.py', '.so', '.dylib', '.dll'}]
        for path in sorted(paths):
            digest.update(str(path).encode() + b'\0' + path.read_bytes() + b'\0')
    return digest.hexdigest()


def legacy_source_matches(work_dir: Path, implementation: str, roots, current_digest: str) -> bool:
    if len(implementation) != 64:
        return False
    snapshots = sorted(work_dir.parent.glob(work_dir.name + '.implementation*'), reverse=True)
    for snapshot in snapshots:
        source = snapshot / 'alpha'
        if not source.is_dir():
            continue
        def full_seal():
            result = hashlib.sha256()
            for path in sorted(source.glob('*.py')):
                result.update(path.name.encode() + b'\0' + path.read_bytes() + b'\0')
            return result.hexdigest()
        try:
            if full_seal() != implementation:
                continue
            if computation_digest(roots, source_root=source) != current_digest:
                return False
            return full_seal() == implementation
        except (OSError, ValueError, SyntaxError, ImportError):
            return False
    return False
