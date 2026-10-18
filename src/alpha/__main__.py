import argparse
from pathlib import Path
from alpha.p01 import run_proto_command


def main() -> int:
    parser = argparse.ArgumentParser()
    commands = parser.add_subparsers(dest="command", required=True)
    dump = commands.add_parser("dump")
    kinds = dump.add_subparsers(dest="kind", required=True)
    proto = kinds.add_parser("proto")
    proto.add_argument("--binary", type=Path)
    proto.add_argument("--wine", type=Path)
    proto.add_argument("--wineprefix", type=Path)
    proto.add_argument("--compiler", type=Path)
    proto.add_argument("--work-dir", type=Path)
    proto.add_argument("--output-dir", type=Path)
    proto.add_argument("--timeout", type=float, default=1800.0)
    proto.add_argument("--resume", action="store_true")
    proto.add_argument("--repair-resume", action="store_true")
    proto.add_argument("--partial-proto-without-field-encrypt", action="store_true")
    proto.add_argument(
        "--carry-forward", action="store_true", dest="carry_forward",
    )
    proto.add_argument(
        "--rebind-live-process", action="store_true", dest="rebind_live_process",
    )
    proto.add_argument(
        "--salvage-restart", action="store_true", dest="salvage_restart",
    )
    proto.add_argument("--rejected-candidates", type=Path, dest="rejected_candidates")
    proto.add_argument("--strict", action="store_true")
    proto.add_argument("--no-guess", action="store_true", dest="no_guess")
    proto.add_argument(
        "--exclude-unresolved", action="store_true", dest="exclude_unresolved",
    )
    proto.add_argument(
        "--semantic-reference", action="append", type=Path,
        dest="semantic_reference",
    )
    proto.add_argument(
        "--with-metadata", action="store_true", dest="with_metadata",
    )
    proto.add_argument(
        "--metadata-output-dir", type=Path, dest="metadata_output_dir",
    )
    proto.add_argument(
        "--skip-metadata-reconstruction", action="store_true",
        dest="skip_metadata_reconstruction",
    )
    proto.add_argument(
        "--metadata-domain-observation", type=Path, action="append",
        dest="metadata_domain_observation", default=[],
    )
    proto.add_argument(
        "--reachable-heap-limit-mib", type=int, default=0,
        dest="reachable_heap_limit_mib",
    )
    args = parser.parse_args()
    if args.repair_resume and not args.resume:
        parser.error("--repair-resume requires --resume")
    if args.carry_forward and not args.repair_resume:
        parser.error("--carry-forward requires --repair-resume")
    if getattr(args, "rebind_live_process", False) and not args.resume:
        parser.error("--rebind-live-process requires --resume")
    if getattr(args, "salvage_restart", False) and not (
        args.resume and args.repair_resume
    ):
        parser.error("--salvage-restart requires --resume --repair-resume")
    return run_proto_command(args)


if __name__ == "__main__":
    raise SystemExit(main())
