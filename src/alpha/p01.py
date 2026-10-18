def generic_attributes_valid(value, *, method_owned):

    return (type(value) is int and 0 <= value <= 31 and type(method_owned) is bool
        and (value & 3) != 3 and (not method_owned or not value & 3))


NATIVE_ATTRIBUTE_VALIDATION = r'''
static int generic_attributes_valid(uint64_t index,uint32_t value) {
    if(index>=expected_argument_count || value&~31u || (value&3u)==3u)return 0;
    return index>=expected_method_argument_count || !(value&3u);
}
'''

from string import Template

NATIVE_PROBE = Template(r'''
static const uint32_t carried_attribute = ${carried_attribute}u;
static const uint32_t carried_constraint = ${carried_constraint}u;

static int probe_candidates(void) {
    uint32_t attribute_valid[ATTRIBUTE_CANDIDATES], constraint_valid[CONSTRAINT_CANDIDATES];
    uint64_t constraint_total[CONSTRAINT_CANDIDATES];
    selected_attribute = selected_constraint = 0xffffffffu;
    attribute_equivalent_count = constraint_equivalent_count = 0;
    if (!expected_argument_count) { failure_kind=7u; return 0; }
    if (carried_attribute < ATTRIBUTE_CANDIDATES &&
        carried_constraint < CONSTRAINT_CANDIDATES) {
        /* Accessor selection is a property of the client build.  When the
           sealed single-survivor evidence from the earlier domain is bound
           and the candidate topology matched, the carried selection is used
           directly instead of re-deriving it on a probe sample that the
           type-graph open classification may legitimately empty. */
        selected_attribute = carried_attribute;
        selected_constraint = carried_constraint;
        attribute_equivalent_count = 1;
        constraint_equivalent_count = 1;
        return 1;
    }
    for (uint32_t c=0;c<ATTRIBUTE_CANDIDATES;c++) attribute_valid[c]=1u;
    for (uint32_t c=0;c<CONSTRAINT_CANDIDATES;c++) {
        constraint_valid[c]=1u; constraint_total[c]=0;
    }
    for (uint64_t i=0;i<expected_argument_count;i++) {
        InterlockedExchange(&probe_stage,1);
        InterlockedExchange(&probe_candidate,0);
        uintptr_t object=type_object(argument_descriptors[i]);
        if (!object) {
            /* An open generic parameter that the runtime handle factory
               cannot resolve is carried by the type graph; probing it is
               skipped instead of failing the candidate selection. */
            if (argument_is_open(i)) { InterlockedIncrement(&probe_progress); continue; }
            failure_kind=1u; failure_index=i+1u; return 0;
        }
        InterlockedIncrement(&probe_progress);
        InterlockedExchange(&probe_stage,2);
        for (uint32_t c=0;c<ATTRIBUTE_CANDIDATES;c++) {
            if (!attribute_valid[c]) continue;
            InterlockedExchange(&probe_candidate,(LONG)c);
            InterlockedExchange(&probe_stage,3);
            uint32_t value=((instance_dword)attribute_pointers[c])(object,attribute_metadata[c]);
            InterlockedExchange(&probe_stage,4);
            if (!generic_attributes_valid(i,value)) attribute_valid[c]=0;
        }
        for (uint32_t c=0;c<CONSTRAINT_CANDIDATES;c++) {
            if (!constraint_valid[c]) continue;
            InterlockedExchange(&probe_candidate,(LONG)c);
            InterlockedExchange(&probe_stage,5);
            uintptr_t array=((instance_noarg)constraint_pointers[c])(object,constraint_metadata[c]);
            InterlockedExchange(&probe_stage,6);
            uintptr_t *items=NULL; uint32_t count=0;
            if (!type_array(array,&items,&count)) { constraint_valid[c]=0; continue; }
            uint64_t descriptors[ALPHA_MAX_CONSTRAINTS]={0};
            for (uint32_t j=0;j<count;j++) {
                if (!descriptor_from_type(items[j],&descriptors[j])) { constraint_valid[c]=0; break; }
                for (uint32_t k=0;k<j;k++)
                    if (descriptors[j]==descriptors[k]) constraint_valid[c]=0;
            }
            constraint_total[c]+=count;
        }
    }
    for (uint32_t c=0;c<ATTRIBUTE_CANDIDATES;c++) if (attribute_valid[c]) {
        selected_attribute=c; attribute_equivalent_count++;
    }


    for (uint32_t c=0;c<CONSTRAINT_CANDIDATES;c++)
        if (constraint_valid[c] && constraint_total[c]) {
            selected_constraint=c; constraint_equivalent_count++;
        }
    if (attribute_equivalent_count!=1) { failure_kind=2u; return 0; }
    if (constraint_equivalent_count!=1) { failure_kind=5u; return 0; }
    return 1;
}
''')


NATIVE_GLOBALS = r'''
static volatile LONG request_sequence,current_request,callback_active,probe_progress;
static volatile LONG candidate_attempts,candidate_action,candidate_outcome,candidate_busy;
static volatile LONG probe_stage,probe_candidate;
'''

NATIVE_WINDOW_PROC = r'''
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam) {
    if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);
    LONG request=(LONG)wparam;
    if(!request || InterlockedCompareExchange(&current_request,0,0)!=request ||
       InterlockedCompareExchange(&callback_active,1,0))return 0;
    if(InterlockedCompareExchange(&current_request,0,request)!=request) {
        InterlockedExchange(&callback_active,0);return 0;
    }
    LONG selected=InterlockedCompareExchange(&action,0,0);
    int ok=generic_instance_current() && (selected==1?probe_candidates():
        selected==2?capture_batch():selected==3?verify_batch():0);
    InterlockedExchange(&complete,ok?1:-1);
    InterlockedExchange(&callback_active,0);
    return ok;
}
'''

NATIVE_SEND_ACTION = r'''
static int send_action(HWND window,LONG selected) {
    for(uint32_t attempt=0;attempt<17u;attempt++) {
        InterlockedIncrement(&candidate_attempts);
        InterlockedExchange(&candidate_action,selected);
        if(!generic_instance_current()) { failure_kind=310u;return 0; }
        for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0)&&wait<2000u;wait++)Sleep(1);
        if(InterlockedCompareExchange(&callback_active,0,0)){
            Sleep(50);
            if(attempt==16u){failure_kind=310u;return 0;}
            continue;
        }
        LONG request=InterlockedIncrement(&request_sequence);
        if(request<=0){failure_kind=311u;return 0;}
        DWORD_PTR result=0;
        InterlockedExchange(&action,selected);
        InterlockedExchange(&complete,0);
        InterlockedExchange(&current_request,request);
        SetLastError(0);
        int sent=SendMessageTimeoutW(window,message_id,(WPARAM)request,0,
            SMTO_BLOCK,60000,&result)!=0;
        DWORD error=GetLastError();
        InterlockedCompareExchange(&current_request,0,request);
        /* A behaviour probe may call into the runtime hundreds of thousands of
           times.  The callback is monitored through its progress counter, so a
           slow but advancing probe is waited out while a genuinely stuck call
           is still detected. */
        LONG baseline=InterlockedCompareExchange(&probe_progress,0,0);
        LONG outcome=0;
        for(uint32_t quiet=0;quiet<300000u;){
            outcome=InterlockedCompareExchange(&complete,0,0);
            if(outcome)break;
            LONG progress=InterlockedCompareExchange(&probe_progress,0,0);
            if(progress!=baseline){baseline=progress;quiet=0;}
            else quiet++;
            Sleep(1);
        }
        if(!outcome){
            for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0)&&wait<2000u;wait++)Sleep(1);
            InterlockedExchange(&candidate_outcome,outcome);
            InterlockedExchange(&candidate_busy,InterlockedCompareExchange(&callback_active,0,0));
            if(InterlockedCompareExchange(&callback_active,0,0)){
                /* A concurrent nested or duplicate delivery can consume the
                   request without completing it; resample with a fresh request
                   id instead of failing the whole capture. */
                Sleep(50);
                if(attempt==16u){failure_kind=312u;return 0;}
                continue;
            }
        }
        if(outcome==1)return generic_instance_current();
        if(outcome<0 || failure_kind)return 0;
        InterlockedExchange(&candidate_outcome,outcome);
        InterlockedExchange(&candidate_busy,InterlockedCompareExchange(&callback_active,0,0));
        if(sent || attempt==16u){failure_kind=313u;failure_index=error;return 0;}
        Sleep(250);
    }
    return 0;
}
'''

NATIVE_DISPATCH = r'''
static void write_candidate_probe(void) {
    wchar_t path[32768];
    if(swprintf(path,32768,L"%ls.probe.json",status_path)<0)return;
    FILE*out=_wfopen(path,L"wb");
    if(!out)return;
    fprintf(out,"{\n  \"attempts\": %ld,\n  \"action\": %ld,\n  \"outcome\": %ld,\n  \"busy\": %ld,\n  \"progress\": %ld,\n  \"probe_stage\": %ld,\n  \"probe_candidate\": %ld,\n  \"failure_kind\": %u,\n  \"failure_index\": %llu\n}\n",
        (long)InterlockedCompareExchange(&candidate_attempts,0,0),
        (long)InterlockedCompareExchange(&candidate_action,0,0),
        (long)InterlockedCompareExchange(&candidate_outcome,0,0),
        (long)InterlockedCompareExchange(&candidate_busy,0,0),
        (long)InterlockedCompareExchange(&probe_progress,0,0),
        (long)InterlockedCompareExchange(&probe_stage,0,0),
        (long)InterlockedCompareExchange(&probe_candidate,0,0),
        failure_kind,(unsigned long long)failure_index);
    fclose(out);_wchmod(path,0600);
}
static int dispatch(void) {
    selection s={0};s.pid=GetCurrentProcessId();
    if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window) {
        failure_kind=100u;failure_index=s.count;return 0;
    }
    message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime generic parameter detail inventory");
    if(!message_id){failure_kind=302u;return 0;}
    SetLastError(0);
    original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);
    DWORD error=GetLastError();
    if(!original_proc||error!=ERROR_SUCCESS){failure_kind=303u;failure_index=error;return 0;}
    int ok=send_action(s.window,1);
    while(ok&&capture_index<expected_argument_count) {
        uint64_t before=capture_index;ok=send_action(s.window,2);
        if(ok&&capture_index<=before){failure_kind=308u;ok=0;}
    }
    while(ok&&verify_index<expected_argument_count) {
        uint64_t before=verify_index;ok=send_action(s.window,3);
        if(ok&&verify_index<=before){failure_kind=309u;ok=0;}
    }
    InterlockedExchange(&current_request,0);

    if((WNDPROC)(uintptr_t)GetWindowLongPtrW(s.window,GWLP_WNDPROC)!=window_proc) {
        failure_kind=314u;return 0;
    }
    SetLastError(0);
    WNDPROC replaced=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);
    if(replaced!=window_proc || GetLastError()!=ERROR_SUCCESS){failure_kind=315u;ok=0;}


    write_candidate_probe();
    return ok&&!InterlockedCompareExchange(&callback_active,0,0);
}
'''


def allocation_codec_slots(code, *, code_address=0, with_evidence=False):
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64
    from capstone.x86 import X86_OP_REG, X86_OP_IMM, X86_OP_MEM, X86_REG_RIP
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    registers, objects, output, offsets, evidence = {}, {}, {}, {}, {}
    serial = 0
    volatile = {"rax", "rcx", "rdx", "r8", "r9", "r10", "r11"}
    def reg(ins, value):
        name = ins.reg_name(value)
        aliases = {"eax":"rax", "ecx":"rcx", "edx":"rdx", "ebx":"rbx",
                   "esi":"rsi", "edi":"rdi", "ebp":"rbp", "esp":"rsp"}
        return aliases.get(name, name[:-1] if name.startswith("r") and name.endswith("d") else name)
    for ins in decoder.disasm(code, code_address):
        ops = ins.operands
        if ins.mnemonic == "call":
            for name in volatile: registers.pop(name, None)
            serial += 1
            objects[serial] = set()
            offsets[serial] = {}
            registers["rax"] = ("object", serial)
            continue
        handled = False
        if ins.mnemonic == "mov" and len(ops) == 2:
            dst, src = ops
            if dst.type == X86_OP_REG:
                name = reg(ins, dst.reg)
                value = registers.get(reg(ins, src.reg)) if src.type == X86_OP_REG else None
                registers.pop(name, None)
                if dst.size == 8 and src.type == X86_OP_REG:
                    if value is not None: registers[name] = value
                elif src.type == X86_OP_IMM:
                    registers[name] = ("constant", src.imm & ((1 << (dst.size*8))-1))
                elif src.type == X86_OP_REG and value and value[0] == "constant":
                    registers[name] = ("constant", value[1] & ((1 << (dst.size*8))-1))
                elif dst.size == 8 and src.type == X86_OP_MEM and src.mem.base == X86_REG_RIP:
                    registers[name] = ("static-base", ins.address + ins.size + src.mem.disp)
                handled = True
            elif dst.type == X86_OP_MEM and not dst.mem.index:
                base = registers.get(reg(ins, dst.mem.base))
                if base and base[0] == "object" and dst.size == 4 and dst.mem.disp >= 16:
                    value = ("constant",src.imm) if src.type == X86_OP_IMM else (
                        registers.get(reg(ins,src.reg)) if src.type == X86_OP_REG else None)
                    if not value or value[0] != "constant":
                        objects[base[1]].add(None)
                    else:
                        tag = value[1] & 0xffffffff
                        if 0 < tag >> 3 <= 0x1fffffff and tag & 7 in range(8):
                            objects[base[1]].add(tag)
                            offsets[base[1]].setdefault(tag,set()).add(dst.mem.disp)
                elif (base and base[0] == "static-base" and dst.size == 8
                      and dst.mem.disp >= 0x1000 and src.type == X86_OP_REG):
                    value = registers.get(reg(ins, src.reg))
                    tags = objects.get(value[1], set()) if value and value[0] == "object" else set()
                    if len(tags) == 1 and None not in tags:
                        slot, tag = dst.mem.disp, next(iter(tags))
                        if slot in output and output[slot] != tag:
                            raise ValueError("constructor allocation has conflicting codec tags")
                        output[slot] = tag
                        evidence[slot] = {"raw_tag":tag, "tag_offsets":sorted(offsets[value[1]][tag]),
                                          "static_base_pointer_slot":base[1]}
                handled = True
        if not handled:
            _, written = ins.regs_access()
            for value in written: registers.pop(reg(ins, value), None)
        if ins.mnemonic in {"ret", "jmp", "int3"}:
            registers.clear()
    return evidence if with_evidence else output


GLOBALS = """
static volatile LONG request_sequence,current_request,callback_active;
static volatile LONG probe_exception_code,probe_phase;
static volatile LONG dispatch_attempt,dispatch_error;
static void write_progress(const char*status);
static int guarded_capture_batch(void);
"""

WINDOW_PROC = """
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){
    if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);
    LONG request=(LONG)wp;
    if(!request||InterlockedCompareExchange(&current_request,0,0)!=request||
       InterlockedCompareExchange(&callback_active,1,0))return 0;
    if(InterlockedCompareExchange(&current_request,0,request)!=request){
        InterlockedExchange(&callback_active,0);return 0;
    }
    write_progress("callback_running");
    int ok=guarded_capture_batch();
    InterlockedExchange(&callback_complete,ok?1:-1);
    InterlockedExchange(&callback_active,0);
    return ok;
}
"""

DISPATCH = """
static int dispatch(void){
    selection s={0};s.pid=GetCurrentProcessId();
    if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)
        return failure_kind=20,0;
    message_id=RegisterWindowMessageW(status_path);
    if(!message_id)return failure_kind=20,0;
    SetLastError(0);
    original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);
    if(!original_proc)return failure_kind=20,0;
    int ok=1;uint32_t transient_failures=0;
    while(ok){

        if(InterlockedCompareExchange(&callback_active,0,0)){ok=0;break;}
        if(message_cursor>=message_count)break;
        uint64_t before=completed_probes;
        LONG request=InterlockedIncrement(&request_sequence);
        if(request<=0){failure_kind=22;ok=0;break;}
        InterlockedExchange(&callback_complete,0);
        InterlockedExchange(&current_request,request);
        DWORD_PTR result=0;
        InterlockedIncrement(&dispatch_attempt);
        InterlockedExchange(&dispatch_error,0);
        write_progress("waiting_window_dispatch");
        SetLastError(ERROR_SUCCESS);
        int sent=SendMessageTimeoutW(s.window,message_id,(WPARAM)request,0,SMTO_BLOCK,5000,&result)!=0;
        if(!sent)InterlockedExchange(&dispatch_error,(LONG)GetLastError());

        InterlockedCompareExchange(&current_request,0,request);

        for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0);wait++){
            if(wait>=60000u){failure_kind=26;write_progress("callback_stalled_restart_required");return 0;}
            if(wait%1000u==0)write_progress("waiting_callback");
            Sleep(1);
        }
        LONG callback=InterlockedCompareExchange(&callback_complete,0,0);
        if(callback==1){
            if(completed_probes==before&&message_cursor<message_count){failure_kind=23;ok=0;break;}
            transient_failures=0;write_progress("capturing");Sleep(0);continue;
        }
        if(callback==-1||failure_kind){ok=0;break;}
        if(!sent&&transient_failures++<11u)continue;
        failure_kind=21;ok=0;
    }
    InterlockedExchange(&current_request,0);
    if(InterlockedCompareExchange(&callback_active,0,0)){
        failure_kind=26;write_progress("callback_stalled_restart_required");return 0;
    }
    if((WNDPROC)(uintptr_t)GetWindowLongPtrW(s.window,GWLP_WNDPROC)!=window_proc)
        return failure_kind=24,0;
    if((WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc)!=window_proc)
        return failure_kind=25,0;
    return ok;
}
"""


GUARD = r'''
#include <excpt.h>
static int __attribute__((used)) probe_exception_filter(EXCEPTION_POINTERS*e,void*frame){
    (void)frame;
    DWORD code=e->ExceptionRecord->ExceptionCode;
    InterlockedExchange(&probe_exception_code,(LONG)code);


    return code==0xe06d7363u || code==0xc0000005u ||
        code==0xc0000006u || code==0x80000002u
        ? EXCEPTION_EXECUTE_HANDLER : EXCEPTION_CONTINUE_SEARCH;
}


static int __attribute__((noinline,optimize("O0"))) guarded_capture_batch(void){
    volatile int ok=0;
    __try1(probe_exception_filter)
    ok=capture_batch();
    __except1
    if(!ok&&!failure_kind)failure_kind=27;
    return ok;
}
'''

PROGRESS = r'''
static void write_progress(const char*status){
    static ULONGLONG last;
    ULONGLONG now=GetTickCount64();
    if(now-last<1000u && !failure_kind)return;
    last=now;
    wchar_t path[32768],pending[32768];
    if(swprintf(path,32768,L"%ls.progress.json",status_path)<0 ||
       swprintf(pending,32768,L"%ls.pending",path)<0)return;
    FILE*f=_wfopen(pending,L"wb");if(!f)return;
    fprintf(f,"{\"schema\":\"alpha.runtime-proto-mutation-progress/v1\","
        "\"status\":\"%s\",\"completed_probe_count\":%llu,\"expected_probe_count\":%llu,"
        "\"message_index\":%u,\"number\":%u,\"wire\":%u,\"phase\":%ld,"
        "\"callback_active\":%ld,\"exception_code\":%lu,\"failure_kind\":%u}\n",
        status,(unsigned long long)completed_probes,(unsigned long long)expected_probe_count,
        failure_message,failure_number,failure_wire,(long)InterlockedCompareExchange(&probe_phase,0,0),
        (long)InterlockedCompareExchange(&callback_active,0,0),
        (unsigned long)InterlockedCompareExchange(&probe_exception_code,0,0),failure_kind);
    if(fclose(f)){_wremove(pending);return;}
    _wchmod(pending,0600);
    if(!MoveFileExW(pending,path,MOVEFILE_REPLACE_EXISTING|MOVEFILE_WRITE_THROUGH))_wremove(pending);
}
'''


MEMORY_CHECKS = r'''
static int accessible(uintptr_t v,SIZE_T n,int write){
    if(!v||!n||v+n<v)return 0;
    uintptr_t end=v+n;
    while(v<end){
        MEMORY_BASIC_INFORMATION r;
        if(!VirtualQuery((const void*)v,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;
        DWORD p=r.Protect&0xffu;
        int rw=p==PAGE_READWRITE||p==PAGE_WRITECOPY||p==PAGE_EXECUTE_READWRITE||p==PAGE_EXECUTE_WRITECOPY;
        if(write?!rw:!(rw||p==PAGE_READONLY||p==PAGE_EXECUTE_READ))return 0;
        uintptr_t next=(uintptr_t)r.BaseAddress+r.RegionSize;
        if(next<=v)return 0;
        v=next<end?next:end;
    }
    return 1;
}
static int readable(uintptr_t v,SIZE_T n){return accessible(v,n,0);}
static int stream_writable(uintptr_t stream){
    const uint32_t offsets[]={stream_null_offset,stream_array_offset,stream_zero_offset,stream_length_offset,stream_bool_offset};
    const SIZE_T widths[]={8u,8u,4u,4u,1u};
    for(unsigned i=0;i<5u;i++){
        uintptr_t p=stream+offsets[i];
        if(p<stream||!accessible(p,widths[i],1))return 0;
    }
    return 1;
}
'''


def harden_serializer_memory(source):
    start=source.index('static int readable(')
    end=source.index('static uintptr_t byte_array(',start)
    source=source[:start]+MEMORY_CHECKS+source[end:]
    old='if(!output||!stream||!readable(stream,0x80u))return 0;'
    if source.count(old)!=1:
        raise ValueError('serializer allocation check shape changed')

    source=source.replace(old,
        'if(!output)return debug_tag=101u,0;'
        'if(!stream)return debug_tag=102u,0;'
        'if(!stream_writable(stream))return debug_tag=103u,0;')
    return source


SNAPSHOT_C = r'''
static int snapshot_copy(uintptr_t address,void*output,SIZE_T bytes){
    SIZE_T copied=0;
    if(!address||!bytes||address>UINTPTR_MAX-bytes)return 0;
    return ReadProcessMemory(GetCurrentProcess(),(const void*)address,output,bytes,&copied)&&copied==bytes;
}
static int take_snapshot(uintptr_t message,const probe_field*f,field_snapshot*out){
    memset(out,0,sizeof(*out));
    SIZE_T bytes=storage_bytes(f->type_enum);
    if(bytes>sizeof(out->storage)||message>UINTPTR_MAX-f->offset)return 0;
    if(!snapshot_copy(message+f->offset,&out->storage,bytes))return 0;
    out->storage_hash=hash_bytes(1469598103934665603ull,&out->storage,bytes);
    if(!reference_type(f->type_enum))return 1;
    out->root=out->storage;if(!out->root)return 1;
    unsigned char root[ALPHA_REFERENCE_BYTES];SIZE_T root_bytes=sizeof(root);
    if(!snapshot_copy(out->root,root,root_bytes)){
        root_bytes=16u;if(!snapshot_copy(out->root,root,root_bytes))return 0;
    }
    memcpy(&out->class_pointer,root,8u);
    uint64_t h=hash_bytes(1469598103934665603ull,root,root_bytes);
    for(SIZE_T offset=16u;offset<=32u&&offset+8u<=root_bytes;offset+=8u){
        uintptr_t child=0,klass=0;unsigned char child_bytes[64],class_bytes[64];
        memcpy(&child,root+offset,8u);
        if(!snapshot_copy(child,child_bytes,sizeof(child_bytes)))continue;
        memcpy(&klass,child_bytes,8u);
        if(!snapshot_copy(klass,class_bytes,sizeof(class_bytes)))continue;
        h=hash_bytes(h,child_bytes,sizeof(child_bytes));
    }
    out->reference_hash=h;return 1;
}
'''


def harden_snapshot_reads(source):
    from alpha.h01 import AcquisitionError
    lines=[line for line in source.splitlines() if line.startswith('static int take_snapshot(')]
    if len(lines)!=1:
        raise AcquisitionError('mutation snapshot source contract changed')
    return source.replace(lines[0],SNAPSHOT_C,1)


from collections import deque


def unused_receiver_slot(code, offset, width=8, *, terminal_call=None):
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64
    from capstone.x86 import X86_OP_REG, X86_OP_MEM, X86_OP_IMM
    if not code or offset < 16 or width < 1:
        return False
    decoder=Cs(CS_ARCH_X86,CS_MODE_64);decoder.detail=True
    ins=list(decoder.disasm(code,0));by={x.address:x for x in ins}
    if sum(x.size for x in ins)!=len(code):
        return False
    def reg(x):
        name=decoder.reg_name(x) or ''
        aliases={'eax':'rax','ecx':'rcx','edx':'rdx','ebx':'rbx','esi':'rsi','edi':'rdi','ebp':'rbp','esp':'rsp'}
        if name in aliases:return aliases[name]
        if name.startswith('r') and name[1:-1].isdigit() and name[-1:] in ('d','w','b'):return name[:-1]
        return name
    states={0:frozenset({('rcx',0)})};queue=deque([0]);steps=0
    args={'rcx','rdx','r8','r9'};volatile=args|{'rax','r10','r11'}
    while queue:
        pc=queue.popleft();steps+=1
        if steps>len(ins)*32 or pc not in by:return False
        x=by[pc];roots=set(states[pc]);ops=x.operands
        root_names={r for r,_ in roots}
        def clear(names):
            roots.difference_update({pair for pair in roots if pair[0] in names})
        for op in ops:
            if op.type!=X86_OP_MEM:continue
            base=reg(op.mem.base);index=reg(op.mem.index)
            if index in root_names:return False
            if base not in root_names:continue
            if op.mem.index:return False
            if x.mnemonic=='lea':continue
            for _,delta in [p for p in roots if p[0]==base]:
                address=delta+op.mem.disp
                if address < offset+width and address+op.size > offset:return False
        if x.mnemonic in ('call','jmp'):
            if len(ops)!=1:return False
            internal=x.mnemonic=='jmp' and ops[0].type==X86_OP_IMM and ops[0].imm in by
            if not internal and root_names & args:
                if ops[0].type==X86_OP_IMM and terminal_call and terminal_call(ops[0].imm):
                    continue
                return False
            if x.mnemonic=='call':clear(volatile)
        elif x.mnemonic=='push':
            if ops and ops[0].type==X86_OP_REG and reg(ops[0].reg) in root_names:return False
        elif x.mnemonic=='lea' and len(ops)==2 and ops[0].type==X86_OP_REG and ops[1].type==X86_OP_MEM:
            src=[delta+ops[1].mem.disp for r,delta in roots if r==reg(ops[1].mem.base)]
            dst=reg(ops[0].reg);clear({dst})
            if src:
                if ops[1].mem.index or ops[0].size!=8:return False
                roots.update((dst,d) for d in src)
        elif x.mnemonic=='mov' and len(ops)==2:
            src=[d for r,d in roots if ops[1].type==X86_OP_REG and r==reg(ops[1].reg)]
            if src and ops[0].type!=X86_OP_REG:return False
            if ops[0].type==X86_OP_REG:
                dst=reg(ops[0].reg);clear({dst})
                if src:
                    if ops[0].size!=8 or ops[1].size!=8:return False
                    roots.update((dst,d) for d in src)
        else:
            _,writes=x.regs_access()
            changed={reg(r) for r in writes}&root_names
            if changed:

                if x.mnemonic=='xor' and len(ops)==2 and all(o.type==X86_OP_REG for o in ops) and ops[0].reg==ops[1].reg:
                    clear(changed)
                elif x.mnemonic=='pop':
                    clear(changed)
                else:return False
        if x.mnemonic.startswith('ret'):
            if any(r=='rax' for r,_ in roots):return False
            continue
        if x.mnemonic in ('int3','ud2'):continue
        next_pc=pc+x.size
        if x.mnemonic=='jmp':
            if ops[0].type!=X86_OP_IMM:return False
            successors=[ops[0].imm] if ops[0].imm in by else []
        elif x.mnemonic.startswith('j'):
            if len(ops)!=1 or ops[0].type!=X86_OP_IMM or ops[0].imm not in by:return False
            successors=[next_pc,ops[0].imm]
        else:successors=[next_pc]
        for successor in successors:
            if successor not in by:return False
            merged=states.get(successor,frozenset())|frozenset(roots)
            if successor not in states or merged!=states[successor]:
                states[successor]=merged;queue.append(successor)
    return True


def validate_exclusions(
    runtime, analysis, fields, indexes, binary,
    runtime_evidence=None,
):

    import hashlib
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64
    from alpha.p29 import _bounded_code
    from alpha.c04 import MappedPE
    from alpha.h01 import AcquisitionError
    messages={int(m['type_index']):m for m in analysis['messages_owner_only']}
    runtime_evidence = dict(runtime_evidence or {})
    if set(runtime_evidence) != set(indexes):
        raise AcquisitionError('nonserialized exclusion evidence domain differs')
    sizes={}
    owners={fields[index]['owner_type_index'] for index in indexes}
    for i in range(runtime.method_count):
        row=runtime.method_row(i)
        if row[0] in owners and not row[10] and not row[5]&0x10 and not row[9]&1 and runtime.method_return(i)=='System.Int32':
            sizes.setdefault(row[0],[]).append(i)
    evidence=[]
    with MappedPE(binary) as image:
        for index in sorted(indexes):
            field=fields[index];owner=field['owner_type_index']
            source = runtime_evidence[index]
            if source == 'runtime-merge-from-exhaustive-no-storage-mutation/v1':
                evidence.append({
                    'field_index': index,
                    'owner_type_index': owner,
                    'object_offset': field['managed_offset']+16,
                    'checked_width': 8,
                    'methods': [],
                    'resolution': source,
                    'scope': (
                        'all current-runtime bounded parser tags and every '
                        'wire compatible with the captured field type'
                    ),
                })
                continue
            writer=messages.get(owner,{}).get('write_to_method_index')
            if writer is None or len(sizes.get(owner,[]))!=1:
                raise AcquisitionError(
                    'nonserialized exclusion lacks unique writer/size methods '
                    f'for field {index} ({source})'
                )
            methods=[]
            for method_index in [writer,sizes[owner][0]]:
                method=runtime.method_row(method_index);code=_bounded_code(image,method[3])
                terminal_helpers={}
                def terminal(target):
                    pointer=(method[3]+target)&((1<<64)-1)
                    body=_bounded_code(image,pointer)
                    if not body or len(body)>32:return False
                    instructions=list(Cs(CS_ARCH_X86,CS_MODE_64).disasm(body,0))


                    if [x.mnemonic for x in instructions]!=['sub','call','int3']:return False
                    terminal_helpers[str(pointer)]={'sha256':hashlib.sha256(body).hexdigest(),'bytes':len(body)}
                    return True
                if not unused_receiver_slot(code,field['managed_offset']+16,terminal_call=terminal):
                    raise AcquisitionError(f'nonserialized exclusion is unproven for field {index}, method {method_index}')
                methods.append({'method_index':method_index,'pointer':method[3],
                    'bytes':len(code),'sha256':hashlib.sha256(code).hexdigest(),
                    'terminal_helpers':terminal_helpers})
            evidence.append({'field_index':index,'owner_type_index':owner,
                'object_offset':field['managed_offset']+16,'checked_width':8,
                'methods':methods,'resolution':'empty-runtime-output-and-bounded-receiver-dataflow',
                'scope':'normal-returning-generated-serializer-paths-under-Windows-x64-ABI',
                'assumptions':['no hidden receiver aliases through globals or unrelated heap fields',
                               'terminal exception/trap paths do not resume as successful serialization']})
    return evidence


from contextlib import contextmanager
from contextvars import ContextVar


_CACHE = ContextVar("current_string_layout_source_replays", default=None)


@contextmanager
def string_layout_replay_scope():
    if _CACHE.get() is not None:
        yield
        return
    token = _CACHE.set({})
    try:
        yield
    finally:
        _CACHE.reset(token)


def current_string_layout_replay_cache():
    return _CACHE.get()


from alpha.h01 import AcquisitionError


def project_fields(*, observed_fields, prefixes, references, owners, template_fields, attribute_layout):
    offset = attribute_layout.get("descriptor_attribute_offset")
    width = attribute_layout.get("descriptor_attribute_bytes")
    if (type(offset) is not int or type(width) is not int or width <= 0 or offset < 0 or offset + width > 16
            or not owners or not references):
        raise AcquisitionError("constructed field reference projection inputs are incomplete")
    templates = {}
    for row in template_fields:
        if len(row) != 10: raise AcquisitionError("constructed field reference template record is truncated")
        key = (row[0], row[1])
        if key in templates: raise AcquisitionError("constructed field reference template identity is invalid")
        templates[key] = row
    cursors = dict.fromkeys(owners, 0); pointers = set(); result = []
    for row in observed_fields:
        owner, ordinal, pointer, descriptor = (row.get(key) for key in ("generic_index", "field_ordinal", "field_metadata_pointer", "descriptor"))
        if owner not in owners or ordinal != cursors[owner] or pointer in pointers or not pointer:
            raise AcquisitionError("constructed field reference observation identity/order differs")
        definition, field_count = owners[owner]
        if ordinal >= field_count: raise AcquisitionError("constructed field reference exceeds owner field count")
        template = templates.get((definition, ordinal))
        reference = references.get(descriptor)
        prefix = prefixes.get(descriptor)
        if (template is None or reference is None or len(reference) != 19 or reference[0] != descriptor
                or not reference[2] or not isinstance(prefix, bytes) or len(prefix) != 16):
            raise AcquisitionError("constructed field reference native/TypeRef evidence is missing")
        attributes = int.from_bytes(prefix[offset:offset + width], "little")
        if attributes != template[5]: raise AcquisitionError("constructed native field attributes differ from definition")
        result.append(dict(generic_index=owner, definition_index=definition, field_ordinal=ordinal,
            field_metadata_pointer=pointer, descriptor=descriptor, type_object=reference[2], type_shape=reference[4],
            attributes=attributes, definition_field_metadata_pointer=template[2], definition_field_descriptor=template[3]))
        cursors[owner] += 1; pointers.add(pointer)
    if any(cursors[owner] != count for owner, (definition, count) in owners.items()) or not result:
        raise AcquisitionError("constructed field reference projection does not cover owners")
    return dict(fields=result, field_count=len(result), distinct_field_descriptor_count=len({r["descriptor"] for r in result}),
        all_native_field_types_resolved=True, all_native_attributes_equal_definition=True,
        template_substitution_used_as_observation=False, native_layout_complete=False, metadata_complete=False)


from alpha.h01 import ContractViolation


def parent_definition(renderer, descriptor, type_object_roots=None):

    root = renderer.root_by_descriptor.get(descriptor)
    if root is not None:
        return root, 'root-descriptor'
    node = getattr(renderer, 'node_by_descriptor', {}).get(descriptor)
    if node is None:
        return None, 'missing-type-reference'
    row = renderer.reference_row(node)
    from alpha.p25 import TYPE_REFERENCE_GENERIC
    if row[4] & TYPE_REFERENCE_GENERIC:
        from alpha.p20 import observed_generic_parts
        try:
            root, arguments = observed_generic_parts(renderer, row)
        except ContractViolation:
            return None, 'invalid-observed-generic-definition'
        return root, 'observed-generic-definition'
    root = renderer.root_by_descriptor.get(row[1])
    if root is not None:
        return root, 'canonical-descriptor'
    candidates = (type_object_roots or {}).get(row[2], [])
    if len(candidates) == 1:
        return candidates[0], 'same-capture-reflection-type-object'
    return None, 'ambiguous-type-object' if candidates else 'unresolved-canonical-descriptor'


def _serializer_facts(runtime):
    facts = {}
    for index in range(runtime.method_count):
        row = runtime.method_row(index)
        if row[9] & 1 or row[5] & 0x10:
            continue
        owner = row[0]
        item = facts.setdefault(owner, {'size': False, 'writers': set()})
        if row[10] == 0 and runtime.method_return(index) == 'System.Int32':
            item['size'] = True
        elif row[10] == 1 and runtime.method_return(index) == 'System.Void':


            parameter = runtime.parameter_row(row[11])
            if isinstance(parameter[2], int) and parameter[2]:
                item['writers'].add(parameter[2])
    return facts


def _serializer_shape(facts, selected):

    writers = None
    for owner in selected:
        item = facts.get(owner, {})
        found = item.get('writers', set())
        if item.get('size') is not True or not found:
            return None
        writers = found if writers is None else writers & found
        if not writers:
            return None
    return next(iter(writers)) if len(writers) == 1 else None


def _has_serializer_shape(facts, index, writer_descriptor):
    item = facts.get(index, {})
    return item.get('size') is True and writer_descriptor in item.get('writers', set())


def _nonconcrete_serializer_reason(runtime, index):

    if hasattr(runtime.renderer, 'identity_row'):
        attributes = runtime.renderer.identity_row(index)[7]
        if attributes & 0x20:
            return 'interface-contract'
    graph = runtime.renderer.graph_row(index)
    if len(graph) > 7 and graph[7] > 0:
        return 'open-generic-definition'
    return None


def audit_message_domain(
    runtime, base, selected_types, messages, *, writer_descriptor=None
):
    selected = set(selected_types)
    emitted_list = [row['type_index_owner_only'] for row in messages]
    emitted = set(emitted_list)
    base_index = runtime.renderer.root_by_descriptor.get(base)
    descendants = set()
    ancestry_errors = []
    parent_resolutions = {}
    type_object_roots = {}
    if hasattr(runtime.renderer, 'identity_row'):
        for index in range(runtime.type_count):
            pointer = runtime.renderer.identity_row(index)[6]
            if pointer:
                type_object_roots.setdefault(pointer, []).append(index)
    for index in range(runtime.type_count):
        if index == base_index:
            continue
        cursor = index
        visited = set()
        while cursor not in visited:
            visited.add(cursor)
            parent = runtime.renderer.graph_row(cursor)[3]
            if parent == base:
                descendants.add(index)
                break
            if not parent:
                break
            if parent not in parent_resolutions:
                parent_resolutions[parent] = parent_definition(runtime.renderer, parent, type_object_roots)
            parent_index, resolution = parent_resolutions[parent]
            if parent_index is None:


                ancestry_errors.append({'type_index_owner_only': index,
                                        'unresolved_parent_owner_only': parent,
                                        'reason': resolution})
                break
            cursor = parent_index
        else:
            ancestry_errors.append({'type_index_owner_only': index, 'cycle': True})
    exclusions = []
    unexplained = []
    serializer_facts = _serializer_facts(runtime) if hasattr(runtime, 'method_count') else {}
    if writer_descriptor is not None and (
        type(writer_descriptor) is not int or writer_descriptor <= 0
    ):
        raise ContractViolation('message writer descriptor is invalid')
    if writer_descriptor is None:
        writer_descriptor = _serializer_shape(serializer_facts, selected)


    direct_serializer_owners = sorted(
        index for index in range(runtime.type_count)
        if writer_descriptor is not None
        and _has_serializer_shape(serializer_facts, index, writer_descriptor)
    )
    in_domain_serializer_owners = sorted(
        index for index in direct_serializer_owners
        if index == base_index or index in descendants
    )
    contract_descriptors = set()
    interface_inventory_available = hasattr(
        runtime.renderer, 'root_interface_descriptors'
    )
    if interface_inventory_available and selected:
        common = None
        for index in selected:
            interfaces = set(runtime.renderer.root_interface_descriptors(index))
            common = interfaces if common is None else common & interfaces
        contract_descriptors = common or set()
    for index in sorted(descendants - selected):
        interfaces = runtime.renderer.root_interfaces(index)
        graph = runtime.renderer.graph_row(index)
        if len(graph) > 7 and graph[7] > 0:
            exclusions.append({'type_index_owner_only': index,
                               'reason': 'open-generic-definition',


                               'open_generic_arity_owner_only': graph[7],
                               'independently_proven_nonmessage': True})
        elif 'System.Collections.Generic.IEnumerable<System.Byte>' in interfaces:
            exclusions.append({'type_index_owner_only': index,
                               'reason': 'byte-container-interface',


                               'byte_container_interface_observed': True,
                               'independently_proven_nonmessage': True})
        elif writer_descriptor is not None and not _has_serializer_shape(serializer_facts, index, writer_descriptor):


            exclusions.append({'type_index_owner_only': index,
                               'reason': 'missing-derived-message-serializer-contract',
                               'writer_descriptor_owner_only': writer_descriptor,
                               'independently_proven_nonmessage': True})
        else:
            unexplained.append(index)
    within_scope_checks = {
        'selected_equals_emitted': selected == emitted,
        'emitted_type_ids_unique': len(emitted_list) == len(emitted),
        'selected_are_descendants': selected <= descendants,
        'no_unexplained_descendants': not unexplained,
        'all_parent_chains_resolved': not ancestry_errors,
        'unselected_descendants_have_current_runtime_explanation': not unexplained,
    }
    outside_serializer_exclusions = []
    outside_serializer_candidates = []
    contract_implementors = set()
    if contract_descriptors:
        contract_implementors = {
            index for index in range(runtime.type_count)
            if contract_descriptors <= set(
                runtime.renderer.root_interface_descriptors(index)
            )
        }
    for index in sorted(set(direct_serializer_owners) | contract_implementors):
        if index == base_index or index in descendants:
            continue
        reason = _nonconcrete_serializer_reason(runtime, index)
        if reason is None:
            outside_serializer_candidates.append(index)
        else:
            outside_serializer_exclusions.append({
                'type_index_owner_only': index,
                'reason': reason,
                'independently_proven_nonmessage': True,
            })
    outside_verified = (
        hasattr(runtime, 'method_count')
        and writer_descriptor is not None
        and bool(in_domain_serializer_owners)
        and bool(contract_descriptors)
        and not outside_serializer_candidates
    )
    checks = {
        **within_scope_checks,
        'message_writer_descriptor_derived': writer_descriptor is not None,
        'message_serializer_abi_observed_within_domain': bool(in_domain_serializer_owners),
        'message_interface_contract_derived': bool(contract_descriptors),
        'no_outside_base_serializer_candidates': not outside_serializer_candidates,
    }
    unresolved_metadata = []
    if unexplained and hasattr(runtime, 'method_count'):
        methods = {index: [] for index in unexplained}
        for index in range(runtime.method_count):
            row = runtime.method_row(index)
            if row[0] in methods:
                methods[row[0]].append({'method_index_owner_only': index,
                    'name': runtime.method_name(index, row), 'attributes': row[5],
                    'function_pointer_owner_only': row[3],
                    'return_type': runtime.method_return(index),
                    'parameters': runtime.method_parameters(index)})
        for index in unexplained:
            descriptor = runtime.renderer.graph_row(index)[3]
            unresolved_metadata.append({'type_index_owner_only': index,
                'name': runtime.renderer.root_name(index),
                'base_type': runtime.renderer.render(descriptor),
                'base_descriptor_owner_only': descriptor,
                'methods_owner_only': methods[index],
                'serialization_role_verified': False})
    within_scope_reconciled = all(within_scope_checks.values())
    exclusions_proven = all(
        row.get('independently_proven_nonmessage') is True for row in exclusions)
    complete = within_scope_reconciled and outside_verified and exclusions_proven
    return {'schema': 'alpha.runtime-proto-message-domain-audit/v1',
            'scope': 'all current-runtime types by inheritance and independently derived serializer ABI',
            'inventory_type_count': runtime.type_count, 'descendant_count': len(descendants),
            'selected_count': len(selected), 'emitted_count': len(emitted),
            'descendant_type_indexes_owner_only': sorted(descendants),
            'unexplained_type_indexes_owner_only': unexplained,
            'unexplained_type_metadata_owner_only': unresolved_metadata,
            'exclusions_owner_only': exclusions, 'ancestry_errors_owner_only': ancestry_errors,
            'writer_descriptor_owner_only': writer_descriptor,
            'direct_serializer_owners_owner_only': direct_serializer_owners,
            'in_domain_serializer_owners_owner_only': in_domain_serializer_owners,
            'message_contract_descriptors_owner_only': sorted(contract_descriptors),
            'message_contract_implementors_owner_only': sorted(contract_implementors),
            'outside_base_serializer_candidates_owner_only': outside_serializer_candidates,
            'outside_base_serializer_exclusions_owner_only': outside_serializer_exclusions,
            'parent_resolution_evidence_owner_only': [
                {'descriptor': descriptor, 'definition_type_index': root, 'source': source}
                for descriptor, (root, source) in sorted(parent_resolutions.items())],
            'checks': checks, 'within_scope_reconciled': within_scope_reconciled,
            'outside_base_domain_independently_verified': outside_verified,
            'all_exclusions_independently_proven': exclusions_proven,
            'complete': complete}


from alpha.h01 import AcquisitionError

ENCODINGS = {1: "int32", 2: "sint32", 3: "int64", 4: "sint64",
             5: "sfixed32", 6: "sfixed64"}

SIGNED_CHECKS = r'''
static int signed_scalar(const unsigned char*d,SIZE_T n,uint32_t wanted,uint32_t wanted_wire,uint64_t*out){
    SIZE_T p=0;unsigned found=0;
    while(p<n){
        uint64_t tag=0,v=0;SIZE_T used=0;
        if(!varint(d+p,n-p,&tag,&used)||!(tag>>3u)||(tag>>3u)>0x1fffffffu)return 0;
        p+=used;uint32_t wire=(uint32_t)(tag&7u);
        if(wire==0){if(!varint(d+p,n-p,&v,&used))return 0;p+=used;}
        else if(wire==1||wire==5){SIZE_T width=wire==1?8u:4u;if(n-p<width)return 0;memcpy(&v,d+p,width);p+=width;}
        else if(wire==2){if(!varint(d+p,n-p,&v,&used)||v>n-p-used)return 0;p+=used+(SIZE_T)v;}
        else return 0;
        if((tag>>3u)==wanted){if(wire!=wanted_wire||++found!=1u)return 0;*out=v;}
    }
    return found==1u;
}
static uint32_t signed_encoding_code(uint32_t type,uint32_t wire,uint64_t positive,uint64_t negative){
    if(type!=8u&&type!=10u)return 0;
    if(wire==0u){
        if(positive==123u&&negative==UINT64_MAX-122u)return type==8u?1u:3u;
        if(positive==246u&&negative==245u)return type==8u?2u:4u;
    }
    if(type==8u&&wire==5u&&positive==123u&&negative==UINT32_MAX-122u)return 5u;
    if(type==10u&&wire==1u&&positive==123u&&negative==UINT64_MAX-122u)return 6u;
    return 0;
}
'''


def enrich_serializer_source(source):

    def replace(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("signed serializer source contract changed")
        source = source.replace(old, new)

    replace('static int put_value(', 'static int signed_probe_negative;\nstatic int put_value(')
    replace('unsigned char b=data[i];v|=',
            'unsigned char b=data[i];if(i==9u&&b>1u)return 0;v|=')
    replace('uint64_t value=123u;',
            'uint64_t value=(signed_probe_negative&&(r->type_enum==8u||r->type_enum==10u))?UINT64_MAX-122u:123u;')
    replace('static int collect(void)', SIGNED_CHECKS + '\nstatic int collect(void)')
    replace('uint32_t i=capture_cursor;', 'signed_probe_negative=0;uint32_t i=capture_cursor;')
    replace('out->serialized_bytes=length;', '''out->serialized_bytes=length;
        if(r->type_enum==8u||r->type_enum==10u){
            uint64_t positive=0,negative=0,negative_length=0;uintptr_t negative_array=0;
            int valid=signed_scalar(after,(SIZE_T)length,number,wire,&positive);
            signed_probe_negative=1;
            if(!valid||!put_value(message,r)||!serialize_message(message,r,&negative_array,&negative_length)
                ||!negative_length||!signed_scalar((const unsigned char*)(negative_array+0x20u),(SIZE_T)negative_length,number,wire,&negative))kind=9u;
            else {out->signed_positive=positive;out->signed_negative=negative;out->reserved=signed_encoding_code(r->type_enum,wire,positive,negative);if(!out->reserved)kind=9u;}
            signed_probe_negative=0;
            if(kind){out->number=0;out->wire=0;out->serialized_bytes=0;out->reserved=0;out->change_count=0;memset(out->changed_tags,0,sizeof(out->changed_tags));}
        }''')
    replace('memcpy(h.magic,"ALPHAPS1",8);h.version=1;',
            'memcpy(h.magic,"ALPHAPS4",8);h.version=4;')
    return source


def encoding_from_code(code, type_enum, wire):
    if not code:
        if type_enum in (8, 10):
            raise AcquisitionError("signed scalar has no encoding evidence")
        return None
    expected = {1: (8, 0), 2: (8, 0), 3: (10, 0), 4: (10, 0),
                5: (8, 5), 6: (10, 1)}
    if expected.get(code) != (type_enum, wire):
        raise AcquisitionError("signed scalar encoding evidence conflicts with storage/wire")
    return ENCODINGS[code]


def encoding_from_values(type_enum, wire, positive, negative):

    if type_enum not in (8, 10):
        if positive or negative:
            raise AcquisitionError("unexpected signed evidence on a nonsigned scalar")
        return None
    if wire == 0 and (positive, negative) == (123, (1 << 64) - 123):
        return "int32" if type_enum == 8 else "int64"
    if wire == 0 and (positive, negative) == (246, 245):
        return "sint32" if type_enum == 8 else "sint64"
    if (type_enum, wire, positive, negative) == (8, 5, 123, (1 << 32) - 123):
        return "sfixed32"
    if (type_enum, wire, positive, negative) == (10, 1, 123, (1 << 64) - 123):
        return "sfixed64"
    raise AcquisitionError("signed wire observations do not match a standard encoding")


def encoding_coverage(messages):

    rows = []
    signed = set(ENCODINGS.values())
    for message in messages:
        entries = [(field, "field") for field in message["fields"]]
        entries += [(case, "oneof:" + oneof["name"])
                    for oneof in message["oneofs"] for case in oneof["cases"]]
        for field, container in entries:
            for role in ("type", "key_type", "value_type"):
                if field.get(role) not in signed:
                    continue
                evidence = field.get("signed_encoding_evidence")
                verified = (container == "field" and role == "type"
                            and field.get("cardinality") == "singular"
                            and evidence == "write-to-positive-negative-123/v1")
                observation = field.get('signed_encoding_observation')
                if verified:
                    if not isinstance(observation, dict):
                        verified = False
                    else:
                        verified = encoding_from_values(observation.get('runtime_type_enum'),
                            observation.get('wire'), observation.get('positive'),
                            observation.get('negative')) == field[role]
                role_evidence = field.get('signed_role_evidence', {}).get(role)
                if role_evidence is not None:
                    from alpha.p01 import verify_role, SIGNED
                    identity = {'type_index_owner_only':message['type_index_owner_only'],
                        'number':field['number'], 'container':container, 'role':role,
                        'cardinality':field.get('cardinality','singular'), 'width':SIGNED[field[role]]}
                    if role_evidence.get('identity') != identity:
                        raise AcquisitionError('signed role evidence identity differs from output field')
                    checked = verify_role(identity, role_evidence['samples'])
                    if checked != role_evidence or checked['encoding'] != field[role]:
                        raise AcquisitionError('signed role evidence no longer matches output')
                    if checked['packed'] is not None and field.get('packed') != checked['packed']:
                        raise AcquisitionError('signed role packing differs from output')
                    verified = True
                parse_evidence = field.get('signed_parse_evidence', {}).get(role)
                if parse_evidence is not None:
                    from alpha.p43 import verify_parse_evidence
                    from alpha.p01 import SIGNED
                    checked = verify_parse_evidence(parse_evidence)
                    identity = {'type_index_owner_only':message['type_index_owner_only'],
                        'number':field['number'], 'container':container, 'role':role,
                        'cardinality':field.get('cardinality','singular'), 'width':SIGNED[field[role]]}
                    if checked.get('identity') != identity or checked.get('encoding') != field[role]:
                        raise AcquisitionError('signed parse evidence differs from output field')
                    if (identity['cardinality'] == 'repeated'
                            and checked.get('context', {}).get('packed') is not field.get('packed')):
                        raise AcquisitionError('signed parse packing differs from output field')
                    verified = True
                rows.append({"type_index_owner_only": message["type_index_owner_only"],
                             "number": field["number"], "container": container,
                             "cardinality": field.get("cardinality", "singular"),
                             "role": role, "type": field[role], "verified": verified})
    return {"schema": "alpha.runtime-proto-signed-encoding-coverage/v1",
            "required_count": len(rows), "verified_count": sum(r["verified"] for r in rows),
            "complete": all(r["verified"] for r in rows), "roles_owner_only": rows,
            "scope": "two distinguishing vectors under standard protobuf scalar encodings"}


import copy
import hashlib
from alpha.h01 import AcquisitionError

SCHEMA = 'alpha.runtime-proto-signed-role-evidence/v1'
SIGNED = {'int32':32, 'sint32':32, 'sfixed32':32,
          'int64':64, 'sint64':64, 'sfixed64':64}


def _varint(data, start):
    value = 0
    for index in range(10):
        if start + index >= len(data):
            raise AcquisitionError('truncated signed-role varint')
        byte = data[start + index]
        if index == 9 and byte > 1:
            raise AcquisitionError('overflowing signed-role varint')
        value |= (byte & 127) << (index * 7)
        if byte < 128:
            return value, start + index + 1
    raise AcquisitionError('unterminated signed-role varint')


def _fields(data):
    if not isinstance(data, bytes) or len(data) > 1048576:
        raise AcquisitionError('signed-role serialized message exceeds contract')
    cursor = 0
    rows = []
    while cursor < len(data):
        tag, cursor = _varint(data, cursor)
        number, wire = tag >> 3, tag & 7
        if not 0 < number <= 0x1fffffff:
            raise AcquisitionError('invalid signed-role field number')
        start = cursor
        if wire == 0:
            _, cursor = _varint(data, cursor)
        elif wire in (1,5):
            cursor += 8 if wire == 1 else 4
        elif wire == 2:
            size, cursor = _varint(data, cursor)
            start = cursor
            cursor += size
        else:
            raise AcquisitionError('unsupported signed-role wire type')
        if cursor > len(data):
            raise AcquisitionError('truncated signed-role field')
        rows.append((number, wire, data[start:cursor]))
    return rows


def _encode_varint(value):
    out = bytearray()
    while value >= 128:
        out.append((value & 127) | 128)
        value >>= 7
    out.append(value)
    return bytes(out)


def _encoded(value, name):
    width = SIGNED[name]
    if type(value) is not int or not -(1 << (width-1)) <= value < (1 << (width-1)):
        raise AcquisitionError('signed probe value outside CLR width')
    if name.startswith('sfixed'):
        return (5 if width == 32 else 1), value.to_bytes(width//8, 'little', signed=True)
    unsigned = ((value << 1) ^ (value >> (width-1))) if name.startswith('sint') else value & ((1 << 64)-1)
    return 0, _encode_varint(unsigned)


def _scalar_tokens(payload, wire):
    tokens = []
    cursor = 0
    while cursor < len(payload):
        start = cursor
        if wire == 0:
            _, cursor = _varint(payload, cursor)
        else:
            cursor += 4 if wire == 5 else 8
        if cursor > len(payload):
            raise AcquisitionError('partial packed fixed-width scalar')
        tokens.append(payload[start:cursor])
    return tokens


def role_inventory(messages):
    rows = []
    seen = set()
    for message in messages:
        fields = [(field,'field',field.get('cardinality','singular')) for field in message['fields']]
        fields += [(field,'oneof:'+oneof['name'],'singular')
                   for oneof in message['oneofs'] for field in oneof['cases']]
        for field, container, cardinality in fields:
            for role in ('type','key_type','value_type'):
                if field.get(role) not in SIGNED:
                    continue
                key = (message['type_index_owner_only'],field['number'],container,role)
                if key in seen:
                    raise AcquisitionError('duplicate signed-role identity')
                seen.add(key)
                rows.append({'type_index_owner_only':key[0], 'number':key[1], 'container':container,
                             'role':role, 'cardinality':cardinality, 'width':SIGNED[field[role]]})
    return rows


def verify_role(identity, samples):

    width = identity['width']
    if width not in (32,64) or identity['cardinality'] not in ('singular','repeated','map'):
        raise AcquisitionError('invalid signed-role identity')
    values = [v for sample in samples for v in sample['values']]
    if not any(type(v) is int and v > 0 for v in values) or not any(type(v) is int and v < 0 for v in values):
        raise AcquisitionError('signed-role evidence requires both positive and negative inputs')
    candidates = []
    for name in ('int'+str(width),'sint'+str(width),'sfixed'+str(width)):
        packing = set()
        matched = True
        for sample in samples:
            try:
                raw = bytes.fromhex(sample['serialized_hex'])
            except (TypeError,ValueError):
                raise AcquisitionError('invalid signed-role serialized hex') from None
            fields = [row for row in _fields(raw) if row[0] == identity['number']]
            expected = [_encoded(value,name) for value in sample['values']]
            if not expected:
                raise AcquisitionError('empty signed-role probe inputs')
            scalar_wire = expected[0][0]
            tokens = []
            try:
                if identity['cardinality'] == 'map':
                    if identity['role'] not in ('key_type','value_type'):
                        raise AcquisitionError('invalid signed map role')
                    member = 1 if identity['role']=='key_type' else 2
                    for _, wire, payload in fields:
                        if wire != 2:
                            matched=False;break
                        entry = _fields(payload)
                        part = [row for row in entry if row[0]==member]
                        if (len(part)>1 or (part and part[0][1]!=scalar_wire)
                                or any(row[0] not in (1,2) for row in entry)
                                or len({row[0] for row in entry})!=len(entry)):
                            matched=False;break
                        tokens.append(part[0][2] if part else _encoded(0,name)[1])
                elif identity['cardinality'] == 'repeated':
                    for _, wire, payload in fields:
                        if wire==2:
                            tokens.extend(_scalar_tokens(payload,scalar_wire));packing.add(True)
                        elif wire==scalar_wire:
                            tokens.append(payload);packing.add(False)
                        else:
                            matched=False;break
                else:
                    if (not fields and identity['container']=='field'
                            and sample['values']==[0] and identity['role']=='type'):
                        tokens=[expected[0][1]]
                        continue
                    if identity['role']!='type' or len(fields)!=1 or len(expected)!=1 or fields[0][1]!=scalar_wire:
                        matched=False;break
                    tokens=[fields[0][2]]
            except AcquisitionError:
                matched=False;break
            expected_tokens=[part[1] for part in expected]

            if identity['cardinality']=='map':
                tokens=sorted(tokens);expected_tokens=sorted(expected_tokens)
            if tokens!=expected_tokens or not matched:
                matched=False;break
        if matched and len(packing)<=1:
            candidates.append((name,next(iter(packing)) if packing else None))
    if len(candidates)!=1:
        raise AcquisitionError('signed-role encoding is absent, inconsistent, or ambiguous')
    name, packed = candidates[0]
    return {'schema':SCHEMA, 'identity':dict(identity), 'encoding':name, 'packed':packed,
            'samples':copy.deepcopy(samples),
            'sample_sha256':[hashlib.sha256(bytes.fromhex(s['serialized_hex'])).hexdigest() for s in samples]}


def apply_role_evidence(model, evidence):

    if evidence.get('target') != model.get('target'):
        raise AcquisitionError('signed-role evidence belongs to another capture')
    if not isinstance(evidence.get('observations'), list):
        raise AcquisitionError('signed-role capture observations are absent')
    result=copy.deepcopy(model)
    domain={tuple(row[k] for k in ('type_index_owner_only','number','container','role')):row
            for row in role_inventory(result['messages_owner_only'])}
    seen=set()
    for row in evidence['observations']:
        identity=row['identity'];key=tuple(identity[k] for k in ('type_index_owner_only','number','container','role'))
        if key not in domain or domain[key]!=identity or key in seen:
            raise AcquisitionError('signed-role observation outside unique current domain')
        seen.add(key)
        verified=verify_role(identity,row['samples'])
        message=next(m for m in result['messages_owner_only'] if m['type_index_owner_only']==key[0])
        fields=(message['fields'] if key[2]=='field' else
                next(o['cases'] for o in message['oneofs'] if 'oneof:'+o['name']==key[2]))
        field=next(f for f in fields if f['number']==key[1])
        previous=field.get('signed_role_evidence',{}).get(key[3])
        if previous is not None:
            checked=verify_role(identity,previous['samples'])
            if checked['encoding']!=verified['encoding'] or checked['packed']!=verified['packed']:
                raise AcquisitionError('independent signed-role observations conflict')
        scalar=field.get('signed_encoding_observation') if key[3]=='type' else None
        if scalar is not None:
            from alpha.p01 import encoding_from_values
            if encoding_from_values(scalar['runtime_type_enum'],scalar['wire'],scalar['positive'],scalar['negative'])!=verified['encoding']:
                raise AcquisitionError('signed-role observation conflicts with scalar probe')
        field[key[3]]=verified['encoding']
        if verified['packed'] is not None:
            field['packed']=verified['packed']
        field.setdefault('signed_role_evidence',{})[key[3]]=verified
    from alpha.p01 import encoding_coverage
    coverage = encoding_coverage(result['messages_owner_only'])
    result['signed_encoding_coverage_owner_only']=coverage
    result['signed_role_observation_counts']={'required':len(domain),'verified':coverage['verified_count'],
                                             'pending':len(domain)-coverage['verified_count']}
    result.setdefault('signed_role_captures_owner_only', []).append(copy.deepcopy(evidence))
    return result


def write_verified_role_model(*, static_model, observation_model, output_path):

    from alpha.h02 import read_json, file_identity
    from alpha.p12 import _private_json
    source_identity=file_identity(static_model)
    observation_identity=file_identity(observation_model)
    model=read_json(static_model);evidence=read_json(observation_model)
    if evidence.get('schema')!='alpha.runtime-proto-signed-role-capture/v1':
        raise AcquisitionError('signed-role capture schema mismatch')
    result=apply_role_evidence(model,evidence)
    if file_identity(static_model)!=source_identity or file_identity(observation_model)!=observation_identity:
        raise AcquisitionError('signed-role inputs changed during verification')
    if output_path.exists() or output_path.is_symlink():
        raise AcquisitionError('signed-role output already exists')
    result.setdefault('inputs', {})['signed_role_observation_model']=observation_identity
    result['inputs']['signed_role_source_model']=source_identity
    domain = result.get('message_domain_audit_owner_only', {})
    result['full_semantic_verification_complete'] = (
        result['signed_encoding_coverage_owner_only'].get('complete') is True
        and domain.get('complete') is True
    )
    _private_json(output_path,result)
    return result


from dataclasses import dataclass, field
from typing import Any

from alpha.h01 import ContractViolation
from alpha.h02 import generation_id


EVIDENCE_KINDS = frozenset(
    {
        "client",
        "package_runtime",
        "proto",
        "rsa",
        "region_dispatch",
        "bootstrap_key",
        "resource_cache_identity",
        "redirect_profile",
    }
)


@dataclass(frozen=True)
class TargetIdentity:
    client_version: str
    client_build: str
    executable_path: str
    executable_sha256: str
    executable_bytes: int

    def public(self) -> dict[str, Any]:
        return {
            "client_version": self.client_version,
            "client_build": self.client_build,
            "executable_path": self.executable_path,
            "executable_sha256": self.executable_sha256,
            "executable_bytes": self.executable_bytes,
        }


@dataclass(frozen=True)
class Evidence:
    kind: str
    target_version: str
    target_executable_sha256: str
    source: dict[str, Any]
    facts: dict[str, Any]
    references: dict[str, str] = field(default_factory=dict)
    provider: str = "builtin"
    provider_version: str = "1"
    id: str = ""

    def __post_init__(self) -> None:
        if self.kind not in EVIDENCE_KINDS:
            raise ContractViolation(f"unsupported evidence kind: {self.kind}")
        material = self.content_material()
        computed = generation_id(self.kind, material)
        if self.id and self.id != computed:
            raise ContractViolation(f"evidence generation id mismatch: {self.kind}")
        object.__setattr__(self, "id", computed)

    def content_material(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "target_version": self.target_version,
            "target_executable_sha256": self.target_executable_sha256,
            "source": self.source,
            "facts": self.facts,
            "references": self.references,
            "provider": self.provider,
            "provider_version": self.provider_version,
        }

    def public(self) -> dict[str, Any]:
        return {
            "schema": "alpha.evidence/v1",
            "generation_id": self.id,
            **self.content_material(),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "Evidence":
        if payload.get("schema") != "alpha.evidence/v1":
            raise ContractViolation("unsupported evidence schema")
        return cls(
            kind=str(payload.get("kind") or ""),
            target_version=str(payload.get("target_version") or ""),
            target_executable_sha256=str(
                payload.get("target_executable_sha256") or ""
            ).lower(),
            source=dict(payload.get("source") or {}),
            facts=dict(payload.get("facts") or {}),
            references=dict(payload.get("references") or {}),
            provider=str(payload.get("provider") or ""),
            provider_version=str(payload.get("provider_version") or ""),
            id=str(payload.get("generation_id") or ""),
        )


from dataclasses import asdict, dataclass
from typing import Any

from alpha.h01 import ContractViolation
from alpha.h02 import generation_id


REFLECTION_SCHEMA = "alpha.runtime-reflection-contract/v1"


@dataclass(frozen=True)
class ReflectionOperation:
    key: str
    owner: str
    member: str
    runtime_owner: str
    runtime_name: str
    kind: str
    parameter_count: int
    semantic_role: str


OPERATIONS = (
    ReflectionOperation("event.name", "System.Reflection.EventInfo", "Name", "System.Reflection.MonoEvent", "get_Name", "property-get", 0, "event-name"),
    ReflectionOperation("event.remove_method", "System.Reflection.EventInfo", "GetRemoveMethod", "System.Reflection.MonoEvent", "GetRemoveMethod", "method", 1, "event-accessor"),
    ReflectionOperation("event.raise_method", "System.Reflection.EventInfo", "GetRaiseMethod", "System.Reflection.MonoEvent", "GetRaiseMethod", "method", 1, "event-accessor"),
    ReflectionOperation("event.add_method", "System.Reflection.EventInfo", "GetAddMethod", "System.Reflection.MonoEvent", "GetAddMethod", "method", 1, "event-accessor"),
    ReflectionOperation("event.handler_type", "System.Reflection.EventInfo", "EventHandlerType", "System.Reflection.EventInfo", "get_EventHandlerType", "property-get", 0, "event-type"),
    ReflectionOperation("property.setter", "System.Reflection.PropertyInfo", "GetSetMethod", "System.Reflection.MonoProperty", "GetSetMethod", "method", 1, "property-accessor"),
    ReflectionOperation("property.getter", "System.Reflection.PropertyInfo", "GetGetMethod", "System.Reflection.MonoProperty", "GetGetMethod", "method", 1, "property-accessor"),
    ReflectionOperation("property.name", "System.Reflection.PropertyInfo", "Name", "System.Reflection.MonoProperty", "get_Name", "property-get", 0, "property-name"),
    ReflectionOperation("property.from_handle", "System.Reflection.PropertyInfo", "GetPropertyFromHandle", "System.Reflection.PropertyInfo", "GetPropertyFromHandle", "method", 1, "resolve-property"),
    ReflectionOperation("field.set_value", "System.Reflection.FieldInfo", "SetValue", "System.Reflection.MonoField", "SetValue", "method", 2, "field-value-write"),
    ReflectionOperation("field.get_value", "System.Reflection.FieldInfo", "GetValue", "System.Reflection.MonoField", "GetValue", "method", 1, "field-value-read"),
    ReflectionOperation("field.name", "System.Reflection.FieldInfo", "Name", "System.Reflection.MonoField", "get_Name", "property-get", 0, "field-name"),
    ReflectionOperation("field.raw_constant", "System.Reflection.FieldInfo", "GetRawConstantValue", "System.Reflection.MonoField", "GetRawConstantValue", "method", 0, "field-constant"),
    ReflectionOperation("field.attributes", "System.Reflection.FieldInfo", "Attributes", "System.Reflection.MonoField", "get_Attributes", "property-get", 0, "field-flags"),
    ReflectionOperation("field.type", "System.Reflection.FieldInfo", "FieldType", "System.Reflection.MonoField", "get_FieldType", "property-get", 0, "field-type"),
    ReflectionOperation("field.from_handle", "System.Reflection.FieldInfo", "GetFieldFromHandle", "System.Reflection.FieldInfo", "internal_from_handle_type", "method", 2, "resolve-field"),
    ReflectionOperation("parameter.default_value", "System.Reflection.ParameterInfo", "DefaultValue", "System.Reflection.MonoParameterInfo", "get_DefaultValue", "property-get", 0, "default-value"),
    ReflectionOperation("parameter.is_out", "System.Reflection.ParameterInfo", "IsOut", "System.Reflection.ParameterInfo", "get_IsOut", "property-get", 0, "parameter-flags"),
    ReflectionOperation("parameter.is_optional", "System.Reflection.ParameterInfo", "IsOptional", "System.Reflection.ParameterInfo", "get_IsOptional", "property-get", 0, "parameter-flags"),
    ReflectionOperation("parameter.is_in", "System.Reflection.ParameterInfo", "IsIn", "System.Reflection.ParameterInfo", "get_IsIn", "property-get", 0, "parameter-flags"),
    ReflectionOperation("parameter.name", "System.Reflection.ParameterInfo", "Name", "System.Reflection.ParameterInfo", "get_Name", "property-get", 0, "parameter-name"),
    ReflectionOperation("parameter.type", "System.Reflection.ParameterInfo", "ParameterType", "System.Reflection.ParameterInfo", "get_ParameterType", "property-get", 0, "parameter-type"),
    ReflectionOperation("method.name", "System.Reflection.MethodInfo", "Name", "System.Reflection.MonoMethod", "get_Name", "property-get", 0, "method-name"),
    ReflectionOperation("method.parameters", "System.Reflection.MethodBase", "GetParameters", "System.Reflection.MonoMethod", "GetParameters", "method", 0, "parameters"),
    ReflectionOperation("method.return_type", "System.Reflection.MethodInfo", "ReturnType", "System.Reflection.MonoMethod", "get_ReturnType", "property-get", 0, "return-type"),
    ReflectionOperation("method.attributes", "System.Reflection.MethodBase", "Attributes", "System.Reflection.MonoMethod", "get_Attributes", "property-get", 0, "method-flags"),
    ReflectionOperation("method.from_handle", "System.Reflection.MethodBase", "GetMethodFromHandle", "System.Reflection.MethodBase", "GetMethodFromHandleInternalType_native", "method", 2, "resolve-method"),
    ReflectionOperation("member.metadata_token", "System.Reflection.MemberInfo", "MetadataToken", "System.Reflection.MemberInfo", "get_MetadataToken", "property-get", 0, "metadata-identity"),
    ReflectionOperation("enum.underlying_type", "System.Enum", "GetUnderlyingType", "System.Enum", "GetUnderlyingType", "method", 1, "enum-underlying-type"),
    ReflectionOperation("type.module", "System.Type", "Module", "System.RuntimeType", "get_Module", "property-get", 0, "module"),
    ReflectionOperation("type.interfaces", "System.Type", "GetInterfaces", "System.RuntimeType", "GetInterfaces", "method", 0, "interfaces"),
    ReflectionOperation("type.is_enum", "System.Type", "IsEnum", "System.RuntimeType", "get_IsEnum", "property-get", 0, "enum-shape"),
    ReflectionOperation("type.is_value_type", "System.Type", "IsValueType", "System.RuntimeType", "IsValueTypeImpl", "method", 0, "value-shape"),
    ReflectionOperation("type.is_generic", "System.Type", "IsGenericType", "System.RuntimeType", "get_IsGenericType", "property-get", 0, "generic-shape"),
    ReflectionOperation("type.generic_definition", "System.Type", "GetGenericTypeDefinition", "System.RuntimeType", "GetGenericTypeDefinition", "method", 0, "generic-definition"),
    ReflectionOperation("type.is_generic_definition", "System.Type", "IsGenericTypeDefinition", "System.RuntimeType", "get_IsGenericTypeDefinition", "property-get", 0, "generic-shape"),
    ReflectionOperation("type.generic_arguments", "System.Type", "GetGenericArguments", "System.RuntimeType", "GetGenericArguments", "method", 0, "generic-arguments"),
    ReflectionOperation("type.element_type", "System.Type", "GetElementType", "System.RuntimeType", "GetElementType", "method", 0, "element-type"),
    ReflectionOperation("type.base_type", "System.Type", "BaseType", "System.RuntimeType", "get_BaseType", "property-get", 0, "inheritance"),
    ReflectionOperation("type.handle", "System.Type", "TypeHandle", "System.RuntimeType", "get_TypeHandle", "property-get", 0, "type-handle"),
    ReflectionOperation("type.declaring_type", "System.Type", "DeclaringType", "System.RuntimeType", "get_DeclaringType", "property-get", 0, "nesting"),
    ReflectionOperation("type.events", "System.Type", "GetEvents", "System.RuntimeType", "GetEvents", "method", 0, "events"),
    ReflectionOperation("type.namespace", "System.Type", "Namespace", "System.RuntimeType", "get_Namespace", "property-get", 0, "namespace"),
    ReflectionOperation("type.name", "System.Type", "Name", "System.RuntimeType", "get_Name", "property-get", 0, "type-name"),
    ReflectionOperation("type.is_byref", "System.Type", "IsByRef", "System.Type", "get_IsByRef", "property-get", 0, "byref-shape"),
    ReflectionOperation("type.attributes", "System.Type", "Attributes", "System.Type", "get_Attributes", "property-get", 0, "type-flags"),
    ReflectionOperation("type.from_handle", "System.Type", "GetTypeFromHandle", "System.Type", "GetTypeFromHandle", "method", 1, "resolve-type"),
)


def reflection_contract() -> dict[str, Any]:
    operations = [asdict(operation) for operation in OPERATIONS]
    payload: dict[str, Any] = {
        "schema": REFLECTION_SCHEMA,
        "operation_count": len(operations),
        "operations": operations,
        "resolution_policy": {
            "exact_current_target_required": True,
            "fresh_runtime_required": True,
            "semantic_identity_required": True,
            "all_operations_required": True,
            "native_address_in_contract": False,
            "native_offset_in_contract": False,
            "saved_dispatch_value_in_contract": False,
            "external_component_required": False,
        },
    }
    payload["contract_id"] = generation_id("runtime-reflection-contract", payload)
    validate_reflection_contract(payload)
    return payload


def validate_reflection_contract(payload: dict[str, Any]) -> None:
    if payload.get("schema") != REFLECTION_SCHEMA:
        raise ContractViolation("runtime reflection contract schema is invalid")
    operations = payload.get("operations")
    if not isinstance(operations, list) or len(operations) != 47:
        raise ContractViolation("runtime reflection contract must contain all operations")
    keys = [operation.get("key") for operation in operations if isinstance(operation, dict)]
    if len(keys) != len(operations) or len(set(keys)) != len(keys):
        raise ContractViolation("runtime reflection operation identities are not unique")
    for operation in operations:
        if (
            not isinstance(operation.get("owner"), str)
            or not operation["owner"].startswith("System.")
            or not isinstance(operation.get("member"), str)
            or not operation["member"]
            or not isinstance(operation.get("runtime_name"), str)
            or not operation["runtime_name"]
            or not isinstance(operation.get("runtime_owner"), str)
            or not operation["runtime_owner"].startswith("System.")
            or operation.get("kind") not in {"method", "property-get"}
            or not isinstance(operation.get("parameter_count"), int)
            or operation["parameter_count"] < 0
        ):
            raise ContractViolation("runtime reflection operation shape is invalid")
    policy = payload.get("resolution_policy")
    if not isinstance(policy, dict) or not all(
        policy.get(key) is expected
        for key, expected in {
            "exact_current_target_required": True,
            "fresh_runtime_required": True,
            "semantic_identity_required": True,
            "all_operations_required": True,
            "native_address_in_contract": False,
            "native_offset_in_contract": False,
            "saved_dispatch_value_in_contract": False,
            "external_component_required": False,
        }.items()
    ):
        raise ContractViolation("runtime reflection resolution policy is unsafe")


import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

from alpha.h01 import AcquisitionError, launch_lock
from alpha.h01 import completion_root, dump_root
from alpha.h02 import publish_new_directory, write_new_json


DEFAULT_DUMP_ROOT = dump_root()
DEFAULT_COMPLETION_ROOT = completion_root()


def assign_default_locations(args):

    if args.work_dir is not None and args.output_dir is not None:
        return
    prefix = "metadata" if getattr(args, "metadata_only", False) else "proto"
    generation = (
        time.strftime("proto-%Y%m%d-%H%M%S")
        + f"-{time.time_ns() % 1_000_000_000:09d}"
    )
    generation = generation.replace("proto-", prefix + "-", 1)
    if args.work_dir is None:
        args.work_dir = DEFAULT_DUMP_ROOT / generation
    if args.output_dir is None:
        args.output_dir = DEFAULT_COMPLETION_ROOT / generation


def manifest(root):
    return {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(root.rglob("*.py")) if not path.name.startswith("._")}


def prepare_implementation(
    work_dir, *, resume=False, repair_resume=False, source=None,
):
    work_dir = work_dir.expanduser().absolute()
    destination = work_dir.with_name(work_dir.name + ".implementation")
    if source is None:
        source = Path(__file__).parent
    else:
        source = Path(source).expanduser().absolute()
    if destination.is_symlink():
        raise AcquisitionError("proto implementation directory is a symlink")
    superseded = None
    superseded_manifest = None
    if destination.exists():
        if not resume:
            raise AcquisitionError("proto implementation already exists; choose a new work directory")
        recorded = json.loads((destination / "manifest.json").read_text())
        observed = manifest(destination / "alpha")
        if not recorded or observed != recorded:
            raise AcquisitionError("proto implementation snapshot changed")
        current = manifest(source)
        if current == recorded:
            return destination
        if not repair_resume:
            raise AcquisitionError(
                "proto implementation snapshot differs from the current source"
            )


        superseded = destination.with_name(
            destination.name + ".superseded-" + str(time.time_ns())
        )
        os.replace(destination, superseded)
        superseded_manifest = recorded
    elif resume:
        raise AcquisitionError("proto resume implementation snapshot is missing")
    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".proto-implementation-", dir=destination.parent))
    before = manifest(source)
    shutil.copytree(source, staging / "alpha", ignore=shutil.ignore_patterns("__pycache__", "._*"))
    if not before or manifest(source) != before or manifest(staging / "alpha") != before:
        raise AcquisitionError("proto implementation changed while snapshotting")
    write_new_json(staging / "manifest.json", before)
    for path in staging.rglob("*"):
        path.chmod(0o700 if path.is_dir() else 0o600)
    publish_new_directory(staging, destination)
    if superseded is not None:
        record = {
            "schema": "alpha.proto-implementation-supersession/v1",
            "superseded_snapshot": str(superseded),
            "superseded_manifest": superseded_manifest,
            "replacement_manifest": before,
            "recorded_ns": time.time_ns(),
        }
        write_new_json(destination / "superseded.json", record)
        (destination / "superseded.json").chmod(0o600)
    return destination


def run_proto_command(args):
    from alpha.p44 import preflight
    from alpha.h01 import find_clients, find_compiler, find_wine, find_wineprefix
    if getattr(args, "repair_resume", False) and not args.resume:
        raise AcquisitionError("repair resume requires --resume")
    if getattr(args, "carry_forward", False) and not (
        args.resume and getattr(args, "repair_resume", False)
    ):
        raise AcquisitionError("carry forward requires --resume --repair-resume")
    if getattr(args, "salvage_restart", False) and not (
        args.resume and getattr(args, "repair_resume", False)
    ):
        raise AcquisitionError("salvage restart requires --resume --repair-resume")
    if getattr(args, "binary", None) is None:
        clients = find_clients()
        process_name = getattr(args, "process_name", None)
        if process_name:
            wanted = Path(process_name).stem.casefold()
            clients = [path for path in clients if path.stem.casefold() == wanted]
        if len(clients) == 1:
            args.binary = clients[0]
        elif clients:
            raise AcquisitionError(
                "client executable is ambiguous; pass --binary: "
                + ", ".join(str(path) for path in clients[:5])
            )
        else:
            raise AcquisitionError(
                "client executable not found; pass --binary or set ALPHA_CLIENT"
            )
    if os.name == "nt":
        args.wine = Path(sys.executable).resolve()
        args.wineprefix = Path(tempfile.gettempdir()).resolve()
    else:
        if getattr(args, "wine", None) is None:
            args.wine = find_wine()
            if args.wine is None:
                raise AcquisitionError("wine not found; pass --wine or set ALPHA_WINE")
        if getattr(args, "wineprefix", None) is None:
            args.wineprefix = find_wineprefix()
            if args.wineprefix is None:
                raise AcquisitionError(
                    "wine prefix not found; pass --wineprefix or set ALPHA_WINEPREFIX"
                )
    if getattr(args, "compiler", None) is None:
        args.compiler = find_compiler()
    from alpha.p12 import verify_windows_toolchain

    args.compiler = verify_windows_toolchain(args.compiler)
    assign_default_locations(args)
    preflight(args.output_dir)
    if (args.work_dir.exists() or args.work_dir.is_symlink()) and not args.resume:
        raise AcquisitionError("proto work directory already exists")
    with launch_lock(args.work_dir):
        implementation = prepare_implementation(
            args.work_dir, resume=args.resume,
            repair_resume=getattr(args, "repair_resume", False),
        )
        command = [sys.executable, "-m", "alpha.runtime_proto_pipeline"]
        for name in ("binary", "work_dir", "output_dir", "wine", "wineprefix"):
            command.extend(("--" + name.replace("_", "-"), str(getattr(args, name).expanduser().absolute())))
        command.extend(("--timeout", str(args.timeout)))
        if args.compiler is not None:
            command.extend(("--compiler", str(args.compiler.expanduser().absolute())))
        if args.resume:
            command.append("--resume")
        if getattr(args, "repair_resume", False):
            command.append("--repair-resume")
        if getattr(args, "carry_forward", False):
            command.append("--carry-forward")
        if getattr(args, "rebind_live_process", False):
            command.append("--rebind-live-process")
        if getattr(args, "salvage_restart", False):
            command.append("--salvage-restart")
        if getattr(args, "partial_proto_without_field_encrypt", False):
            command.append("--partial-proto-without-field-encrypt")
        if getattr(args, "with_metadata", False):
            command.append("--with-metadata")
        metadata_output = getattr(args, "metadata_output_dir", None)
        if metadata_output is not None:
            command.extend(
                ("--metadata-output-dir", str(metadata_output.expanduser().absolute()))
            )
        if getattr(args, "skip_metadata_reconstruction", False):
            command.append("--skip-metadata-reconstruction")
        if getattr(args, "metadata_only", False):
            command.append("--metadata-only")
        if "reachable_heap_limit_mib" in getattr(args, "__dict__", {}):
            command.extend(
                ("--reachable-heap-limit-mib", str(args.reachable_heap_limit_mib))
            )
        for observation in getattr(args, "metadata_domain_observation", None) or []:
            command.extend(
                ("--metadata-domain-observation", str(observation.expanduser().absolute()))
            )
        environment = dict(os.environ, PYTHONPATH=str(implementation))
        if getattr(args, "pid", None) is not None:
            environment["ALPHA_TARGET_PID"] = str(args.pid)
        if getattr(args, "attach_latest", False) and getattr(args, "pid", None) is None:
            environment["ALPHA_ATTACH_LATEST"] = "1"
        if getattr(args, "rejected_candidates", None) is not None:
            environment["ALPHA_NAMEEPROTO_REJECTED_LEDGER"] = str(
                args.rejected_candidates.expanduser().absolute()
            )
        if getattr(args, "strict", False):
            environment["ALPHA_NAMEEPROTO_STRICT"] = "1"
        if getattr(args, "no_guess", False):
            environment["ALPHA_NAMEEPROTO_NO_GUESS"] = "1"
        if getattr(args, "exclude_unresolved", False):
            environment["ALPHA_NAMEEPROTO_INCLUDE_UNRESOLVED"] = "0"
        semantic_references = [
            path.expanduser().absolute()
            for path in (getattr(args, "semantic_reference", None) or [])
        ]
        if semantic_references:
            environment["ALPHA_NAMEEPROTO_SEMANTIC_REFERENCES"] = os.pathsep.join(
                str(path) for path in semantic_references
            )
        return subprocess.call(command, cwd=implementation, env=environment)
