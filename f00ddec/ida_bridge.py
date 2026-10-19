"""
IDA integration for f00ddec.  Runs inside IDA on a database opened with a MeP
processor module (the bundled ``mepf00d`` Python module, or IDA's native ``mep``).
Reads the flash bytes from the database, uses IDA's function boundaries as entry
points, and reuses IDA's names.  IDA is imported lazily.
"""

from . import decoder, cfg, opt, frame, callargs, recover, structure, cgen, db, abi, vars
from .names import Namer
from . import Program, Function, BANNER  # noqa: F401


class IdaNamer(Namer):
    def __init__(self):
        super().__init__()
        import ida_name
        self._n = ida_name

    def code(self, ea):
        if ea is None:
            return "?"
        return self._n.get_name(ea) or super().code(ea)

    def label(self, ea):
        return self._n.get_name(ea) or super().label(ea)

    def data(self, ea):
        return self._n.get_name(ea) or super().data(ea)


class SegmentedImage:
    """Sparse segment-backed memory image that avoids reading unmapped address gaps."""
    def __init__(self, segments):
        # segments: list of (start_ea, end_ea, bytearray) sorted by start_ea
        self.segments = sorted(segments, key=lambda s: s[0])
        self.base = self.segments[0][0] if self.segments else 0
        self._total = sum(len(b) for _, _, b in self.segments)

    def __len__(self):
        return self._total

    def contains(self, ea, size=1):
        for start, end, _ in self.segments:
            if start <= ea:
                if ea + size <= end:
                    return True
            else:
                break
        return False

    def get_u16(self, ea):
        for start, end, buf in self.segments:
            if start <= ea:
                if ea + 2 <= end:
                    off = ea - start
                    return buf[off] | (buf[off + 1] << 8)
            else:
                break
        return None

    def get_u32(self, ea):
        for start, end, buf in self.segments:
            if start <= ea:
                if ea + 4 <= end:
                    off = ea - start
                    return (buf[off] | (buf[off + 1] << 8)
                            | (buf[off + 2] << 16) | (buf[off + 3] << 24))
            else:
                break
        return None


_ARITY_CACHE = {}
_RET_CACHE = {}


def _image():
    import ida_bytes, ida_segment
    segments = []
    seg = ida_segment.get_first_seg()
    while seg is not None:
        start, end = seg.start_ea, seg.end_ea
        size = end - start
        if 0 < size <= 0x4000000 and ida_bytes.is_loaded(start):
            data = ida_bytes.get_bytes(start, size)
            if data:
                segments.append((start, end, bytearray(data)))
        seg = ida_segment.get_next_seg(start)
    if not segments:
        return None, 0
    img = SegmentedImage(segments)
    return img, img.base


def _entries():
    import idautils
    return sorted(idautils.Functions())


def _resolve_op_name(ea, n, op):
    """Resolve an instruction operand to a named symbol in IDA."""
    try:
        import idautils, ida_name, ida_idaapi
        # 1. Check data cross references from this instruction
        for x in idautils.XrefsFrom(ea):
            if not x.iscode:
                xname = ida_name.get_name(x.to)
                if xname and not xname.startswith(("unk_", "byte_", "word_", "dword_", "loc_", "sub_")):
                    return xname

        # 2. Check address directly if it's a valid mapped address pointing to a named symbol
        val = getattr(op, "value", None) or getattr(op, "addr", None)
        if val is not None and isinstance(val, int) and (val >= 0x800000 or val >= 0x1000):
            val_name = ida_name.get_name(val)
            if val_name and not val_name.startswith(("unk_", "byte_", "word_", "dword_", "loc_", "sub_")):
                return val_name
    except Exception:
        pass
    return None


def _annotate_operand_names(insns):
    """Annotate operands of instructions with resolved symbol names from IDA."""
    for ins in insns.values():
        for n, op in enumerate(ins.ops):
            if getattr(op, "mode", None) in ("imm", "near", "mem"):
                sym = _resolve_op_name(ins.ea, n, op)
                if sym:
                    op.name = sym


class _IdaFrameInfo:
    def __init__(self, members=None):
        self.members = members or {}


def _ida_frame_info(ea):
    """Read stack frame structure details from IDA Pro if available."""
    try:
        import ida_funcs, ida_frame, ida_typeinf
        pfn = ida_funcs.get_func(ea)
        if not pfn:
            return None
        tif = ida_typeinf.tinfo_t()
        members = {}
        if ida_frame.get_func_frame(tif, pfn):
            udt = ida_typeinf.udt_type_data_t()
            if tif.get_udt_details(udt):
                frsize = getattr(pfn, "frsize", 0)
                for m in udt:
                    actual_off = (m.offset // 8) - frsize
                    members[actual_off] = (m.name, m.size // 8, m.type.dstr())
        return _IdaFrameInfo(members=members)
    except Exception:
        return None


def _get_ida_func_proto(ea):
    """Retrieve function prototype from IDA type system if set."""
    try:
        import ida_typeinf, ida_name
        tif = ida_typeinf.tinfo_t()
        if ida_typeinf.get_tinfo(tif, ea):
            name = ida_name.get_name(ea) or ("sub_%X" % ea)
            return tif.dstr() + " " + name
    except Exception:
        pass
    return None


def _find_entry(image, base, ea, entset):
    """If *ea* is inside an un-functioned routine in IDA, locate its entry."""
    if ea in entset:
        return ea
    cur = ea & ~1
    limit = max(base, cur - 0x200)
    best = cur
    while cur > limit:
        prev2 = cur - 2
        prev4 = cur - 4
        # Check if previous instruction is an unconditional stop (ret/reti/bra/jmp)
        ins4 = decoder.decode_one(image, prev4, base) if decoder.in_bounds(image, prev4, base, 4) else None
        if ins4 is not None and ins4.size == 4 and ins4.mnem in ("bra", "jmp"):
            return cur
        ins2 = decoder.decode_one(image, prev2, base) if decoder.in_bounds(image, prev2, base, 2) else None
        if ins2 is not None and ins2.size == 2:
            if ins2.mnem in ("ret", "reti", "dret", "bra", "jmp"):
                return cur
            if ins2.mnem == "nop":
                ins_before = decoder.decode_one(image, prev2 - 2, base)
                if ins_before is not None and ins_before.size == 2 and ins_before.mnem in ("ret", "reti", "dret", "bra", "jmp"):
                    return cur
        if prev2 in entset:
            return prev2
        cur -= 2
    return best


def _callee_arity(image, base, callee_ea, entset):
    if callee_ea in _ARITY_CACHE:
        return _ARITY_CACHE[callee_ea]
    stop = entset - {callee_ea}
    c_insns, _ = decoder.decode(image, entries=[callee_ea], base=base, stop_at=stop)
    c_func = cfg.build_func(c_insns, callee_ea, entset)
    if c_func is None:
        return None
    frame_info = frame.analyze_frame(c_func)
    opt.optimize(c_func)
    sig = abi.analyze_calling_convention(c_func, frame_info=frame_info)
    n = len(sig.params)
    _ARITY_CACHE[callee_ea] = n
    _RET_CACHE[callee_ea] = sig.ret_type
    return n


def decompile_program():
    image, base = _image()
    if image is None:
        raise RuntimeError("f00ddec: no segments")
    entries = _entries() or [base]
    insns, calls = decoder.decode(image, entries=entries, base=base)
    _annotate_operand_names(insns)
    funcs = cfg.build_functions(insns, calls, extra_entries=entries)
    namer = IdaNamer()

    # Pre-populate arity cache
    for entry, f in funcs.items():
        frame_info = frame.analyze_frame(f)
        opt.optimize(f)
        sig = abi.analyze_calling_convention(f, frame_info=frame_info)
        _ARITY_CACHE[entry] = len(sig.params)
        _RET_CACHE[entry] = sig.ret_type

    out = {}
    for entry, f in funcs.items():
        db_data = db.get_func_data(entry)
        u_renames = db_data.get("renames", {})
        u_types = db_data.get("types", {})
        u_proto = db_data.get("proto") or _get_ida_func_proto(entry)

        ida_info = _ida_frame_info(entry)
        frame_info = frame.analyze_frame(f, ida_frame_info=ida_info)
        frame_info.user_renames = u_renames
        frame_info.user_types = u_types

        callargs.rewrite(f, _ARITY_CACHE)
        opt.optimize(f)
        sig = abi.analyze_calling_convention(f, frame_info=frame_info, user_proto=u_proto, ret_types=_RET_CACHE)
        vars.recover_variables(f, sig, frame_info)
        tree = structure.structure(f)
        lines = cgen.generate(f, tree, namer, frame_info=frame_info, sig=sig,
                              user_renames=u_renames, user_types=u_types)
        out[entry] = Function(entry, namer.code(entry), f, tree, lines)
    return Program(image, base, insns, out, namer)


def decompile_one(ea):
    import ida_funcs
    image, base = _image()
    if image is None:
        raise RuntimeError("f00ddec: no segments")
    entset = set(_entries())
    f = ida_funcs.get_func(ea)
    entry = f.start_ea if f is not None else _find_entry(image, base, ea, entset)
    entset.add(entry)
    stop = entset - {entry}
    insns, calls = decoder.decode(image, entries=[entry], base=base, stop_at=stop)
    _annotate_operand_names(insns)

    # Check if entry is a switch case fragment belonging to a parent function
    for ins in insns.values():
        if getattr(ins, "switch", None) is not None and entry in ins.switch.targets:
            parent_f = ida_funcs.get_func(ins.ea)
            if parent_f and parent_f.start_ea != entry:
                entry = parent_f.start_ea
                break

    all_entries = entset | calls
    func = cfg.build_func(insns, entry, all_entries)
    if func is None:
        raise RuntimeError("f00ddec: nothing decoded at 0x%X" % entry)
    namer = IdaNamer()

    db_data = db.get_func_data(entry)
    u_renames = db_data.get("renames", {})
    u_types = db_data.get("types", {})
    u_proto = db_data.get("proto") or _get_ida_func_proto(entry)

    ida_info = _ida_frame_info(entry)
    frame_info = frame.analyze_frame(func, ida_frame_info=ida_info)
    frame_info.user_renames = u_renames
    frame_info.user_types = u_types

    # Resolve direct callee arities
    arity = {}
    for callee in func.calls:
        ca = _callee_arity(image, base, callee, all_entries)
        if ca is not None:
            arity[callee] = ca
    callargs.rewrite(func, arity)

    opt.optimize(func)
    sig = abi.analyze_calling_convention(func, frame_info=frame_info, user_proto=u_proto, ret_types=_RET_CACHE)
    vars.recover_variables(func, sig, frame_info)
    tree = structure.structure(func)
    lines = cgen.generate(func, tree, namer, frame_info=frame_info, sig=sig, banner=None,
                          user_renames=u_renames, user_types=u_types)
    return Function(entry, namer.code(entry), func, tree, lines)
