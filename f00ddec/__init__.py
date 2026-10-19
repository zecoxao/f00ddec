"""
f00ddec -- a decompiler for the PS Vita "F00D" security processor, a
little-endian Toshiba MeP core.

Mirrors zecoxao's spudec and the Kirk/Spock (startrekdec) and RL78 (rl78dec)
tools: an IDA processor module is used purely as a decoder; the standalone
package re-implements that decoder so the whole pipeline runs headless on a raw
F00D dump.

    decoder -> lifter -> cfg -> opt -> structure -> cgen
"""

from . import decoder, cfg, opt, frame, callargs, recover, structure, cgen, loader, abi, vars, db
from .names import Namer

__version__ = "0.2.0"

BANNER = [
    "/*",
    " * Decompiled by f00ddec -- PS Vita F00D (Toshiba MeP, little-endian).",
    " * r0..r12/tp/gp/sp are the machine registers; mem8/mem16/mem32 index data",
    " * memory (s8/s16 = sign-extending loads).  Unmodelled opcodes are printed",
    " * as pseudo-calls; cross-function tail jumps as JUMPOUT().",
    " */",
    "",
]


class Function:
    def __init__(self, entry, name, func, tree, lines, line_eas=None, line_to_eas=None, ea_to_line=None, header_count=None):
        self.entry = entry
        self.name = name
        self.cfg = func
        self.tree = tree
        self.lines = lines
        self.line_eas = line_eas if line_eas is not None else getattr(lines, "line_eas", None)
        self.line_to_eas = line_to_eas if line_to_eas is not None else getattr(lines, "line_to_eas", {})
        self.ea_to_line = ea_to_line if ea_to_line is not None else getattr(lines, "ea_to_line", {})
        self.header_count = header_count if header_count is not None else getattr(lines, "header_count", 0)


class Program:
    def __init__(self, image, base, insns, funcs, namer):
        self.image = image
        self.base = base
        self.insns = insns
        self.funcs = funcs
        self.namer = namer

    def listing(self, banner=True):
        out = list(BANNER) if banner else []
        for entry in sorted(self.funcs):
            out.extend(self.funcs[entry].lines)
            out.append("")
        return "\n".join(out)


def decompile_image(image, entries, base=0, code_names=None):
    insns, calls = decoder.decode(image, entries=entries, base=base)
    funcs = cfg.build_functions(insns, calls, extra_entries=entries)
    namer = Namer(code_names=code_names)

    # 1. Pre-compute calling conventions and arities
    arity = {}
    for entry, f in funcs.items():
        frame_info = frame.analyze_frame(f)
        opt.optimize(f)
        sig = abi.analyze_calling_convention(f, frame_info=frame_info)
        arity[entry] = len(sig.params)

    # 2. Decompile each function with virtual variable recovery
    out = {}
    for entry, f in funcs.items():
        frame_info = frame.analyze_frame(f)
        callargs.rewrite(f, arity)
        opt.optimize(f)
        sig = abi.analyze_calling_convention(f, frame_info=frame_info)
        vars.recover_variables(f, sig, frame_info)
        tree = structure.structure(f)
        lines = cgen.generate(f, tree, namer, frame_info=frame_info, sig=sig)
        out[entry] = Function(entry, namer.code(entry), f, tree, lines)
    return Program(image, base, insns, out, namer)


def decompile_file(path, base=None, extra_entries=(), **kw):
    image = loader.load(path)
    det_base, reset = loader.detect_base(image)
    if base is None:
        base = det_base
    entries = list(loader.vector_entries(image, base))
    if reset:
        entries.append(reset)
    entries += list(extra_entries)
    return decompile_image(image, entries=entries, base=base, **kw)


def decompile_one(ea):
    from . import ida_bridge
    return ida_bridge.decompile_one(ea)

