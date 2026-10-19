"""
IR for the MeP/F00D decompiler.

A register machine (like rl78dec) but simpler: MeP conditional branches are
self-contained register compares, so a :class:`Branch` carries its condition
expression directly and there is no PSW/flag layer.  Statement shapes match the
other tools so the control-flow structurer and highlighter are shared.
"""


class Expr:
    pass


class Const(Expr):
    __slots__ = ("value", "name", "width")

    def __init__(self, value, width="w", name=None):
        self.value = value & 0xFFFFFFFF
        self.width = width
        self.name = name

    def __eq__(self, o):
        return isinstance(o, Const) and o.value == self.value

    def __hash__(self):
        return hash(("const", self.value))


class Reg(Expr):
    __slots__ = ("name", "width")

    def __init__(self, name, width="w"):
        self.name = name
        self.width = width

    def __eq__(self, o):
        return isinstance(o, Reg) and o.name == self.name

    def __hash__(self):
        return hash(("reg", self.name))


class Var(Expr):
    """Virtual high-level variable (v0, v1, a0, arg_0, etc.)."""
    __slots__ = ("name", "width")

    def __init__(self, name, width="w"):
        self.name = name
        self.width = width

    def __eq__(self, o):
        return isinstance(o, Var) and o.name == self.name

    def __hash__(self):
        return hash(("var", self.name))


class StackVar(Var):
    """A stack frame variable or argument slot."""
    __slots__ = ("offset", "is_arg")

    def __init__(self, name, width="w", offset=0, is_arg=False):
        super().__init__(name, width)
        self.offset = offset
        self.is_arg = is_arg

    def __eq__(self, o):
        return isinstance(o, StackVar) and o.name == self.name and o.offset == self.offset

    def __hash__(self):
        return hash(("stackvar", self.name, self.offset))


class Mem(Expr):
    """Memory access; ``addr`` is an int (absolute) or an Expr (reg-based).
    width in bytes (1/2/4); ``signed`` selects sign- vs zero-extension;
    ``name`` is an optional symbolic name from IDA."""
    __slots__ = ("addr", "width", "signed", "name")

    def __init__(self, addr, width=4, signed=False, name=None):
        self.addr = addr
        self.width = width
        self.signed = signed
        self.name = name


class Bin(Expr):
    __slots__ = ("op", "l", "r")

    def __init__(self, op, l, r):
        self.op = op
        self.l = l
        self.r = r


class Un(Expr):
    __slots__ = ("op", "e")

    def __init__(self, op, e):
        self.op = op
        self.e = e


class IntrExpr(Expr):
    __slots__ = ("name", "args")

    def __init__(self, name, args):
        self.name = name
        self.args = args


# --- statements -------------------------------------------------------------

class Assign:
    __slots__ = ("ea", "dst", "src", "inlined_eas")

    def __init__(self, ea, dst, src, inlined_eas=None):
        self.ea = ea
        self.dst = dst
        self.src = src
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Call:
    __slots__ = ("ea", "target", "expr", "args", "is_tail", "inlined_eas")

    def __init__(self, ea, target=None, expr=None, args=None, is_tail=False, inlined_eas=None):
        self.ea = ea
        self.target = target
        self.expr = expr
        self.args = args          # list of argument exprs (filled by callargs pass)
        self.is_tail = is_tail
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Intrinsic:
    __slots__ = ("ea", "name", "args", "note", "inlined_eas")

    def __init__(self, ea, name, args, note="", inlined_eas=None):
        self.ea = ea
        self.name = name
        self.args = args
        self.note = note
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Ret:
    __slots__ = ("ea", "kind", "inlined_eas")

    def __init__(self, ea, kind="ret", inlined_eas=None):
        self.ea = ea
        self.kind = kind
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Goto:
    __slots__ = ("ea", "target", "inlined_eas")

    def __init__(self, ea, target, inlined_eas=None):
        self.ea = ea
        self.target = target
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Branch:
    __slots__ = ("ea", "cexpr", "target", "fallthrough", "inlined_eas")

    def __init__(self, ea, cexpr, target, fallthrough, inlined_eas=None):
        self.ea = ea
        self.cexpr = cexpr          # condition expression (taken when true)
        self.target = target
        self.fallthrough = fallthrough
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Switch:
    __slots__ = ("ea", "expr", "cases", "default_ea", "inlined_eas")

    def __init__(self, ea, expr, cases, default_ea=None, inlined_eas=None):
        self.ea = ea
        self.expr = expr            # switch controlling Expr
        self.cases = cases          # list of (case_val, target_ea)
        self.default_ea = default_ea
        self.inlined_eas = list(inlined_eas) if inlined_eas is not None else []


class Nop:
    __slots__ = ("ea",)

    def __init__(self, ea):
        self.ea = ea

