"""
Pseudo-C back-end for the MeP/F00D decompiler.

Registers print as themselves or virtual variables (v0, v1, a0, ...); memory reads
as ``mem8/mem16/mem32`` (``s8``/``s16`` for sign-extending loads) indexed by an
address expression or symbolic name; conditional branches use the relational expression
the lifter recovered. Out-of-function tail jumps render as ``JUMPOUT(addr)``.
"""

from . import ir
from . import structure as S


_PRECEDENCE = {
    "*": 10, "/": 10, "%": 10,
    "+": 9, "-": 9,
    "<<": 8, ">>": 8,
    "<": 7, "<=": 7, ">": 7, ">=": 7,
    "==": 6, "!=": 6,
    "&": 5,
    "^": 4,
    "|": 3,
    "&&": 2,
    "||": 1,
}


class CodeLines(list):
    """List of generated C lines carrying a parallel line_eas mapping."""
    pass


class _Emit:
    def __init__(self, namer, block_starts=frozenset(), returns_value=False, hidden=frozenset(), user_renames=None, user_types=None):
        self.namer = namer
        self.block_starts = block_starts
        self.returns_value = returns_value
        self.hidden = hidden
        self.user_renames = user_renames or {}
        self.user_types = user_types or {}
        self.used_labels = set()
        self._pending = []

    def expr(self, e, top=True):
        if isinstance(e, ir.Const):
            if getattr(e, "name", None):
                return self.user_renames.get(e.name, e.name)
            v = e.value
            return str(v) if v < 10 else "0x%X" % v
        if isinstance(e, (ir.Reg, ir.Var)):
            return self.user_renames.get(e.name, e.name)
        if isinstance(e, ir.Mem):
            return self._mem(e)
        if isinstance(e, ir.Bin):
            op, r = e.op, e.r
            # render "+ 0xFFFFFFFF" (add #-1) etc. as a subtraction
            if op == "+" and isinstance(r, ir.Const) and r.value >= 0x80000000:
                op, r = "-", ir.Const((0x100000000 - r.value))
            rs = self.expr(r, False)
            s = "%s %s %s" % (self.expr(e.l, False), op, rs)
            return s if top else "(%s)" % s
        if isinstance(e, ir.Un):
            return "%s%s" % (e.op, self.expr(e.e, False))
        if isinstance(e, ir.IntrExpr):
            return "%s(%s)" % (e.name, ", ".join(self.expr(a) for a in e.args)) if e.args else e.name
        return "?"

    def _mem(self, e):
        if getattr(e, "name", None):
            return self.user_renames.get(e.name, e.name)
        pre = {1: "s8" if e.signed else "mem8", 2: "s16" if e.signed else "mem16",
               4: "mem32"}.get(e.width, "mem32")
        if isinstance(e.addr, ir.Expr):
            return "%s[%s]" % (pre, self.expr(e.addr))
        return "%s[0x%X]" % (pre, e.addr)

    def stmt(self, s):
        if isinstance(s, ir.Assign):
            return "%s = %s;" % (self.expr(s.dst), self.expr(s.src))
        if isinstance(s, ir.Call):
            args = ", ".join(self.expr(a) for a in (s.args or []))
            if s.target is not None:
                tgt_name = self.namer.code(s.target)
                tgt_name = self.user_renames.get(tgt_name, tgt_name)
                call_str = "%s(%s)" % (tgt_name, args)
            else:
                call_str = "(*%s)(%s)" % (self.expr(s.expr), args)
            if getattr(s, "is_tail", False):
                if self.returns_value:
                    return "return %s;" % call_str
                else:
                    return "%s;" % call_str
            return "%s;" % call_str
        if isinstance(s, ir.Intrinsic):
            call = "%s(%s);" % (s.name, ", ".join(self.expr(a) for a in s.args))
            return call + ("   /* %s */" % s.note if s.note else "")
        return "/* %s */" % type(s).__name__

    def _ext(self, ea):
        return self.namer.code(ea) if ea is not None else "?"

    def emit(self, nodes, ind):
        pad = "    " * ind
        for n in nodes:
            if isinstance(n, S.SLabel):
                self._pending.append((ind, None, n.ea, n.ea, [n.ea]))
            elif isinstance(n, S.SStmt):
                ea = getattr(n.stmt, "ea", None)
                inlined = list(getattr(n.stmt, "inlined_eas", []))
                all_eas = ([ea] if ea is not None else []) + inlined
                self._pending.append((ind, pad + self.stmt(n.stmt), None, ea, all_eas))
            elif isinstance(n, S.SRet):
                if self._pending and self._pending[-1][1] and self._pending[-1][1].strip().startswith("return "):
                    continue
                ea = getattr(n, "ea", None)
                self._pending.append((ind, pad + ("return r0;" if self.returns_value else "return;"), None, ea, [ea] if ea else []))
            elif isinstance(n, S.SGoto):
                ea = getattr(n, "ea", None)
                all_eas = [ea] if ea is not None else []
                if n.ea in self.block_starts:
                    self.used_labels.add(n.ea)
                    self._pending.append((ind, pad + "goto %s;" % self.namer.label(n.ea), None, ea, all_eas))
                else:
                    self._pending.append((ind, pad + "JUMPOUT(%s);" % self._ext(n.ea), None, ea, all_eas))
            elif isinstance(n, S.SIfGoto):
                br_ea = getattr(n, "branch_ea", None) or getattr(n, "ea", None)
                all_eas = [e for e in (br_ea, getattr(n, "ea", None)) if e is not None]
                if n.ea in self.block_starts:
                    self.used_labels.add(n.ea)
                    tail = "goto %s;" % self.namer.label(n.ea)
                else:
                    tail = "JUMPOUT(%s);" % self._ext(n.ea)
                self._pending.append((ind, pad + "if (%s) %s" % (self.expr(n.cond), tail), None, br_ea, all_eas))
            elif isinstance(n, S.SBreak):
                ea = getattr(n, "ea", None)
                self._pending.append((ind, pad + "break;", None, ea, [ea] if ea is not None else []))
            elif isinstance(n, S.SBreakIf):
                ea = getattr(n, "ea", None)
                self._pending.append((ind, pad + "if (%s) break;" % self.expr(n.cond), None, ea, [ea] if ea is not None else []))
            elif isinstance(n, S.SContinue):
                ea = getattr(n, "ea", None)
                all_eas = [ea] if ea is not None else []
                if n.cond is None:
                    self._pending.append((ind, pad + "continue;", None, ea, all_eas))
                else:
                    self._pending.append((ind, pad + "if (%s) continue;" % self.expr(n.cond), None, ea, all_eas))
            elif isinstance(n, S.SIf):
                ea = getattr(n, "ea", None)
                self._pending.append((ind, pad + "if (%s) {" % self.expr(n.cond), None, ea, [ea] if ea is not None else []))
                self.emit(n.then, ind + 1)
                if n.els:
                    self._pending.append((ind, pad + "} else {", None, None, []))
                    self.emit(n.els, ind + 1)
                self._pending.append((ind, pad + "}", None, None, []))
            elif isinstance(n, S.SWhile):
                self._emit_while(n, ind)
            elif isinstance(n, S.SSwitch):
                self._emit_switch(n, ind)

    def _emit_switch(self, n, ind):
        pad = "    " * ind
        ea = getattr(n, "ea", None)
        self._pending.append((ind, pad + "switch (%s) {" % self.expr(n.expr), None, ea, [ea] if ea is not None else []))
        for vals, arm in n.cases:
            for v in vals:
                v_str = str(v) if v < 10 else "0x%X" % v
                self._pending.append((ind, pad + "case %s:" % v_str, None, None, []))
            self.emit(arm, ind + 1)
        if n.default_body:
            self._pending.append((ind, pad + "default:", None, None, []))
            self.emit(n.default_body, ind + 1)
        self._pending.append((ind, pad + "}", None, None, []))

    def _emit_while(self, n, ind):
        pad = "    " * ind
        body = list(n.body)
        tail = None
        tail_ea = None
        ea = getattr(n, "ea", None)
        all_eas = [ea] if ea is not None else []
        if body and isinstance(body[-1], S.SContinue) and body[-1].cond is not None:
            tail = body[-1].cond
            tail_ea = getattr(body[-1], "ea", None)
            body = body[:-1]
        if tail is not None:
            self._pending.append((ind, pad + "do {", None, ea, all_eas))
            self.emit(body, ind + 1)
            t_eas = [tail_ea] if tail_ea is not None else []
            self._pending.append((ind, pad + "} while (%s);" % self.expr(tail), None, tail_ea, t_eas))
            return
        # Drop redundant unconditional `continue;` at the end of a while loop
        if body and isinstance(body[-1], S.SContinue) and body[-1].cond is None:
            body = body[:-1]
        # Check if the first statement after the loop header label is `if (cond) break;`
        first_idx = None
        for idx, item in enumerate(body):
            if not isinstance(item, S.SLabel):
                first_idx = idx
                break
        if first_idx is not None and isinstance(body[first_idx], S.SBreakIf):
            wcond = S.negate(body[first_idx].cond)
            body = body[:first_idx] + body[first_idx + 1:]
            self._pending.append((ind, pad + "while (%s) {" % self.expr(wcond), None, ea, all_eas))
            self.emit(body, ind + 1)
            self._pending.append((ind, pad + "}", None, None, []))
        else:
            self._pending.append((ind, pad + "while (1) {", None, ea, all_eas))
            self.emit(body, ind + 1)
            self._pending.append((ind, pad + "}", None, None, []))

    def flush(self):
        out = []
        line_eas = []
        line_to_eas = {}
        for ind, text, label_ea, primary_ea, all_eas in self._pending:
            if label_ea is not None:
                if label_ea in self.used_labels:
                    lineno = len(out)
                    out.append("%s:" % self.namer.label(label_ea))
                    line_eas.append(label_ea)
                    line_to_eas[lineno] = [label_ea]
                continue
            lineno = len(out)
            out.append(text)
            line_eas.append(primary_ea)
            unique_eas = list(dict.fromkeys(e for e in all_eas if e is not None))
            line_to_eas[lineno] = unique_eas
        return out, line_eas, line_to_eas


def generate(func, tree, namer, frame_info=None, sig=None, banner=None, user_renames=None, user_types=None):
    hidden = getattr(frame_info, "hidden_stmts", frozenset()) if frame_info else frozenset()
    u_renames = dict(getattr(frame_info, "user_renames", {}) or {})
    if user_renames:
        u_renames.update(user_renames)
    u_types = dict(getattr(frame_info, "user_types", {}) or {})
    if user_types:
        u_types.update(user_types)

    returns_value = (sig.ret_type != "void") if sig else False
    em = _Emit(namer, block_starts=frozenset(func.blocks), returns_value=returns_value,
               hidden=hidden, user_renames=u_renames, user_types=u_types)
    em.emit(tree, 1)
    body, body_eas, body_line_to_eas = em.flush()

    out = CodeLines()
    if banner:
        out.extend(banner)

    fn_name = namer.code(func.entry)
    fn_name = u_renames.get(fn_name, fn_name)

    if sig is not None:
        ret_t = u_types.get("__return__", sig.ret_type)
        if sig.params:
            param_parts = []
            for p in sig.params:
                p_name = u_renames.get(p.name, p.name)
                p_type = u_types.get(p.name, u_types.get(p_name, p.type_str))
                sep = "" if p_type.endswith("*") else " "
                param_parts.append(f"{p_type}{sep}{p_name}")
            pstr = ", ".join(param_parts)
        else:
            pstr = "void"
        ret_sep = "" if ret_t.endswith("*") else " "
        out.append(f"{ret_t}{ret_sep}{fn_name}({pstr})")
    else:
        out.append(f"void {fn_name}(void)")

    out.append("{")
    decls = []

    # Stack variable declarations
    if frame_info and frame_info.locals:
        def sort_loc(kv):
            name = kv[0]
            if "_" in name and name.split("_")[1].isalnum():
                try:
                    return (0, int(name.split("_")[1], 16))
                except ValueError:
                    pass
            return (1, name)

        for name, size in sorted(frame_info.locals.items(), key=sort_loc):
            eff_name = u_renames.get(name, name)
            default_t = {1: "char", 2: "short", 4: "int"}.get(size, "int")
            tstr = u_types.get(name, u_types.get(eff_name, default_t))
            sep = "" if tstr.endswith("*") else " "
            decls.append(f"    {tstr}{sep}{eff_name};")

    # Virtual variable declarations
    if frame_info and getattr(frame_info, "virtual_vars", None):
        def sort_vvar(kv):
            name = kv[0]
            if name.startswith("v") and name[1:].isdigit():
                return (0, int(name[1:]))
            return (1, name)

        for name, (var, width) in sorted(frame_info.virtual_vars.items(), key=sort_vvar):
            if frame_info.locals and name in frame_info.locals:
                continue
            eff_name = u_renames.get(name, name)
            default_t = "int"
            tstr = u_types.get(name, u_types.get(eff_name, default_t))
            sep = "" if tstr.endswith("*") else " "
            decls.append(f"    {tstr}{sep}{eff_name};")

    if decls:
        out.extend(decls)
        if body:
            out.append("")

    header_count = len(out)
    out.header_count = header_count
    out.extend(body)
    out.append("}")
    out.line_eas = [None] * header_count + body_eas + [None]

    # Map line numbers to associated instruction EAs
    out.line_to_eas = {header_count + k: v for k, v in body_line_to_eas.items()}
    out.ea_to_line = {}
    for lineno, eas in out.line_to_eas.items():
        for ea in eas:
            if ea not in out.ea_to_line:
                out.ea_to_line[ea] = lineno

    # Map function prototype and header lines to func.entry
    proto_lineno = len(banner) if banner else 0
    if proto_lineno < header_count:
        if func.entry not in out.ea_to_line:
            out.ea_to_line[func.entry] = proto_lineno
        for h_line in range(proto_lineno, header_count):
            if func.entry not in out.line_to_eas.setdefault(h_line, []):
                out.line_to_eas[h_line].append(func.entry)
            out.line_eas[h_line] = func.entry

    # Dense instruction completion across all basic blocks in func
    if getattr(func, "blocks", None):
        sorted_blocks = sorted(func.blocks.values(), key=lambda b: b.start)
        for b in sorted_blocks:
            b_lines = []
            for s in b.stmts:
                s_ea = getattr(s, "ea", None)
                if s_ea in out.ea_to_line:
                    b_lines.append((s_ea, out.ea_to_line[s_ea]))
            for ins in getattr(b, "insns", []):
                if ins.ea in out.ea_to_line:
                    continue
                chosen_line = None
                if b_lines:
                    _, chosen_line = min(b_lines, key=lambda pair: abs(pair[0] - ins.ea))
                elif b.start in out.ea_to_line:
                    chosen_line = out.ea_to_line[b.start]
                else:
                    chosen_line = proto_lineno if proto_lineno >= 0 else 0
                if chosen_line is not None:
                    out.ea_to_line[ins.ea] = chosen_line
                    if ins.ea not in out.line_to_eas.setdefault(chosen_line, []):
                        out.line_to_eas[chosen_line].append(ins.ea)

    return out
