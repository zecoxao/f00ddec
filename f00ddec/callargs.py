"""
Call-argument folding: show how parameters are passed at each call site.

The MeP convention puts the first four integer arguments in ``r1``-``r4``
(further ones on the stack).  A compiler loads ``r1``, ``r2`` ... immediately
before the call, so this pass tracks the current value of each argument register
within a basic block and, at a ``Call``, attaches the contiguous ``r1``.. values
as the call's arguments and drops the now-folded ``rN = ...`` set-up statements.

    r1 = 1; r2 = 0x20; r3 = 0; foo();   -->   foo(1, 0x20, 0);

When the callee is one of our own functions its recovered parameter count caps
the list; for library calls (unknown arity) the contiguous run of argument
registers set since the previous call is used.  Stack-passed arguments (5+) are
not recovered.
"""

from . import ir

ARGS = ("r1", "r2", "r3", "r4")
_ARGSET = frozenset(ARGS)


def _expr_regs(e, out):
    if isinstance(e, ir.Reg):
        out.add(e.name)
    elif isinstance(e, ir.Bin):
        _expr_regs(e.l, out); _expr_regs(e.r, out)
    elif isinstance(e, ir.Un):
        _expr_regs(e.e, out)
    elif isinstance(e, ir.Mem) and isinstance(e.addr, ir.Expr):
        _expr_regs(e.addr, out)
    elif isinstance(e, ir.IntrExpr):
        for a in e.args:
            _expr_regs(a, out)
    return out


def _has_mem(e):
    if isinstance(e, ir.Mem):
        return True
    if isinstance(e, ir.Bin):
        return _has_mem(e.l) or _has_mem(e.r)
    if isinstance(e, ir.Un):
        return _has_mem(e.e)
    if isinstance(e, ir.IntrExpr):
        return any(_has_mem(a) for a in e.args)
    return False


def rewrite(func, arity=None):
    arity = arity or {}
    for b in func.blocks.values():
        argexpr = {}        # reg name -> current value expr
        argstmt = {}        # reg name -> the Assign that set it (to drop if folded)
        used_since = set()  # arg regs read since their Assign
        out = []
        for s in b.stmts:
            if isinstance(s, ir.Assign):
                src_regs = _expr_regs(s.src, set())
                if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr):
                    src_regs |= _expr_regs(s.dst.addr, set())
                used_since |= (src_regs & _ARGSET)

                if isinstance(s.dst, ir.Reg):
                    dname = s.dst.name
                    # Invalidate any pending arg expr that depends on dname
                    for a, ex in list(argexpr.items()):
                        if a != dname and dname in _expr_regs(ex, set()):
                            argexpr[a] = ir.Reg(a)
                            argstmt.pop(a, None)
                    if dname in _ARGSET:
                        # If `r1 = f(r1)` self-references `r1` and a prior `r1` setup is still in out,
                        # keep the prior setup statement so `r1` is defined before this update.
                        if dname in src_regs and dname in argstmt:
                            argstmt.pop(dname, None)
                        argexpr[dname] = s.src
                        argstmt[dname] = s
                        used_since.discard(dname)
                        out.append(s)
                        continue
                elif isinstance(s.dst, ir.Mem):
                    for a, ex in list(argexpr.items()):
                        if _has_mem(ex):
                            argexpr[a] = ir.Reg(a)
                            argstmt.pop(a, None)
                out.append(s)
                continue

            if isinstance(s, ir.Call):
                call_ptr_regs = _expr_regs(s.expr, set()) if s.expr is not None else set()
                n = arity.get(s.target)
                if n is not None:
                    k = n
                else:
                    set_indices = [idx for idx, a in enumerate(ARGS) if a in argexpr and a not in call_ptr_regs]
                    if getattr(s, "is_tail", False) and set_indices:
                        k = max(set_indices) + 1
                    else:
                        run = []
                        for a in ARGS:
                            if a in argexpr and a not in call_ptr_regs:
                                run.append(a)
                            else:
                                break
                        k = len(run)

                args_list = []
                for idx in range(min(k, len(ARGS))):
                    a = ARGS[idx]
                    if a in argexpr and a not in call_ptr_regs:
                        ex = argexpr[a]
                        st = argstmt.get(a)
                        if a in used_since and not isinstance(ex, (ir.Const, ir.Reg)):
                            args_list.append(ir.Reg(a))
                        else:
                            args_list.append(ex)
                            if st is not None and a not in used_since and st in out:
                                out.remove(st)
                                if getattr(s, "inlined_eas", None) is None:
                                    s.inlined_eas = []
                                if getattr(st, "ea", None) is not None:
                                    s.inlined_eas.append(st.ea)
                                if getattr(st, "inlined_eas", None):
                                    s.inlined_eas.extend(st.inlined_eas)
                    else:
                        args_list.append(ir.Reg(a))
                s.args = args_list
                argexpr.clear()
                argstmt.clear()
                used_since.clear()
                out.append(s)
                continue

            if isinstance(s, ir.Branch):
                used_since |= (_expr_regs(s.cexpr, set()) & _ARGSET)
            elif isinstance(s, ir.Switch):
                used_since |= (_expr_regs(s.expr, set()) & _ARGSET)
            elif isinstance(s, ir.Intrinsic):
                for a in s.args:
                    used_since |= (_expr_regs(a, set()) & _ARGSET)
            out.append(s)
        b.stmts = out
    return func

