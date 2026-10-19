"""
High-Level Virtual Variable Recovery and Register Tracing Layer for Toshiba MeP.

This module elevates decompiler IR from machine registers to high-level C variables:
1. Reaching Definitions Analysis:
   Performs iterative dataflow analysis on general-purpose registers (r0..r12) and
   stack variables across the entire CFG.
2. Def-Use Web Construction:
   Unifies definitions and uses that reach each other into connected live-range webs
   using Union-Find. Each web corresponds to an independent virtual variable (v0, v1, ...).
3. Parameter Binding:
   Binds live-in register reads at function entry (r1..r4) directly to parameter
   names (a0..a3).
4. Stack Spill Bridging & Elimination:
   Bridges callee-saved register spills (r5..r12, lp) to the underlying values,
   eliminating phantom variables.
5. Copy Propagation & Dead Store Elimination:
   Eliminates redundant variable-to-variable copies and dead assignments to temporaries.
6. Single-Use Inlining:
   Inlines pure single-use temporary variables into their use sites, producing natural C expressions.
7. Variable Declarations:
   Collects all virtual variables and records their deduced types for
   declaration at the function head.
"""

from . import ir

MEP_GPRS = {f"r{i}" for i in range(13)}
CALLER_SAVED = {"r0", "r1", "r2", "r3", "r4", "lp"}
CALLEE_SAVED = {f"r{i}" for i in range(5, 13)}


class _UnionFind:
    def __init__(self):
        self.parent = {}

    def find(self, x):
        if x not in self.parent:
            self.parent[x] = x
            return x
        if self.parent[x] != x:
            self.parent[x] = self.find(self.parent[x])
        return self.parent[x]

    def union(self, x, y):
        rx, ry = self.find(x), self.find(y)
        if rx != ry:
            self.parent[rx] = ry


def _collect_expr_regs(e, out_regs):
    """Collect register reads from expression e."""
    if isinstance(e, ir.Reg) and e.name in MEP_GPRS:
        out_regs.append(e.name)
    elif isinstance(e, ir.Var):
        out_regs.append(e.name)
    elif isinstance(e, ir.Bin):
        _collect_expr_regs(e.l, out_regs)
        _collect_expr_regs(e.r, out_regs)
    elif isinstance(e, ir.Un):
        _collect_expr_regs(e.e, out_regs)
    elif isinstance(e, ir.Mem) and isinstance(e.addr, ir.Expr):
        _collect_expr_regs(e.addr, out_regs)
    elif isinstance(e, ir.IntrExpr):
        for a in e.args:
            _collect_expr_regs(a, out_regs)


def _get_stmt_uses(s):
    """Return all GPR and variable uses in statement s."""
    uses = []
    if isinstance(s, ir.Assign):
        _collect_expr_regs(s.src, uses)
        if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr):
            _collect_expr_regs(s.dst.addr, uses)
    elif isinstance(s, ir.Call):
        if s.args:
            for a in s.args:
                _collect_expr_regs(a, uses)
        if s.expr:
            _collect_expr_regs(s.expr, uses)
    elif isinstance(s, ir.Branch):
        if isinstance(s.cexpr, ir.Expr):
            _collect_expr_regs(s.cexpr, uses)
    elif isinstance(s, ir.Switch) and isinstance(s.expr, ir.Expr):
        _collect_expr_regs(s.expr, uses)
    elif isinstance(s, ir.Intrinsic):
        for a in s.args:
            _collect_expr_regs(a, uses)
    elif isinstance(s, ir.Ret):
        # A return reading r0 (implicit or explicit)
        pass
    return uses


def _get_stmt_defs(s):
    """Return all GPR definitions and clobbers in statement s."""
    defs = []
    clobbers = []
    if isinstance(s, ir.Assign):
        if isinstance(s.dst, ir.Reg) and s.dst.name in MEP_GPRS:
            defs.append(s.dst.name)
        elif isinstance(s.dst, ir.Var):
            defs.append(s.dst.name)
    elif isinstance(s, ir.Call):
        if not getattr(s, "is_tail", False):
            for r in CALLER_SAVED:
                if r in MEP_GPRS:
                    clobbers.append(r)
    return defs, clobbers


def _expr_uses_var(e, var_name):
    """Return True if expression e references a Var or Reg named var_name."""
    if isinstance(e, (ir.Var, ir.Reg)) and e.name == var_name:
        return True
    if isinstance(e, ir.Bin):
        return _expr_uses_var(e.l, var_name) or _expr_uses_var(e.r, var_name)
    if isinstance(e, ir.Un):
        return _expr_uses_var(e.e, var_name)
    if isinstance(e, ir.Mem) and isinstance(e.addr, ir.Expr):
        return _expr_uses_var(e.addr, var_name)
    if isinstance(e, ir.IntrExpr):
        return any(_expr_uses_var(a, var_name) for a in e.args)
    return False


def _stmt_uses_var(s, var_name):
    """Return True if statement s references var_name in any read position."""
    if isinstance(s, ir.Assign):
        if _expr_uses_var(s.src, var_name):
            return True
        if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr) and _expr_uses_var(s.dst.addr, var_name):
            return True
        return False
    if isinstance(s, ir.Call):
        if s.args and any(_expr_uses_var(a, var_name) for a in s.args):
            return True
        if s.expr and _expr_uses_var(s.expr, var_name):
            return True
        return False
    if isinstance(s, ir.Branch):
        return isinstance(s.cexpr, ir.Expr) and _expr_uses_var(s.cexpr, var_name)
    if isinstance(s, ir.Switch):
        return isinstance(s.expr, ir.Expr) and _expr_uses_var(s.expr, var_name)
    if isinstance(s, ir.Intrinsic):
        return any(_expr_uses_var(a, var_name) for a in s.args)
    return False


def _subst_ast(e, repl_map):
    """Substitute variables in expression e using repl_map."""
    if isinstance(e, (ir.Reg, ir.Var)) and e.name in repl_map:
        return repl_map[e.name]
    if isinstance(e, ir.Bin):
        nl = _subst_ast(e.l, repl_map)
        nr = _subst_ast(e.r, repl_map)
        if nl is not e.l or nr is not e.r:
            return ir.Bin(e.op, nl, nr)
        return e
    if isinstance(e, ir.Un):
        ne = _subst_ast(e.e, repl_map)
        if ne is not e.e:
            return ir.Un(e.op, ne)
        return e
    if isinstance(e, ir.Mem):
        if isinstance(e.addr, ir.Expr):
            na = _subst_ast(e.addr, repl_map)
            if na is not e.addr:
                return ir.Mem(na, e.width, e.signed, e.name)
        return e
    if isinstance(e, ir.IntrExpr):
        new_args = [_subst_ast(a, repl_map) for a in e.args]
        if any(na is not oa for na, oa in zip(new_args, e.args)):
            return ir.IntrExpr(e.name, new_args)
        return e
    return e


def _subst_stmt_var(s, var_name, target_expr):
    """Substitute var_name with target_expr in all read positions of statement s."""
    repl = {var_name: target_expr}
    changed = False
    if isinstance(s, ir.Assign):
        if _expr_uses_var(s.src, var_name):
            s.src = _subst_ast(s.src, repl)
            changed = True
        if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr):
            if _expr_uses_var(s.dst.addr, var_name):
                s.dst.addr = _subst_ast(s.dst.addr, repl)
                changed = True
    elif isinstance(s, ir.Call):
        if s.args:
            new_args = []
            for a in s.args:
                if _expr_uses_var(a, var_name):
                    new_args.append(_subst_ast(a, repl))
                    changed = True
                else:
                    new_args.append(a)
            if changed:
                s.args = new_args
        if s.expr and _expr_uses_var(s.expr, var_name):
            s.expr = _subst_ast(s.expr, repl)
            changed = True
    elif isinstance(s, ir.Branch):
        if isinstance(s.cexpr, ir.Expr) and _expr_uses_var(s.cexpr, var_name):
            s.cexpr = _subst_ast(s.cexpr, repl)
            changed = True
    elif isinstance(s, ir.Switch) and isinstance(s.expr, ir.Expr):
        if _expr_uses_var(s.expr, var_name):
            s.expr = _subst_ast(s.expr, repl)
            changed = True
    elif isinstance(s, ir.Intrinsic):
        new_args = []
        for a in s.args:
            if _expr_uses_var(a, var_name):
                new_args.append(_subst_ast(a, repl))
                changed = True
            else:
                new_args.append(a)
        if changed:
            s.args = new_args
    return changed


def _is_pure_expr(e):
    if isinstance(e, (ir.Const, ir.Reg, ir.Var)):
        return True
    if isinstance(e, ir.Bin):
        return _is_pure_expr(e.l) and _is_pure_expr(e.r)
    if isinstance(e, ir.Un):
        return _is_pure_expr(e.e)
    if isinstance(e, ir.IntrExpr):
        return all(_is_pure_expr(a) for a in e.args)
    return False


def _compute_var_counts(func, hidden):
    """Compute use_count and def_count for all variables/registers in func."""
    use_count = {}
    def_count = {}

    def count_in_expr(e):
        if isinstance(e, (ir.Var, ir.Reg)):
            use_count[e.name] = use_count.get(e.name, 0) + 1
        elif isinstance(e, ir.Bin):
            count_in_expr(e.l)
            count_in_expr(e.r)
        elif isinstance(e, ir.Un):
            count_in_expr(e.e)
        elif isinstance(e, ir.Mem) and isinstance(e.addr, ir.Expr):
            count_in_expr(e.addr)
        elif isinstance(e, ir.IntrExpr):
            for a in e.args:
                count_in_expr(a)

    for b in func.blocks.values():
        for s in b.stmts:
            if id(s) in hidden:
                continue
            if isinstance(s, ir.Assign):
                count_in_expr(s.src)
                if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr):
                    count_in_expr(s.dst.addr)
                elif isinstance(s.dst, (ir.Var, ir.Reg)):
                    def_count[s.dst.name] = def_count.get(s.dst.name, 0) + 1
            elif isinstance(s, ir.Call):
                if s.args:
                    for a in s.args:
                        count_in_expr(a)
                if s.expr:
                    count_in_expr(s.expr)
            elif isinstance(s, ir.Branch):
                if isinstance(s.cexpr, ir.Expr):
                    count_in_expr(s.cexpr)
            elif isinstance(s, ir.Switch) and isinstance(s.expr, ir.Expr):
                count_in_expr(s.expr)
            elif isinstance(s, ir.Intrinsic):
                for a in s.args:
                    count_in_expr(a)

    return use_count, def_count


def _fold_temp_copies(func, hidden):
    """Fold direct variable copies (v1 = v0) into subsequent uses within basic blocks."""
    changed = False
    for b in func.blocks.values():
        new_stmts = []
        i = 0
        stmts = b.stmts
        while i < len(stmts):
            s = stmts[i]
            if id(s) in hidden:
                new_stmts.append(s)
                i += 1
                continue

            if isinstance(s, ir.Assign) and isinstance(s.dst, ir.Var) and isinstance(s.src, ir.Var):
                # v_dst = v_src
                dst_name = s.dst.name
                src_var = s.src

                # Check if dst_name is read subsequently and can be replaced
                can_propagate = True
                subst_count = 0
                for j in range(i + 1, len(stmts)):
                    nxt = stmts[j]
                    if id(nxt) in hidden:
                        continue
                    # Stop if v_src is modified
                    nxt_defs, _ = _get_stmt_defs(nxt)
                    if src_var.name in nxt_defs:
                        break
                    if _subst_stmt_var(nxt, dst_name, src_var):
                        subst_count += 1
                        changed = True
                    # Stop if dst_name is overwritten
                    if dst_name in nxt_defs:
                        break

            new_stmts.append(s)
            i += 1
        b.stmts = new_stmts
    return changed


def _inline_single_use(func, hidden):
    """Inline pure expressions assigned to temporary variables used exactly once in the same block."""
    use_count, def_count = _compute_var_counts(func, hidden)
    changed = False

    for b in func.blocks.values():
        new_stmts = []
        i = 0
        stmts = b.stmts
        while i < len(stmts):
            s = stmts[i]
            if id(s) in hidden:
                new_stmts.append(s)
                i += 1
                continue

            # Look for v = pure_expr where v is defined once and used once
            if (isinstance(s, ir.Assign)
                and isinstance(s.dst, ir.Var)
                and s.dst.name.startswith("v")
                and def_count.get(s.dst.name, 0) == 1
                and use_count.get(s.dst.name, 0) == 1
                and _is_pure_expr(s.src)):

                v_name = s.dst.name
                # Find use in the same block without intervening side effects
                can_inline = False
                target_stmt_idx = None
                for j in range(i + 1, len(stmts)):
                    nxt = stmts[j]
                    if id(nxt) in hidden:
                        continue
                    if _stmt_uses_var(nxt, v_name):
                        can_inline = True
                        target_stmt_idx = j
                        break
                    # If intervening statement has side effects or writes variables in s.src, stop
                    nxt_defs, _ = _get_stmt_defs(nxt)
                    if any(_expr_uses_var(s.src, d) for d in nxt_defs):
                        break

                if can_inline and target_stmt_idx is not None:
                    nxt = stmts[target_stmt_idx]
                    if _subst_stmt_var(nxt, v_name, s.src):
                        if getattr(nxt, "inlined_eas", None) is None:
                            nxt.inlined_eas = []
                        if getattr(s, "ea", None) is not None:
                            nxt.inlined_eas.append(s.ea)
                        if getattr(s, "inlined_eas", None):
                            nxt.inlined_eas.extend(s.inlined_eas)
                        changed = True
                        i += 1
                        continue

            new_stmts.append(s)
            i += 1
        b.stmts = new_stmts
    return changed


def _eliminate_dead_assignments(func, hidden, sig=None):
    """Eliminate dead assignments to temporaries and unused virtual variables."""
    protected_names = set()
    if sig and sig.ret_type != "void":
        protected_names.add("r0")

    changed = True
    any_changed = False
    iterations = 0
    while changed and iterations < 10:
        changed = False
        iterations += 1
        use_count, _ = _compute_var_counts(func, hidden)

        for b in func.blocks.values():
            new_stmts = []
            for s in b.stmts:
                if id(s) in hidden:
                    new_stmts.append(s)
                    continue

                if isinstance(s, ir.Assign) and _is_pure_expr(s.src):
                    # Check virtual variables
                    if isinstance(s.dst, ir.Var) and s.dst.name.startswith("v") and s.dst.name[1:].isdigit():
                        if use_count.get(s.dst.name, 0) == 0:
                            changed = True
                            any_changed = True
                            continue
                    # Check GPRs
                    elif isinstance(s.dst, ir.Reg) and s.dst.name in MEP_GPRS:
                        if use_count.get(s.dst.name, 0) == 0 and s.dst.name not in protected_names:
                            changed = True
                            any_changed = True
                            continue

                new_stmts.append(s)
            b.stmts = new_stmts
    return any_changed


def recover_variables(func, sig, frame_info):
    """Main virtual variable recovery pass for Toshiba MeP."""
    hidden = getattr(frame_info, "hidden_stmts", frozenset()) or frozenset()
    preds = {b_ea: [] for b_ea in func.blocks}
    for b in func.blocks.values():
        for _, succ_ea in b.succ:
            if succ_ea in preds:
                preds[succ_ea].append(b.start)

    # 1. Reaching definitions dataflow analysis
    out_defs = {}
    stmt_reaching = {}

    changed = True
    iterations = 0
    ordered = func.ordered()
    while changed and iterations < 20:
        changed = False
        iterations += 1
        for b in ordered:
            cur = {}
            for p_ea in preds[b.start]:
                for reg, dset in out_defs.get(p_ea, {}).items():
                    cur.setdefault(reg, set()).update(dset)

            if b.start == func.entry:
                for reg in MEP_GPRS:
                    cur.setdefault(reg, set()).add(("entry", reg))

            for s in b.stmts:
                if id(s) in hidden:
                    continue

                uses = _get_stmt_uses(s)
                for reg in uses:
                    stmt_reaching[(id(s), reg)] = set(cur.get(reg, set()))

                defs, clobbers = _get_stmt_defs(s)
                for reg in defs:
                    cur[reg] = {(id(s), reg)}
                for reg in clobbers:
                    cur[reg] = {("clobber", id(s), reg)}

            old_out = out_defs.get(b.start, {})
            if cur != old_out:
                out_defs[b.start] = cur
                changed = True

    # 2. Def-Use Web Construction via Union-Find
    uf = _UnionFind()
    for (s_id, reg), reaching in stmt_reaching.items():
        use_key = (s_id, reg, "use")
        for def_site in reaching:
            if def_site[0] == "clobber":
                continue
            uf.union(use_key, def_site)

    # 3. Web assignment to parameters and virtual variables
    groups = {}
    for node in list(uf.parent.keys()):
        root = uf.find(node)
        groups.setdefault(root, set()).add(node)

    web_var = {}
    var_counter = 0

    param_map = {}
    if sig and sig.params:
        for p in sig.params:
            if p.location in ("r1", "r2", "r3", "r4"):
                param_map[p.name] = p.location

    for root, members in groups.items():
        name = None

        # Check parameter binding
        for p_name, rloc in param_map.items():
            if ("entry", rloc) in members:
                name = p_name
                break

        # Check stack args
        if name is None and frame_info and getattr(frame_info, "stack_args", None):
            for sname in frame_info.stack_args:
                if any(m[0] == "entry" and m[1] == sname for m in members):
                    name = sname
                    break

        if name is None:
            name = f"v{var_counter}"
            var_counter += 1

        web_var[root] = ir.Var(name, width="w")

    # 4. Rewrite Statements using Virtual Variables
    for b in func.blocks.values():
        new_stmts = []
        for s in b.stmts:
            if id(s) in hidden:
                new_stmts.append(s)
                continue

            uses_repl = {}
            for reg in _get_stmt_uses(s):
                use_key = (id(s), reg, "use")
                root = uf.find(use_key)
                if root in web_var:
                    uses_repl[reg] = web_var[root]

            dst_var = None
            defs, _ = _get_stmt_defs(s)
            if defs:
                reg = defs[0]
                def_key = (id(s), reg)
                root = uf.find(def_key)
                if root in web_var:
                    dst_var = web_var[root]

            if isinstance(s, ir.Assign):
                s.src = _subst_ast(s.src, uses_repl)
                if isinstance(s.dst, ir.Mem) and isinstance(s.dst.addr, ir.Expr):
                    s.dst.addr = _subst_ast(s.dst.addr, uses_repl)
                elif dst_var is not None:
                    s.dst = dst_var

                # Drop identity assignments (v0 = v0)
                if isinstance(s.dst, ir.Var) and isinstance(s.src, ir.Var) and s.dst.name == s.src.name:
                    continue

            elif isinstance(s, ir.Branch):
                if isinstance(s.cexpr, ir.Expr):
                    s.cexpr = _subst_ast(s.cexpr, uses_repl)
            elif isinstance(s, ir.Switch) and isinstance(s.expr, ir.Expr):
                s.expr = _subst_ast(s.expr, uses_repl)
            elif isinstance(s, ir.Call):
                if s.args:
                    s.args = [_subst_ast(a, uses_repl) for a in s.args]
                if s.expr:
                    s.expr = _subst_ast(s.expr, uses_repl)
            elif isinstance(s, ir.Intrinsic):
                s.args = [_subst_ast(a, uses_repl) for a in s.args]

            new_stmts.append(s)
        b.stmts = new_stmts

    # 5. Optimize: Copy Folding, Single-Use Inlining, Dead Assignment Elimination
    for _ in range(8):
        c1 = _eliminate_dead_assignments(func, hidden, sig=sig)
        c2 = _fold_temp_copies(func, hidden)
        c3 = _inline_single_use(func, hidden)
        if not (c1 or c2 or c3):
            break
    _eliminate_dead_assignments(func, hidden, sig=sig)

    # 6. Collect virtual variables for function declaration
    virtual_vars = {}

    def _collect_vvar(e):
        if isinstance(e, ir.Var) and not isinstance(e, ir.StackVar) and e.name.startswith("v") and e.name[1:].isdigit():
            virtual_vars[e.name] = (e, "w")
        elif isinstance(e, ir.Bin):
            _collect_vvar(e.l)
            _collect_vvar(e.r)
        elif isinstance(e, ir.Un):
            _collect_vvar(e.e)
        elif isinstance(e, ir.Mem) and isinstance(e.addr, ir.Expr):
            _collect_vvar(e.addr)
        elif isinstance(e, ir.IntrExpr):
            for a in e.args:
                _collect_vvar(a)

    for b in func.blocks.values():
        for s in b.stmts:
            if id(s) in hidden:
                continue
            if isinstance(s, ir.Assign):
                _collect_vvar(s.dst)
                _collect_vvar(s.src)
            elif isinstance(s, ir.Call):
                if s.args:
                    for a in s.args:
                        _collect_vvar(a)
                if s.expr:
                    _collect_vvar(s.expr)
            elif isinstance(s, ir.Branch):
                if isinstance(s.cexpr, ir.Expr):
                    _collect_vvar(s.cexpr)
            elif isinstance(s, ir.Switch) and isinstance(s.expr, ir.Expr):
                _collect_vvar(s.expr)
            elif isinstance(s, ir.Intrinsic):
                for a in s.args:
                    _collect_vvar(a)

    if frame_info:
        frame_info.virtual_vars = virtual_vars

    return func
