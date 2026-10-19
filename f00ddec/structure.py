"""
Control-flow structuring (shared design with startrekdec/rl78dec).

Recovers if / while / do-while with a correct goto+label fallback.  MeP branches
carry their own condition expression, so ``cond_expr`` just returns it.
"""

from . import ir


class SStmt:
    def __init__(self, stmt): self.stmt = stmt
class SLabel:
    def __init__(self, ea): self.ea = ea
class SGoto:
    def __init__(self, ea): self.ea = ea
class SRet:
    def __init__(self, ea=None): self.ea = ea
class SIf:
    def __init__(self, cond, then, els, ea=None):
        self.cond = cond; self.then = then; self.els = els; self.ea = ea
class SIfGoto:
    def __init__(self, cond, ea, branch_ea=None):
        self.cond = cond; self.ea = ea; self.branch_ea = branch_ea
class SWhile:
    def __init__(self, body, cond=None, dowhile=False, ea=None):
        self.body = body; self.cond = cond; self.dowhile = dowhile; self.ea = ea
class SBreak:
    def __init__(self, ea=None): self.ea = ea
class SContinue:
    def __init__(self, cond=None, ea=None): self.cond = cond; self.ea = ea
class SBreakIf:
    def __init__(self, cond, ea=None): self.cond = cond; self.ea = ea
class SSwitch:
    def __init__(self, expr, cases, default_body=None, ea=None):
        self.expr = expr
        self.cases = cases              # list of (case_vals_list, body_nodes)
        self.default_body = default_body
        self.ea = ea


_NEG = {"==": "!=", "!=": "==", ">": "<=", "<": ">=", ">=": "<", "<=": ">"}


def cond_expr(branch):
    return branch.cexpr


def negate(e):
    if isinstance(e, ir.Un) and e.op == "!":
        return e.e
    if isinstance(e, ir.Bin) and e.op in _NEG:
        return ir.Bin(_NEG[e.op], e.l, e.r)
    if isinstance(e, ir.Const):
        return ir.Const(0 if e.value else 1)
    return ir.Un("!", e)


class _Structurer:
    def __init__(self, func):
        self.order = func.ordered()
        self.idx = {b.start: i for i, b in enumerate(self.order)}
        self.blocks = self.order
        self._open = set()
        self.preds = {b.start: set() for b in self.blocks}
        for i, b in enumerate(self.blocks):
            for _, tgt in b.succ:
                if tgt in self.preds:
                    self.preds[tgt].add(i)

    def run(self):
        return self._emit(0, len(self.blocks), loop=None, switch_merge=None)

    def _in_range(self, ea, lo, hi):
        i = self.idx.get(ea)
        return i is not None and lo <= i < hi

    def _region_clean(self, r_lo, r_hi, parent_idx):
        """Return True if no block inside (r_lo, r_hi) has predecessors outside [r_lo, r_hi)."""
        if r_hi - r_lo > 16:
            return False
        for k in range(r_lo, r_hi):
            if self.blocks[k].term == "switch":
                return False
            if k > r_lo:
                for p in self.preds.get(self.blocks[k].start, ()):
                    if not (r_lo <= p < r_hi) and p != parent_idx:
                        return False
        return True

    def _find_latch(self, header_idx, hi):
        h = self.blocks[header_idx].start
        latch = None
        for j in range(header_idx, hi):
            for _, tgt in self.blocks[j].succ:
                if tgt == h and j >= header_idx:
                    latch = j
        return latch

    def _body_stmts(self, block):
        out = []
        for s in block.stmts:
            if isinstance(s, (ir.Goto, ir.Branch, ir.Switch, ir.Ret, ir.Nop)):
                continue
            out.append(SStmt(s))
        return out

    def _branch_of(self, block):
        for s in block.stmts:
            if isinstance(s, ir.Branch):
                return s
        return None

    def _switch_of(self, block):
        for s in block.stmts:
            if isinstance(s, ir.Switch):
                return s
        return None

    def _emit(self, lo, hi, loop, switch_merge=None):
        out = []
        i = lo
        while i < hi:
            b = self.blocks[i]
            latch = None if i in self._open else self._find_latch(i, hi)
            if latch is not None:
                node, nxt = self._emit_loop(i, latch, hi)
                out.append(node)
                i = nxt
                continue
            out.append(SLabel(b.start))
            out.extend(self._body_stmts(b))

            term = b.term
            if term == "ret":
                ret_ea = b.insns[-1].ea if getattr(b, "insns", None) else None
                out.append(SRet(ea=ret_ea)); i += 1; continue
            if term == "goto":
                self._emit_edge(out, b.succ[0][1], lo, hi, loop, i + 1, switch_merge)
                i += 1
                continue
            if term == "switch":
                sw = self._switch_of(b)
                if sw is not None:
                    node, nxt = self._emit_switch(i, sw, hi, loop)
                    if node is not None:
                        out.append(node)
                        i = nxt
                        continue
                i += 1
                continue
            if term == "branch":
                br = self._branch_of(b)
                cond = cond_expr(br)
                br_ea = br.ea if br else (b.insns[-1].ea if getattr(b, "insns", None) else None)
                taken = b.succ[0][1]
                fall = b.succ[1][1] if len(b.succ) > 1 else None
                if switch_merge is not None and taken == switch_merge:
                    out.append(SBreakIf(cond, ea=br_ea))
                    self._fall_after(out, fall, loop, i, switch_merge)
                    i += 1
                    continue
                if loop is not None and taken == loop[0]:
                    out.append(SContinue(cond, ea=br_ea))
                    self._fall_after(out, fall, loop, i, switch_merge)
                    i += 1
                    continue
                if loop is not None and taken == loop[1] and switch_merge is None:
                    out.append(SBreakIf(cond, ea=br_ea))
                    self._fall_after(out, fall, loop, i, switch_merge)
                    i += 1
                    continue
                ti = self.idx.get(taken)
                if (ti is not None and i + 1 < ti <= hi and taken != b.start
                        and (loop is None or taken not in (loop[0], loop[1]))
                        and (switch_merge is None or taken != switch_merge)
                        and self._region_clean(i + 1, ti, i)):
                    # Check for if/else pattern where block ti-1 jumps past else block
                    last_then = self.blocks[ti - 1]
                    if (last_then.term == "goto" and last_then.succ
                            and self.preds.get(taken) == {i}):
                        else_end_ea = last_then.succ[0][1]
                        ei = self.idx.get(else_end_ea)
                        if (ei is not None and ti < ei <= hi
                                 and (switch_merge is None or else_end_ea != switch_merge)
                                 and self._region_clean(ti, ei, i)):
                            then = self._emit(i + 1, ti, loop, switch_merge)
                            if then and isinstance(then[-1], SGoto) and then[-1].ea == else_end_ea:
                                then = then[:-1]
                            els = self._emit(ti, ei, loop, switch_merge)
                            out.append(SIf(negate(cond), then, els, ea=br_ea))
                            i = ei
                            continue
                    then = self._emit(i + 1, ti, loop, switch_merge)
                    out.append(SIf(negate(cond), then, None, ea=br_ea))
                    i = ti
                    continue
                out.append(SIfGoto(cond, taken, branch_ea=br_ea))
                self._fall_after(out, fall, loop, i, switch_merge)
                i += 1
                continue
            if b.succ:
                tgt = b.succ[0][1]
                if self.idx.get(tgt) != i + 1:
                    self._emit_edge(out, tgt, lo, hi, loop, i + 1, switch_merge)
            i += 1
        return out

    def _emit_switch_arm(self, c_lo, c_hi, merge_ea, loop):
        nodes = self._emit(c_lo, c_hi, loop, switch_merge=merge_ea)
        # Ensure arm ends with break if it falls into merge_ea or next arm
        last_non_label = None
        for n in reversed(nodes):
            if not isinstance(n, SLabel):
                last_non_label = n
                break
        if not isinstance(last_non_label, (SBreak, SRet, SGoto, SContinue)):
            nodes.append(SBreak())
        return nodes

    def _emit_switch(self, i, sw, hi, loop):
        by_tgt = {}
        for val, tgt in sw.cases:
            by_tgt.setdefault(tgt, []).append(val)
        if not by_tgt:
            return None, i + 1
        for tgt in by_tgt:
            ti = self.idx.get(tgt)
            if ti is None or not (i < ti < hi):
                return None, i + 1
        sorted_tgts = sorted(by_tgt, key=lambda t: self.idx[t])
        c_idxs = [self.idx[t] for t in sorted_tgts]

        # Identify switch merge target from forward jumps at the end of case arms
        merge_counts = {}
        for k in range(len(c_idxs)):
            end_b_idx = (c_idxs[k + 1] - 1) if (k + 1 < len(c_idxs)) else c_idxs[k]
            if i < end_b_idx < hi:
                eb = self.blocks[end_b_idx]
                if eb.term in ("goto", "fall") and eb.succ:
                    t = eb.succ[0][1]
                    ti = self.idx.get(t)
                    if ti is not None and c_idxs[-1] < ti <= hi:
                        merge_counts[t] = merge_counts.get(t, 0) + 1

        merge_ea = None
        if merge_counts:
            merge_ea = max(merge_counts, key=lambda t: (merge_counts[t], -self.idx[t]))
        elif sw.default_ea is not None:
            di = self.idx.get(sw.default_ea)
            if di is not None and c_idxs[-1] < di <= hi:
                merge_ea = sw.default_ea

        if merge_ea is None:
            # Scan from last case start for first block jumping out or returning
            for j in range(c_idxs[-1], hi):
                if self.blocks[j].term in ("goto", "ret"):
                    if j + 1 < hi:
                        merge_ea = self.blocks[j + 1].start
                    break

        merge_idx = self.idx.get(merge_ea, hi) if merge_ea is not None else hi
        if merge_idx <= c_idxs[-1] or merge_idx > hi:
            merge_idx = hi
            merge_ea = self.blocks[merge_idx].start if merge_idx < len(self.blocks) else None

        cases_end_idx = merge_idx
        default_body = None
        if sw.default_ea is not None and sw.default_ea != merge_ea:
            di = self.idx.get(sw.default_ea)
            if di is not None and c_idxs[-1] < di < merge_idx:
                cases_end_idx = di
                default_body = self._emit_switch_arm(di, merge_idx, merge_ea, loop)
            else:
                default_body = [SGoto(sw.default_ea)]

        # Ensure the last case does not swallow blocks jumped to from before the switch
        for j in range(c_idxs[-1] + 1, cases_end_idx):
            b_ea = self.blocks[j].start
            if any(p < i for p in self.preds.get(b_ea, ())):
                cases_end_idx = j
                merge_idx = j
                merge_ea = self.blocks[j].start
                break

        case_arms = []


        for k, tgt in enumerate(sorted_tgts):
            c_lo = c_idxs[k]
            c_hi = c_idxs[k + 1] if k + 1 < len(c_idxs) else cases_end_idx
            arm = self._emit_switch_arm(c_lo, c_hi, merge_ea, loop)
            case_arms.append((by_tgt[tgt], arm))

        return SSwitch(sw.expr, case_arms, default_body, ea=sw.ea), merge_idx

    def _emit_loop(self, hidx, latch, hi):
        loop_lo, loop_hi = hidx, latch + 1
        header = self.blocks[hidx].start
        follow_ea = None
        for k, tgt in self.blocks[latch].succ:
            if not self._in_range(tgt, loop_lo, loop_hi):
                follow_ea = tgt
                break
        if follow_ea is None and loop_hi < len(self.blocks):
            follow_ea = self.blocks[loop_hi].start
        self._open.add(hidx)
        body = self._emit(loop_lo, loop_hi, (header, follow_ea), switch_merge=None)
        self._open.discard(hidx)
        nxt = latch + 1
        if follow_ea is not None and self.idx.get(follow_ea) is not None:
            f_idx = self.idx[follow_ea]
            if latch < f_idx <= hi:
                nxt = f_idx
        return SWhile(body, ea=header), nxt

    def _fall_after(self, out, fall, loop, i, switch_merge=None):
        if fall is None or self.idx.get(fall) == i + 1:
            return
        if switch_merge is not None and fall == switch_merge:
            out.append(SBreak()); return
        if loop is not None:
            if fall == loop[0]:
                out.append(SContinue()); return
            if fall == loop[1] and switch_merge is None:
                out.append(SBreak()); return
        out.append(SGoto(fall))

    def _emit_edge(self, out, tgt, lo, hi, loop, fall_i, switch_merge=None):
        if switch_merge is not None and tgt == switch_merge:
            out.append(SBreak()); return
        if loop is not None:
            if tgt == loop[0]:
                out.append(SContinue()); return
            if tgt == loop[1] and switch_merge is None:
                out.append(SBreak()); return
        if self.idx.get(tgt) == fall_i:
            return
        out.append(SGoto(tgt))


def structure(func):
    return _Structurer(func).run()

