#!/usr/bin/env python3
"""Exhaustive, model-exact search: can k hard-attention heads + one linear
threshold readout compute parityN?

Evidence artifact for AttentionLean/ParityAchieve.lean (W2-T5). Refutes the
briefed target `parityN_achievable_with_N_heads` at n = 3 and establishes the
empirical exact head complexities k(2) = 2, k(3) = 4 = 2^(n-1).

Model exactness. A head's score depends only on (i, x_i) (`scoreVal` /
`attentionScore_eq_scoreVal`, Defs.lean); the winner is the max-score live
literal with min-index tie-break (`argmaxScore`); the output is a threshold
of the read value at the winner (`headOutput`). With internal dimension
d >= 2 arbitrary (score, read) pairs per literal are realizable, and weak
orders with the index tie-break collapse to strict priorities, so realizable
head outputs are EXACTLY the "priority functions": fix a strict priority
order on the 2n literals (i, b) and an output bit per literal; the output is
the bit of the highest-priority live literal. Cross-check: this enumeration
yields 96 distinct functions at n = 3 — equal to the repo's own
`achievable3Raw` mask count (ParitySmall.lean).

Results (rerun to verify):
  n=2: |realizable| = 14, |LTFs on 2 bits| = 14; parity2 with 2 heads:
       8 solutions (the AND/OR pair among them).
  n=3: |realizable| = 96, |LTFs on 3 bits| = 104 (known exact count);
       parity3 with 3 heads: 0 of 152,096 head multisets. REFUTED.
  n=3 with 4 heads: |LTFs on 4 bits| = 1882 (known exact count);
       solutions exist (>= 50 found before early stop); among them the
       odd-point indicator family the Lean construction generalizes.
"""

import itertools
from functools import lru_cache


def priority_functions(n):
    """All boolean functions on {0,1}^n realizable as hard-attention head
    outputs: priority order on 2n literals, output bit per literal."""
    lits = [(i, b) for i in range(n) for b in (0, 1)]
    nl = len(lits)
    R = {}
    winners_seen = set()
    for perm in itertools.permutations(range(nl)):
        winners = []
        for x in range(2 ** n):
            for j in perm:
                (i, b) = lits[j]
                if ((x >> i) & 1) == b:
                    winners.append(j)
                    break
        wt = tuple(winners)
        if wt in winners_seen:
            continue
        winners_seen.add(wt)
        for rmask in range(2 ** nl):
            out = 0
            for xi in range(2 ** n):
                if (rmask >> winners[xi]) & 1:
                    out |= 1 << xi
            R.setdefault(out, (perm, rmask))
    return R


def ltf_labelings(k, rng=9):
    """All labelings of the 2^k points of {0,1}^k achievable by a strict
    linear threshold sign(u.p + c > 0), integer grid |u_i|,|c| <= rng."""
    pts = [tuple((p >> i) & 1 for i in range(k)) for p in range(2 ** k)]
    labs = {}
    for u in itertools.product(range(-rng, rng + 1), repeat=k):
        for c in range(-rng, rng + 1):
            m = 0
            for pi, p in enumerate(pts):
                if sum(ui * xi for ui, xi in zip(u, p)) + c > 0:
                    m |= 1 << pi
            labs.setdefault(m, (u, c))
    return labs


def parity_mask(n):
    m = 0
    for x in range(2 ** n):
        if bin(x).count("1") % 2 == 1:
            m |= 1 << x
    return m


def solve(n, k, max_solutions=50):
    """Search all multisets of k realizable head functions for an LTF
    combination computing parityN. Returns (checked, solutions)."""
    R = priority_functions(n)
    Rlist = sorted(R)
    labs = list(ltf_labelings(k).items())
    par = parity_mask(n)
    print(f"n={n}, k={k}: |realizable|={len(Rlist)}, |LTF labelings on {k}-cube|={len(labs)}")

    @lru_cache(maxsize=None)
    def separable(constraints):
        for m, w in labs:
            if all(req < 0 or ((m >> pi) & 1) == req
                   for pi, req in enumerate(constraints)):
                return w
        return None

    checked, sols = 0, []
    for combo in itertools.combinations_with_replacement(Rlist, k):
        checked += 1
        cons = [-1] * (2 ** k)
        ok = True
        for x in range(2 ** n):
            pt = 0
            for hi, f in enumerate(combo):
                if (f >> x) & 1:
                    pt |= 1 << hi
            req = (par >> x) & 1
            if cons[pt] == -1:
                cons[pt] = req
            elif cons[pt] != req:
                ok = False
                break
        if not ok:
            continue
        w = separable(tuple(cons))
        if w:
            sols.append((combo, w))
            if len(sols) >= max_solutions:
                break
    tail = "+" if len(sols) >= max_solutions else ""
    print(f"  multisets checked: {checked}, solutions: {len(sols)}{tail}")
    return checked, sols


if __name__ == "__main__":
    _, s22 = solve(2, 2)
    _, s33 = solve(3, 3)
    _, s34 = solve(3, 4)
    print()
    print(f"parity2 with 2 heads: {'ACHIEVABLE' if s22 else 'IMPOSSIBLE'}")
    print(f"parity3 with 3 heads: {'ACHIEVABLE' if s33 else 'IMPOSSIBLE'}"
          f"  <- refutes parityN_achievable_with_N_heads")
    print(f"parity3 with 4 heads: {'ACHIEVABLE' if s34 else 'IMPOSSIBLE'}"
          f"  (4 = 2^(3-1); see ParityAchieve.lean for the general theorem)")
