#!/usr/bin/env python3
"""Design oracle for AttentionLean/WitnessMaj5Exact.lean (k(maj_5) >= 4).

Reconstructs, in the EXACT parametrization of the Lean module, the two
case kills that finish the k(maj_5) >= 4 proof on top of maj5_reduction
and the L1 threshold catalogs:

  CASE 2 (shared direction e, opposite signs): the third witness is
    catQ-classified on {x_e=1} and catQ3-classified on {x_e=0}
    (`case2C`). Result: ALL 2,880 parameter choices are unfixable; a
    2-pin hitting list of failing subcubes per direction e (size 8)
    covers every candidate. (Also checked: 5,760 of the 46,080 full
    triple assemblies pass refinement, and every one of them has
    unfixable C - the C-kill alone suffices.)

  CASE 3 (canonical directions 0,1,2, unanimous sign sigma): each
    witness is piecewise-catalog on two faces + constant on its own
    face + free on the region {x0=x1=x2=not sigma} (`case3A/B/C`).
    Under the slice-constancy (F1) and cross-face-consistency (F2)
    filters: 40 parameter parts per witness per sigma; of the 640
    (part, region) items, exactly 16 are fixable (the bad lists), the
    other 624 are covered by a 9-element hitting list of failing
    subcubes. The bad lists are mutually INCOMPATIBLE on the shared
    face subsets (matched bad triples: 0), so three simultaneously
    fixable case-3 witnesses cannot exist.

Every count printed here is re-verified in the kernel by the decides in
WitnessMaj5Exact.lean; this script is the design artifact.

Expected output ends with:
  case2: candidates 2880 unfixable 2880 (per-e hitting lists of size 8)
  case3 matched bad triples: sigma=1: 0  sigma=0: 0
"""

from itertools import product


def embed(e, i):
    return i if i < e else i + 1


def delAt(e, x5):
    return tuple(x5[embed(e, i)] for i in range(4))


def catBase(a, b, y):
    return y[a] | y[b] | int(all(y[j] for j in range(4) if j != a and j != b))


def catP(a, b, c, y):
    v = catBase(a, b, y)
    return v if c else 1 - v


def catCoBase(a, b, y):
    return int(any(y[j] for j in range(4) if j != a and j != b)) | (y[a] & y[b])


def catQ(a, b, c, y):
    v = catCoBase(a, b, y)
    return v if c else 1 - v


def catBase3(a, b, y):
    return y[a] & y[b] & int(any(y[j] for j in range(4) if j != a and j != b))


def catP3(a, b, c, y):
    v = catBase3(a, b, y)
    return v if c else 1 - v


def catCoBase3(a, b, y):
    return int(all(y[j] for j in range(4) if j != a and j != b)) & (y[a] | y[b])


def catQ3(a, b, c, y):
    v = catCoBase3(a, b, y)
    return v if c else 1 - v


PTS5 = [tuple((p >> j) & 1 for j in range(5)) for p in range(32)]
PAIRS = [(a, b) for a in range(4) for b in range(4) if a != b]
Y4 = list(product((0, 1), repeat=4))
RHOS = list(product((None, 0, 1), repeat=5))
REG = list(product((0, 1), repeat=4))


def PF(s, a, b, c, y):
    return catP(a, b, c, y) if s else catP3(a, b, c, y)


def QF(s, a, b, c, y):
    return catQ(a, b, c, y) if s else catQ3(a, b, c, y)


def regfn(bits):
    return {(0, 0): bits[0], (1, 0): bits[1], (0, 1): bits[2], (1, 1): bits[3]}


def failing_rhos(F):
    out = []
    for rho in RHOS:
        cube = [x for x in PTS5
                if all(r is None or x[k] == r for k, r in enumerate(rho))]
        ok = False
        for i in range(5):
            for b in (0, 1):
                if rho[i] == 1 - b:
                    continue
                if len({F[x] for x in cube if x[i] == b}) <= 1:
                    ok = True
                    break
            if ok:
                break
        if not ok:
            out.append(rho)
    return out


def pins(rho):
    return sum(1 for v in rho if v is not None)


def greedy_hit(items):
    cover = {}
    for idx, frs in enumerate(items):
        for r in frs:
            cover.setdefault(r, set()).add(idx)
    remaining = set(range(len(items)))
    hit = []
    while remaining:
        r, ss = max(cover.items(), key=lambda kv: len(kv[1] & remaining))
        if not (ss & remaining):
            break
        hit.append(r)
        remaining -= ss
    return hit, remaining


def main():
    # ---- CASE 2 ----
    total = 0
    unfix = 0
    for e in range(5):
        items = []
        for (a, b) in PAIRS:
            for cQ in (0, 1):
                for (a2, b2) in PAIRS:
                    for cQ2 in (0, 1):
                        total += 1
                        C = {}
                        for x in PTS5:
                            y = delAt(e, x)
                            C[x] = QF(1, a, b, cQ, y) if x[e] \
                                else QF(0, a2, b2, cQ2, y)
                        fr = failing_rhos(C)
                        if fr:
                            unfix += 1
                            items.append(set(t for t in fr if pins(t) >= 2)
                                         or set(fr))
        hit, rem = greedy_hit(items)
        assert not rem and len(hit) <= 8, (e, len(hit), len(rem))
    print(f"case2: candidates {total} unfixable {unfix} "
          f"(per-e hitting lists of size 8)")

    # ---- CASE 3 ----
    def buildC(s, a0, b0, c0, a1, b1, c1, cv, r):
        C = {}
        for x in PTS5:
            if x[0] == s:
                C[x] = QF(s, a0, b0, c0, delAt(0, x))
            elif x[1] == s:
                C[x] = QF(s, a1, b1, c1, delAt(1, x))
            elif x[2] == s:
                C[x] = cv
            else:
                C[x] = r[(x[3], x[4])]
        return C

    def buildA(s, a1, b1, c1, a2, b2, c2, cv, r):
        A = {}
        for x in PTS5:
            if x[0] == s:
                A[x] = cv
            elif x[1] == s:
                A[x] = PF(s, a1, b1, c1, delAt(1, x))
            elif x[2] == s:
                A[x] = PF(s, a2, b2, c2, delAt(2, x))
            else:
                A[x] = r[(x[3], x[4])]
        return A

    def buildB(s, a0, b0, c0, a2, b2, c2, cv, r):
        B = {}
        for x in PTS5:
            if x[0] == s:
                B[x] = PF(s, a0, b0, c0, delAt(0, x))
            elif x[1] == s:
                B[x] = cv
            elif x[2] == s:
                B[x] = QF(s, a2, b2, c2, delAt(2, x))
            else:
                B[x] = r[(x[3], x[4])]
        return B

    def parts(s, W):
        out = []
        for (fa, fb) in PAIRS:
            for pc in (0, 1):
                for (ga, gb) in PAIRS:
                    for qc in (0, 1):
                        for cv in (0, 1):
                            if W == 'C':
                                v = {QF(s, fa, fb, pc, y) for y in Y4
                                     if y[1] == s}
                                w2 = {QF(s, ga, gb, qc, y) for y in Y4
                                      if y[1] == s}
                                cons = all(
                                    QF(s, fa, fb, pc, delAt(0, x))
                                    == QF(s, ga, gb, qc, delAt(1, x))
                                    for x in PTS5
                                    if x[0] == s and x[1] == s)
                            elif W == 'A':
                                v = {PF(s, fa, fb, pc, y) for y in Y4
                                     if y[0] == s}
                                w2 = {PF(s, ga, gb, qc, y) for y in Y4
                                      if y[0] == s}
                                cons = all(
                                    PF(s, fa, fb, pc, delAt(1, x))
                                    == PF(s, ga, gb, qc, delAt(2, x))
                                    for x in PTS5
                                    if x[1] == s and x[2] == s)
                            else:
                                v = {PF(s, fa, fb, pc, y) for y in Y4
                                     if y[0] == s}
                                w2 = {QF(s, ga, gb, qc, y) for y in Y4
                                      if y[1] == s}
                                cons = all(
                                    PF(s, fa, fb, pc, delAt(0, x))
                                    == QF(s, ga, gb, qc, delAt(2, x))
                                    for x in PTS5
                                    if x[0] == s and x[2] == s)
                            if v != {cv} or w2 != {cv} or not cons:
                                continue
                            out.append((fa, fb, pc, ga, gb, qc, cv))
        return out

    build = {'A': buildA, 'B': buildB, 'C': buildC}
    bad = {}
    for s in (1, 0):
        for W in ('A', 'B', 'C'):
            ps = parts(s, W)
            assert len(ps) == 40, (s, W, len(ps))
            badl = []
            items = []
            for pt in ps:
                for rc in REG:
                    F = build[W](s, *pt, regfn(rc))
                    fr = failing_rhos(F)
                    if not fr:
                        badl.append((pt, rc))
                    else:
                        items.append(set(t for t in fr if pins(t) >= 2)
                                     or set(fr))
            assert len(badl) == 16, (s, W, len(badl))
            hit, rem = greedy_hit(items)
            assert not rem and len(hit) <= 9, (s, W, len(hit))
            bad[(s, W)] = badl

    line = "case3 matched bad triples:"
    for s in (1, 0):
        n = 0
        for (pA, _) in bad[(s, 'A')]:
            for (pB, _) in bad[(s, 'B')]:
                if (pA[3], pA[4]) != (pB[3], pB[4]):
                    continue
                for (pC, _) in bad[(s, 'C')]:
                    if (pC[0], pC[1]) != (pB[0], pB[1]):
                        continue
                    if (pC[3], pC[4]) != (pA[0], pA[1]):
                        continue
                    n += 1
        line += f" sigma={s}: {n} "
    print(line.rstrip())


if __name__ == "__main__":
    main()
