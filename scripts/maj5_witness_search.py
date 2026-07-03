#!/usr/bin/env python3
"""Exhaustive search: can THREE Fixable witnesses + any aggregator compute
strict majority on 5 bits?

Evidence artifact for AttentionLean/WitnessMaj5.lean (Verdict B):
k(maj_5) = 4 — the witness number strictly exceeds the certificate
complexity minCert(maj_5) = 3. The k <= 4 half is machine-checked in Lean;
this script is the k >= 4 half.

Method (complete case analysis; the necessary facts used are formalized in
the repo — Fixable functions are constant on a half-cube, and restrictions
of Fixable functions to half-cubes are Fixable on the 4-cube):

  0. Enumerate the EXACT class Fixable(4) by definition (81 subcubes,
     bitmask tests): 1050 truth tables. Catalog the ordered fixable pairs
     refining T2 (>=2-of-4) and T3 (>=3-of-4): 24 each.
  1. Case 1 — two witnesses share a signed direction: the third's
     restriction must equal +-T2/+-T3, none of which is Fixable. Dead.
  2. Case 2 — two witnesses share a direction with opposite signs: both
     faces force catalog pairs and determine the third witness fully;
     all 24 x 24 x 4 assemblies fail refinement-or-fixability. Dead.
  3. Case 3 — all directions distinct: the triple-overlap square forces a
     uniform sign (self-duality covers the all-zeros sign); faces force
     catalog pairs with slice-constant + overlap-consistency constraints;
     the three-free-coordinate region is enumerated (16^3). All 262,144
     surviving assemblies fail. Dead.

Positive controls: |Fixable(3)| = 96 (the priority-function count) and the
144 two-witness refinements of maj_3 (containing the construction shipped
in WitnessTightness). The script also verifies the shipped 4-witness
construction (refines + all fixable).

Expected output ends with:
  config (b) solutions: 0
  config (c) solutions: 0
  4-witness construction ok: True
"""

from itertools import product


def enum_fixable_tests(n):
    N = 1 << n
    tests = []
    for rho in product((None, 0, 1), repeat=n):
        lits = []
        for i in range(n):
            for b in (0, 1):
                if rho[i] == 1 - b:
                    continue
                m = 0
                for p in range(N):
                    ok = all(r is None or ((p >> j) & 1) == r
                             for j, r in enumerate(rho))
                    if ok and ((p >> i) & 1) == b:
                        m |= 1 << p
                lits.append(m)
        tests.append(lits)
    return tests


def make_isfix(tests):
    def isfix(f):
        for lits in tests:
            ok = False
            for m in lits:
                fm = f & m
                if fm == 0 or fm == m:
                    ok = True
                    break
            if not ok:
                return False
        return True
    return isfix


def weight(p):
    return bin(p).count("1")


def fv(f, p):
    return (f >> p) & 1


def refine(fns, T, npts):
    fib = {}
    for p in range(npts):
        lab = tuple(fv(f, p) for f in fns)
        t = fv(T, p)
        if lab in fib:
            if fib[lab] != t:
                return False
        else:
            fib[lab] = t
    return True


def main():
    isfix3 = make_isfix(enum_fixable_tests(3))
    n3 = sum(1 for f in range(256) if isfix3(f))
    print("|Fixable(3)| =", n3, "(expect 96)")

    isfix4 = make_isfix(enum_fixable_tests(4))
    fix4 = [f for f in range(1 << 16) if isfix4(f)]
    print("|Fixable(4)| =", len(fix4), "(expect 1050)")

    T2 = sum(1 << p for p in range(16) if weight(p) >= 2)
    T3 = sum(1 << p for p in range(16) if weight(p) >= 3)
    for name, T in (("T2", T2), ("T3", T3)):
        print(name, "or complement fixable:",
              isfix4(T) or isfix4(T ^ 0xFFFF), "(expect False; case 1 dead)")

    R2 = [(P, Q) for P in fix4 for Q in fix4 if refine((P, Q), T2, 16)]
    R3 = [(P, Q) for P in fix4 for Q in fix4 if refine((P, Q), T3, 16)]
    print("|R2| =", len(R2), " |R3| =", len(R3), "(expect 24 / 24)")

    MAJ3 = sum(1 << p for p in range(8) if weight(p) >= 2)
    c = sum(1 for P in range(256) if isfix3(P)
            for Q in range(256) if isfix3(Q) and refine((P, Q), MAJ3, 8))
    print("maj3 fixable-pair refinements:", c, "(expect 144; positive control)")

    tests5 = enum_fixable_tests(5)
    isfix5 = make_isfix(tests5)
    MAJ5 = sum(1 << p for p in range(32) if weight(p) >= 3)

    # ---- config (b): axis split ----
    sols_b = 0
    for (P, Q) in R2:
        for (Pp, Qp) in R3:
            for c1 in (0, 1):
                for c2 in (0, 1):
                    w1 = w2 = w3 = 0
                    for p in range(32):
                        x0 = p & 1
                        y = p >> 1
                        v1 = c1 if x0 else fv(Pp, y)
                        v2 = fv(P, y) if x0 else c2
                        v3 = fv(Q, y) if x0 else fv(Qp, y)
                        w1 |= v1 << p
                        w2 |= v2 << p
                        w3 |= v3 << p
                    if refine((w1, w2, w3), MAJ5, 32) and \
                            isfix5(w1) and isfix5(w2) and isfix5(w3):
                        sols_b += 1
    print("config (b) solutions:", sols_b)

    # ---- config (c): three distinct directions, uniform sign ----
    def slice_const(F, bit, val):
        vals = {fv(F, p) for p in range(16) if ((p >> bit) & 1) == val}
        return vals.pop() if len(vals) == 1 else None

    def restrict(F, bit, val):
        out = {}
        rem = [b for b in range(4) if b != bit]
        for p in range(16):
            if ((p >> bit) & 1) == val:
                out[tuple((p >> b) & 1 for b in rem)] = fv(F, p)
        return out

    sols_c = 0
    tried = 0
    for (P0, Q0) in R2:
        c2 = slice_const(P0, 0, 1)
        c3 = slice_const(Q0, 1, 1)
        if c2 is None or c3 is None:
            continue
        for (P1, Q1) in R2:
            c1 = slice_const(P1, 0, 1)
            if c1 is None:
                continue
            if slice_const(Q1, 1, 1) != c3:
                continue
            if restrict(Q0, 0, 1) != restrict(Q1, 0, 1):
                continue
            for (P2, Q2) in R2:
                if slice_const(P2, 0, 1) != c1:
                    continue
                if slice_const(Q2, 1, 1) != c2:
                    continue
                if restrict(P1, 1, 1) != restrict(P2, 1, 1):
                    continue
                if restrict(P0, 1, 1) != restrict(Q2, 0, 1):
                    continue
                r1a = restrict(P1, 0, 0)
                r1b = restrict(P2, 0, 0)
                r2a = restrict(P0, 0, 0)
                r2b = restrict(Q2, 1, 0)
                r3a = restrict(Q0, 1, 0)
                r3b = restrict(Q1, 1, 0)
                for f1 in range(16):
                    for f2 in range(16):
                        for f3 in range(16):
                            tried += 1
                            w1 = w2 = w3 = 0
                            for p in range(32):
                                x0, x1, x2, x3, x4 = [(p >> j) & 1
                                                      for j in range(5)]
                                if x0:
                                    v1 = c1
                                elif x1:
                                    v1 = r1a[(x2, x3, x4)]
                                elif x2:
                                    v1 = r1b[(x1, x3, x4)]
                                else:
                                    v1 = (f1 >> (x3 + 2 * x4)) & 1
                                if x1:
                                    v2 = c2
                                elif x0:
                                    v2 = r2a[(x2, x3, x4)]
                                elif x2:
                                    v2 = r2b[(x0, x3, x4)]
                                else:
                                    v2 = (f2 >> (x3 + 2 * x4)) & 1
                                if x2:
                                    v3 = c3
                                elif x0:
                                    v3 = r3a[(x1, x3, x4)]
                                elif x1:
                                    v3 = r3b[(x0, x3, x4)]
                                else:
                                    v3 = (f3 >> (x3 + 2 * x4)) & 1
                                w1 |= v1 << p
                                w2 |= v2 << p
                                w3 |= v3 << p
                            if refine((w1, w2, w3), MAJ5, 32) and \
                                    isfix5(w1) and isfix5(w2) and isfix5(w3):
                                sols_c += 1
    print("config (c) assemblies tried:", tried, "solutions:", sols_c)

    # ---- verify the shipped 4-witness construction ----
    def A(a, b, c, d):
        return a or c or (b and d)

    def B(a, b, c, d):
        return b or d or (a and c)

    def Cp(a, b, c, d):
        return a and c and (b or d)

    def Dp(a, b, c, d):
        return b and d and (a or c)

    ws = [0, 0, 0, 0]
    for p in range(32):
        x0, x1, x2, x3, x4 = [(p >> j) & 1 for j in range(5)]
        vals = [x0 and A(x1, x2, x3, x4), x0 and B(x1, x2, x3, x4),
                (not x0) and Cp(x1, x2, x3, x4),
                (not x0) and Dp(x1, x2, x3, x4)]
        for i, v in enumerate(vals):
            ws[i] |= int(bool(v)) << p
    ok = refine(tuple(ws), MAJ5, 32) and all(isfix5(w) for w in ws)
    print("4-witness construction ok:", ok)


if __name__ == "__main__":
    main()
