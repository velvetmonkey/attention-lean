#!/usr/bin/env python3
"""Exhaustive search: can FIVE Fixable witnesses + any aggregator compute
strict majority on 7 bits?

Evidence artifact for the open endpoint of AttentionLean/WitnessMaj7Lower.lean:
k(maj_7) is bracketed [5, 6] (maj7_head_bracket_tight); this script decides
which endpoint is the truth at the level of an exhaustive machine search.
Repo discipline: the script corroborates, the kernel proves.  A positive
answer (a 5-witness construction) is formalized by a 128-point kernel
`decide`; a negative answer leaves the Lean bracket unchanged unless the
case analysis compresses to kernel scale.

Method (search-first, mirroring scripts/maj5_witness_search.py one
dimension up):

  0. POSITIVE CONTROLS (hard gate): |Fixable(n)| for n <= 6 by recursive
     generation, cross-validated against the subcube definition at n <= 4;
     catalog counts |R2| = |R3| = 24 and the 144 maj_3 pair refinements
     from the maj5 script; the shipped maj5 4-witness and maj7 6-witness
     constructions verify; the engine re-derives the known UNSAT facts.
  1. KILL LADDER (base facts machine-checked exhaustively at the 5-cube):
       (T2of5, k<=2) UNSAT,  (maj5, k<=2) UNSAT   [two independent methods]
       (maj5, 3) UNSAT       [shipped maj5_witness_search.py + Lean theorem
                              maj5_no_three_fixable_witnesses]
     From these, by the sound NECESSITY direction of face restriction
     (a fixable witness is constant on a half-cube; on that half-cube the
     remaining witnesses' restrictions must refine the pinned target, and
     restrictions of fixable functions are fixable):
       K2: (T3of6, 3) UNSAT and dually (T4of6, 3) UNSAT.
       K3: any (T3of6, 4) solution has four nonconstant members with
           distinct POSITIVE constancy directions and no negative-face
           constancy (member constant on a negative face -> other three
           restrict to a (maj5, 3) solution; two members sharing a face ->
           other two restrict to a (T2of5, 2) solution).
       K4 (sign collapse): up to the maj7 self-duality, every 5-witness
           solution for maj7 has five nonconstant witnesses with five
           DISTINCT positive constancy directions (WLOG x0..x4), i.e.
           w_i = (x_i ? c_i : g_i) with g_i Fixable on the other 6 bits,
           no witness constant on any negative face or on another
           witness's designated face.
     NOTE the one-sidedness: pinning is used ONLY to kill configurations
     and to GENERATE candidates.  Global refinement over all 128 points is
     re-checked for every assembled candidate (fibers straddle half-cubes;
     face-wise refinement does not compose).
  2. CONSTRUCTIVE PRE-PASS: seeded annealing directly inside the collapsed
     configuration.  A hit is a k(maj7) = 5 witness, checked exactly.
  3. CORE (staged join inside the collapsed configuration):
       C3 = all (T2of5, 3) triples with the inherited top-positive shape:
            EXHAUSTIVELY ENUMERATED, |C3| = 543,528.
       C4 = all (T3of6, 4) solutions (K3 shape), built from C3 by fiber
            lifting + anchor completion + GLOBAL 64-point verification:
            EXHAUSTIVELY ENUMERATED via --stage c4count,
            |C4| = 51,812,352 exactly (559,447,512 lift combos,
            106 min at 7 workers).
       top = all 5-tuples from C4 by one more fiber lift + completion +
            GLOBAL 128-point verification: measured at ~3.41e4
            completions per C4 tuple (~0.5 ms each), ~1.8e12 in total
            ~ 29 CPU-years — OUT OF REACH for this architecture.
            NOT RUN in full.
     VERDICT: INCOMPLETE.  The script never claims a refutation it did
     not compute.  What IS decided (script-level, exhaustively): no
     5-witness solution exists outside the collapsed configuration
     (kill ladder), and none whose four non-anchor witnesses restrict on
     the anchor face outside C4.  The sign-purity slice of the kill
     ladder (mixed-sign families are impossible) is KERNEL-PROVED in
     AttentionLean/WitnessMaj7SignPurity.lean (maj_witness_descent_pair,
     maj7_no_mixed_sign_pair, maj7_no_shared_face_pair,
     maj7_no_opposite_pair_same_direction, maj7_five_witness_sign_purity),
     from maj5_no_three_fixable_witnesses via balanced double pins.

Fixable(n) counts (recursive generation, cross-checked at n <= 4 against
the 3^n-subcube definition): 2, 4, 14, 96, 1050, 15036, 260134, 5253912.

Honesty notes:
  * T1of4 (= x OR y OR z OR w) IS fixable, so at the 4-cube level single
    witnesses can refine pinned targets; the C3 layer is therefore
    enumerated DIRECTLY (no deeper recursion, no pruning that would need a
    kill unavailable at that level).
  * All catalog pools are SUPERSETS of the necessary forms (safe for a
    refutation; positives are verified exactly).
  * The RNG is used only in the pre-pass (stage 2) and is fixed-seeded;
    stages 0-1 and 3 are deterministic.

Usage:
  python3 scripts/maj7_witness_search.py            # controls+ladder+prepass+core
  python3 scripts/maj7_witness_search.py --stage controls|ladder|prepass|core
  python3 scripts/maj7_witness_search.py --stage c4count   # exact |C4| (hours)
  python3 scripts/maj7_witness_search.py --stage top --force-top --jobs N
      # the full 5-tuple join: INFEASIBLE at current scale, gated
"""

import argparse
import json
import os
import random
import subprocess
import sys
import time
from itertools import combinations, permutations, product

# ---------------------------------------------------------------------------
# SECTION A: bit-table infrastructure
#
# A function on n bits is a (1 << (1 << n))-range integer: bit p is the value
# at the point whose i-th input bit is (p >> i) & 1.
# ---------------------------------------------------------------------------


def fv(f, p):
    return (f >> p) & 1


def weight(p):
    return p.bit_count()


def full_table(n):
    return (1 << (1 << n)) - 1


def tk(k, n):
    """Threshold >= k of n as a truth table."""
    return sum(1 << p for p in range(1 << n) if weight(p) >= k)


def extract(f, n, i, b):
    """Restrict the n-var table f to x_i = b: an (n-1)-var table over the
    remaining variables in order."""
    w = 1 << i
    mask = (1 << w) - 1
    g = 0
    for hi in range(1 << (n - 1 - i)):
        g |= ((f >> ((hi << (i + 1)) | (b << i))) & mask) << (hi * w)
    return g


def insert_top(g, n, i, b, c):
    """The n-var table equal to the constant c on {x_i = b} and to the
    (n-1)-var table g on {x_i = 1-b}."""
    w = 1 << i
    mask = (1 << w) - 1
    cchunk = mask if c else 0
    f = 0
    for hi in range(1 << (n - 1 - i)):
        f |= cchunk << ((hi << (i + 1)) | (b << i))
        f |= ((g >> (hi * w)) & mask) << ((hi << (i + 1)) | ((1 - b) << i))
    return f


def table_const(f, n):
    return f == 0 or f == full_table(n)


def dual(f, n):
    """Input-and-output complement: dual(f)(x) = 1 - f(~x)."""
    npts = 1 << n
    g = 0
    for p in range(npts):
        g |= (1 - fv(f, (npts - 1) ^ p)) << p
    return g


def apply_perm(f, n, sigma):
    """Coordinate permutation: result(x) = f(x o sigma) via point remap
    p -> sum_i p_i << sigma[i]."""
    g = 0
    for p in range(1 << n):
        pp = 0
        for i in range(n):
            if (p >> i) & 1:
                pp |= 1 << sigma[i]
        g |= fv(f, p) << pp
    return g


def _selfcheck_bit_ops():
    """Randomized cross-check of extract/insert_top/dual against pointwise
    reference implementations.  Aborts on any mismatch."""
    rng = random.Random(20260710)

    def extract_ref(f, n, i, b):
        g = 0
        for q in range(1 << (n - 1)):
            low = q & ((1 << i) - 1)
            p = low | (b << i) | ((q >> i) << (i + 1))
            g |= fv(f, p) << q
        return g

    def insert_ref(g, n, i, b, c):
        f = 0
        for p in range(1 << n):
            if ((p >> i) & 1) == b:
                v = c
            else:
                low = p & ((1 << i) - 1)
                q = low | ((p >> (i + 1)) << i)
                v = fv(g, q)
            f |= v << p
        return f

    for _ in range(200):
        n = rng.randint(2, 7)
        f = rng.getrandbits(1 << n)
        g = rng.getrandbits(1 << (n - 1))
        i = rng.randrange(n)
        b = rng.randint(0, 1)
        c = rng.randint(0, 1)
        assert extract(f, n, i, b) == extract_ref(f, n, i, b)
        assert insert_top(g, n, i, b, c) == insert_ref(g, n, i, b, c)
        assert extract(insert_top(g, n, i, b, c), n, i, 1 - b) == g
        assert dual(dual(f, n), n) == f
    # dual maps thresholds correctly: dual(Tk/n) = T(n+1-k)/n
    for n in range(2, 7):
        for k in range(1, n + 1):
            assert dual(tk(k, n), n) == tk(n + 1 - k, n)
    # sanity: permutations act on points, identity fixed
    f = rng.getrandbits(1 << 5)
    assert apply_perm(f, 5, list(range(5))) == f


# ---------------------------------------------------------------------------
# SECTION B: fixability, refinement
# ---------------------------------------------------------------------------


def enum_fixable_tests(n):
    """All 3^n subcubes, each with its list of non-excluded literal masks
    (verbatim semantics of scripts/maj5_witness_search.py)."""
    npts = 1 << n
    tests = []
    for rho in product((None, 0, 1), repeat=n):
        lits = []
        for i in range(n):
            for b in (0, 1):
                if rho[i] == 1 - b:
                    continue
                m = 0
                for p in range(npts):
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


def gen_fixable(nmax):
    """Fixable(n) for n = 0..nmax by the recursive characterization:
    f is fixable iff f is constant or f = (x_i = b ? c : g) with g fixable
    on the remaining variables.  Returns a list indexed by n of sorted
    lists of truth tables."""
    layers = [[0, 1]]
    for n in range(1, nmax + 1):
        out = {0, full_table(n)}
        for g in layers[n - 1]:
            for i in range(n):
                for b in (0, 1):
                    for c in (0, 1):
                        out.add(insert_top(g, n, i, b, c))
        layers.append(sorted(out))
    return layers


def refine(fns, T, npts):
    """maj-computability: T constant on every fiber of the signature map
    (verbatim semantics of scripts/maj5_witness_search.py)."""
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


def mixed_pairs(T, n):
    npts = 1 << n
    zeros = [p for p in range(npts) if not fv(T, p)]
    ones = [p for p in range(npts) if fv(T, p)]
    return [(p, q) for p in zeros for q in ones]


def sepmask(f, pairs):
    m = 0
    for idx, (p, q) in enumerate(pairs):
        if fv(f, p) != fv(f, q):
            m |= 1 << idx
    return m


def neg_face_constancies(f, n):
    """Directions i with f constant on {x_i = 0}."""
    return [i for i in range(n) if table_const(extract(f, n, i, 0), n - 1)]


def pos_face_constancies(f, n):
    return [i for i in range(n) if table_const(extract(f, n, i, 1), n - 1)]


# ---------------------------------------------------------------------------
# SECTION C: stage 0 — positive controls (hard gate)
# ---------------------------------------------------------------------------


def stage_controls(fix, big=False):
    t0 = time.time()
    ok = True

    def check(name, got, expect):
        nonlocal ok
        good = got == expect
        ok = ok and good
        print(f"  control {name}: {got} (expect {expect})"
              f"{'' if good else '  *** MISMATCH ***'}")

    counts = [len(layer) for layer in fix]
    for n, expect in enumerate([2, 4, 14, 96, 1050, 15036, 260134][:len(counts)]):
        check(f"|Fixable({n})| (recursive)", counts[n], expect)

    # cross-validate recursion == subcube definition, exhaustively at n <= 4
    for n in (3, 4):
        isfix = make_isfix(enum_fixable_tests(n))
        subcube = {f for f in range(1 << (1 << n)) if isfix(f)}
        check(f"Fixable({n}) recursion == subcube-definition set",
              set(fix[n]) == subcube, True)

    # soundness spot-check at n = 5: every generated table passes the
    # subcube definition
    isfix5 = make_isfix(enum_fixable_tests(5))
    check("Fixable(5) generated tables all pass subcube definition",
          all(isfix5(f) for f in fix[5]), True)

    # catalog counts from the maj5 script
    T2of4, T3of4 = tk(2, 4), tk(3, 4)
    fix4 = fix[4]
    r2 = sum(1 for P in fix4 for Q in fix4 if refine((P, Q), T2of4, 16))
    r3 = sum(1 for P in fix4 for Q in fix4 if refine((P, Q), T3of4, 16))
    check("|R2| (T2of4 fixable pair refinements)", r2, 24)
    check("|R3| (T3of4 fixable pair refinements)", r3, 24)
    maj3 = tk(2, 3)
    c144 = sum(1 for P in fix[3] for Q in fix[3] if refine((P, Q), maj3, 8))
    check("maj3 fixable-pair refinements", c144, 144)

    # shipped maj5 4-witness construction (WitnessMaj5.lean)
    maj5 = tk(3, 5)
    ws = [0, 0, 0, 0]
    for p in range(32):
        x = [(p >> j) & 1 for j in range(5)]
        vals = [x[0] and (x[1] or x[3] or (x[2] and x[4])),
                x[0] and (x[2] or x[4] or (x[1] and x[3])),
                (not x[0]) and (x[1] and x[3] and (x[2] or x[4])),
                (not x[0]) and (x[2] and x[4] and (x[1] or x[3]))]
        for i, v in enumerate(vals):
            ws[i] |= int(bool(v)) << p
    check("maj5 4-witness construction refines + fixable",
          refine(tuple(ws), maj5, 32) and all(w in set(fix[5]) for w in ws)
          and all(isfix5(w) for w in ws), True)

    # shipped maj7 6-witness construction (WitnessMaj7Bracket.lean:19-44)
    maj7 = tk(4, 7)
    w6 = [0] * 6
    for p in range(128):
        x = [(p >> j) & 1 for j in range(7)]
        vals = [x[0],
                x[1],
                (not x[6]) or ((not x[2]) and (not x[3]) and (not x[4])),
                x[5] and (x[2] or x[3] or x[4] or x[6]),
                x[4] and (x[2] or x[3]),
                x[3] and (x[2] or (x[4] and x[5] and x[6]))]
        for i, v in enumerate(vals):
            w6[i] |= int(bool(v)) << p
    isfix7 = make_isfix(enum_fixable_tests(7))
    check("maj7 6-witness construction refines maj7",
          refine(tuple(w6), maj7, 128), True)
    check("maj7 6-witness construction all fixable (subcube definition)",
          all(isfix7(w) for w in w6), True)
    # its restrictions to {x0=1} refine T3of6, and no 4-subset of the six
    # witnesses refines maj7 on its own
    T3of6 = tk(3, 6)
    restr = [extract(w, 7, 0, 1) for w in w6[1:]]
    check("6-witness restrictions to {x0=1} refine T3of6",
          refine(tuple(restr), T3of6, 64), True)
    any4 = any(refine(sub, maj7, 128) for sub in combinations(w6, 4))
    check("some 4-subset of the 6 witnesses refines maj7", any4, False)

    if big:
        t = time.time()
        n7 = {0, full_table(7)}
        for g in fix[6]:
            for i in range(7):
                for b in (0, 1):
                    for c in (0, 1):
                        n7.add(insert_top(g, 7, i, b, c))
        check("|Fixable(7)| (recursive)", len(n7), 5253912)
        print(f"    (|Fixable(7)| computed in {time.time() - t:.0f}s)")
        del n7

    print(f"  stage controls: {'PASS' if ok else 'FAIL'} "
          f"({time.time() - t0:.0f}s)")
    return ok


# ---------------------------------------------------------------------------
# SECTION D: stage 1 — kill-ladder base facts, machine-checked at the 5-cube
# ---------------------------------------------------------------------------


def solve_two_witnesses_repscan(T, n, funcs, group_perms):
    """Method A for (T, 2) on n vars: canonicalize the first witness up to
    the symmetry group of T, then scan all partners.  Returns
    (solution-or-None, orbit-rep count).  Exhaustive: refinement is
    invariant under simultaneous relabeling, so a solution (f, g) yields
    one with f canonical."""
    pairs = mixed_pairs(T, n)
    fullmask = (1 << len(pairs)) - 1
    point_maps = []
    for sigma in group_perms:
        pm = []
        for p in range(1 << n):
            pp = 0
            for i in range(n):
                if (p >> i) & 1:
                    pp |= 1 << sigma[i]
            pm.append(pp)
        point_maps.append(pm)

    def canon(f):
        best = None
        for pm in point_maps:
            g = 0
            for p in range(1 << n):
                g |= fv(f, p) << pm[p]
            if best is None or g < best:
                best = g
        return best

    reps = sorted({canon(f) for f in funcs})
    sepl = [(sepmask(g, pairs), g) for g in funcs]
    for f in reps:
        req = fullmask & ~sepmask(f, pairs)
        if req == 0:
            return (f, f), len(reps)
        for sg, g in sepl:
            if sg & req == req:
                return (f, g), len(reps)
    return None, len(reps)


def solve_two_witnesses_anchor(T, n, funcs):
    """Method B for (T, 2): anchor on the least-covered mixed pair; the
    first witness (WLOG, up to order) covers it.  Returns a solution or
    None.  Independent of method A (no symmetry argument)."""
    pairs = mixed_pairs(T, n)
    fullmask = (1 << len(pairs)) - 1
    seps = [(sepmask(f, pairs), f) for f in funcs]
    cover_counts = [0] * len(pairs)
    for s, _ in seps:
        m = s
        while m:
            low = m & -m
            cover_counts[low.bit_length() - 1] += 1
            m ^= low
    anchor = min(range(len(pairs)), key=lambda i: cover_counts[i])
    abit = 1 << anchor
    for s1, f1 in seps:
        if not (s1 & abit):
            continue
        req = fullmask & ~s1
        if req == 0:
            return (f1, f1)
        for s2, f2 in seps:
            if s2 & req == req:
                return (f1, f2)
    return None


def stage_ladder(fix, repo_root):
    t0 = time.time()
    ok = True

    def check(name, got, expect):
        nonlocal ok
        good = got == expect
        ok = ok and good
        print(f"  ladder {name}: {got} (expect {expect})"
              f"{'' if good else '  *** MISMATCH ***'}")

    isfix5 = make_isfix(enum_fixable_tests(5))
    isfix6 = make_isfix(enum_fixable_tests(6))

    # K0: fixability of the pinned targets themselves
    maj5, T2of5, T4of5 = tk(3, 5), tk(2, 5), tk(4, 5)
    T3of6, T4of6 = tk(3, 6), tk(4, 6)
    T1of4 = tk(1, 4)
    isfix4 = make_isfix(enum_fixable_tests(4))
    check("maj5 or complement fixable", isfix5(maj5) or isfix5(maj5 ^ full_table(5)), False)
    check("T2of5 or complement fixable", isfix5(T2of5) or isfix5(T2of5 ^ full_table(5)), False)
    check("T4of5 or complement fixable", isfix5(T4of5) or isfix5(T4of5 ^ full_table(5)), False)
    check("T3of6 fixable", isfix6(T3of6), False)
    check("T4of6 fixable", isfix6(T4of6), False)
    # honesty note: T1of4 = OR is a decision list, hence fixable — this is
    # why no negative-face pruning is applied at the C3 (5-cube) layer
    check("T1of4 (= 4-bit OR) fixable", isfix4(T1of4), True)

    # K1 single-witness facts: one fixable witness refines T iff T is
    # constant or T in {w, not w}; T nonconstant and (with complement)
    # unfixable settles it — recorded via the K0 line above.
    f5set = set(fix[5])
    for name, T in (("maj5", maj5), ("T2of5", T2of5)):
        check(f"({name}, 1) has a solution",
              T in f5set or (T ^ full_table(5)) in f5set, False)

    # K1 two-witness facts, two independent methods
    s5perms = list(permutations(range(5)))
    for name, T in (("maj5", maj5), ("T2of5", T2of5)):
        resA, nreps = solve_two_witnesses_repscan(T, 5, fix[5], s5perms)
        if resA is None:
            print(f"    ({name}, 2) method A: UNSAT over {nreps} "
                  f"S5-orbit reps x {len(fix[5])} partners")
        resB = solve_two_witnesses_anchor(T, 5, fix[5])
        check(f"({name}, 2) method A (orbit-rep scan)", resA, None)
        check(f"({name}, 2) method B (anchor branching)", resB, None)

    # (maj5, 3) UNSAT: the shipped exhaustive case analysis (13s), plus the
    # Lean kernel theorem maj5_no_three_fixable_witnesses
    script = os.path.join(repo_root, "scripts", "maj5_witness_search.py")
    res = subprocess.run([sys.executable, script], capture_output=True,
                         text=True, timeout=600)
    out = res.stdout
    good = ("config (b) solutions: 0" in out
            and "solutions: 0" in out.split("config (c)")[-1]
            and "4-witness construction ok: True" in out
            and res.returncode == 0)
    check("(maj5, 3) UNSAT via shipped maj5_witness_search.py", good, True)

    print("""  derived (necessity of face restriction; each base fact above):
    K2: (T3of6, 3) UNSAT   [witness constant on {x_d=1} -> (T2of5, 2);
                            on {x_d=0} -> (maj5, 2); constant witness ->
                            (T3of6, 2) -> (T2of5,1)/(maj5,1); all UNSAT]
        dually (T4of6, 3) UNSAT.
    K3: (T3of6, 4) members: nonconstant [else K2], no negative-face
        constancy [else (maj5, 3)], pairwise distinct positive faces
        [else (T2of5, 2)].  Dually for (T4of6, 4).
    K4: (maj7, 5): witnesses nonconstant + pairwise distinct partitions
        [else (maj7, 4), UNSAT: face restriction gives (T3of6, 3) or
        (T4of6, 3) = K2].  Mixed signs die: pos face {x_d=1} + neg face
        {x_e=0}, d != e -> restrict to {x_d=1}: a (T3of6, 4) member is
        constant on a negative 6-face, contradicting K3.  Same-direction
        opposite signs and dictators die the same way (any third witness
        violates K3 on one of the two faces).  Up to duality: five
        distinct positive directions, WLOG x0..x4.""")

    print(f"  stage ladder: {'PASS' if ok else 'FAIL'} "
          f"({time.time() - t0:.0f}s)")
    return ok


# ---------------------------------------------------------------------------
# SECTION E: the collapsed configuration
#
# w_i = (x_i ? c_i : g_i), i = 0..4, g_i in Fixable(6) over the other six
# coordinates, c_i in {0,1}; no witness constant on any negative face or on
# another witness's designated positive face (spare positive faces x5, x6
# are permitted).  Up to relabeling + duality this covers every candidate.
# ---------------------------------------------------------------------------

MAJ7 = tk(4, 7)
T3OF6 = tk(3, 6)
T2OF5 = tk(2, 5)


def witness_ok_level7(w, slot):
    """Necessary conditions on a full 7-var witness in the collapsed form
    (slot = its designated direction in 0..4)."""
    if table_const(w, 7):
        return False
    if neg_face_constancies(w, 7):
        return False
    for j in range(5):
        if j != slot and table_const(extract(w, 7, j, 1), 6):
            return False
    return True


def member_ok_level6(m, slot):
    """Necessary conditions on a 6-var member of a (T3of6, 4) solution in
    K3 shape (slot = designated direction in 0..3; vars 4,5 spare)."""
    if table_const(m, 6):
        return False
    if neg_face_constancies(m, 6):
        return False
    for j in range(4):
        if j != slot and table_const(extract(m, 6, j, 1), 5):
            return False
    return True


def assemble5(cs, gs):
    """Build the five 7-var witnesses from (c_i, g_i)."""
    return tuple(insert_top(gs[i], 7, i, 1, cs[i]) for i in range(5))


def check_candidate(ws, isfix7=None):
    """Global verification of a candidate 5-tuple: refinement over all 128
    points; optionally the subcube fixability definition per witness."""
    if not refine(ws, MAJ7, 128):
        return False
    if isfix7 is not None and not all(isfix7(w) for w in ws):
        return False
    return True


# ---------------------------------------------------------------------------
# SECTION F: stage 2 — constructive pre-pass (seeded annealing)
# ---------------------------------------------------------------------------


def prepass(fix, seconds=600, seed=20260710):
    """Bounded search FOR a 5-witness construction inside the collapsed
    configuration.  Score = number of points in violating fibers.  A hit is
    verified exactly and returned; failure carries no logical weight."""
    rng = random.Random(seed)
    f6 = fix[6]
    t0 = time.time()
    best_overall = None
    restarts = 0
    evals = 0

    def score(ws):
        fib = {}
        for p in range(128):
            lab = tuple(fv(w, p) for w in ws)
            fib.setdefault(lab, [0, 0])[fv(MAJ7, p)] += 1
        return sum(min(a, b) for a, b in fib.values())

    while time.time() - t0 < seconds:
        restarts += 1
        cs = [rng.randint(0, 1) for _ in range(5)]
        gs = [f6[rng.randrange(len(f6))] for _ in range(5)]
        cur = score(assemble5(cs, gs))
        stale = 0
        while stale < 400 and time.time() - t0 < seconds:
            slot = rng.randrange(5)
            oldg, oldc = gs[slot], cs[slot]
            if rng.random() < 0.1:
                cs[slot] ^= 1
            gs[slot] = f6[rng.randrange(len(f6))]
            s = score(assemble5(cs, gs))
            evals += 1
            if s <= cur:
                if s < cur:
                    stale = 0
                cur = s
                if cur == 0:
                    ws = assemble5(cs, gs)
                    if check_candidate(ws, make_isfix(enum_fixable_tests(7))):
                        print(f"  prepass HIT after {restarts} restarts, "
                              f"{evals} evals: cs={cs} "
                              f"gs={[hex(g) for g in gs]}")
                        return ws
            else:
                gs[slot], cs[slot] = oldg, oldc
                stale += 1
        if best_overall is None or cur < best_overall:
            best_overall = cur
            print(f"    prepass best score so far: {cur} "
                  f"(restart {restarts}, {evals} evals, "
                  f"{time.time() - t0:.0f}s)")
    print(f"  prepass: no construction found ({restarts} restarts, "
          f"{evals} evals, {seconds}s budget) — no logical weight")
    return None


# ---------------------------------------------------------------------------
# SECTION G: stage 3 — the exhaustive core (C3 -> C4 -> top join)
# ---------------------------------------------------------------------------


def build_c3(fix):
    """All ordered triples (u0, u1, u2) of 5-var functions in inherited
    top-positive shape u_j = (v_j ? a_j : e_j), e_j in Fixable(4) over the
    other four variables, u_j nonconstant, refining T2of5 globally.

    These are exactly the possible restrictions to the C4 anchor face of
    the three non-anchor C4 members ((T2of5, 2) UNSAT forces all three
    restrictions nonconstant; the top-positive shape is inherited from the
    K3 shape one level up).  No other pruning is applied at this level
    (T1of4 is fixable, so K3-style kills are NOT available here)."""
    t0 = time.time()
    pairs = mixed_pairs(T2OF5, 5)
    fullmask = (1 << len(pairs)) - 1
    pools = []
    for slot in range(3):
        pool = []
        for e in fix[4]:
            for a in (0, 1):
                u = insert_top(e, 5, slot, 1, a)
                if table_const(u, 5):
                    continue
                pool.append((u, sepmask(u, pairs)))
        pools.append(pool)
    print(f"    C3 pools: {[len(p) for p in pools]} "
          f"({len(pairs)} mixed pairs)")

    # per-pair coverer lists for the last slot: at depth 2 branch on the
    # least-covered still-required pair and scan only its coverers
    npairs = len(pairs)
    coverers = [[] for _ in range(npairs)]
    for u, s in pools[2]:
        m = s
        while m:
            low = m & -m
            coverers[low.bit_length() - 1].append((u, s))
            m ^= low
    order = sorted(range(npairs), key=lambda i: len(coverers[i]))

    triples = []
    for u0, s0 in pools[0]:
        r0 = fullmask & ~s0
        for u1, s1 in pools[1]:
            req = r0 & ~s1
            if req == 0:
                # any nonconstant pool member completes the triple
                for u2, s2 in pools[2]:
                    triples.append((u0, u1, u2))
                continue
            pick = next(i for i in order if (req >> i) & 1)
            for u2, s2 in coverers[pick]:
                if s2 & req == req and refine((u0, u1, u2), T2OF5, 32):
                    triples.append((u0, u1, u2))
    print(f"    |C3| = {len(triples)} ordered triples "
          f"({time.time() - t0:.0f}s)", flush=True)
    return triples


def _fiber_index(funcs, n):
    """Index of the restriction-to-{var0=1} map: 5-var (resp. (n-1)-var)
    table -> list of n-var tables in funcs restricting to it."""
    idx = {}
    for f in funcs:
        idx.setdefault(extract(f, n, 0, 1), []).append(f)
    return idx


def _forced_masks(partial_ws, T, n):
    """Mixed signature classes of the all-but-anchor tuple: on each fiber
    of the partial signature map that is mixed for T, the anchor witness
    must separate the T-zeros from the T-ones (its value on the class is
    determined by T up to one flip bit per class — see complete_anchor).
    Returns the list of mixed classes as (zeros_mask, ones_mask).
    Vectorized: classes are built by whole-table AND splits."""
    fullmask = full_table(n)
    classes = [fullmask]
    for w in partial_ws:
        nxt = []
        for c in classes:
            a = c & w
            if a:
                nxt.append(a)
            b = c & ~w & fullmask
            if b:
                nxt.append(b)
        classes = nxt
    out = []
    for c in classes:
        o = c & T
        z = c & ~T & fullmask
        if z and o:
            out.append((z, o))
    return out


def refine_fast(ws, T, n):
    """refine() via whole-table splits (identical semantics, hot path)."""
    return not _forced_masks(ws, T, n)


def complete_anchor(mixed, n, anchor_var, pool_index, face_mask, cap=4096):
    """Enumerate anchor candidates w = (x_{anchor_var} ? c : g) whose value
    separates zeros from ones on every mixed class.  For each class the
    anchor is T-aligned or anti-aligned (one flip bit); each choice forces
    point values, split between the constant face and g.  pool_index maps
    a forced-(A, B) query on the g-half to candidate g tables.

    Exact and exhaustive: the forced conditions are necessary and
    sufficient for w to separate all residual mixed pairs; every returned
    candidate is subsequently verified globally anyway."""
    face_bit = anchor_var
    # the anchor is constant on its designated face, so a mixed class with
    # both zeros and ones ON the face can never be separated: dead, no scan
    for (z, o) in mixed:
        if (z & face_mask) and (o & face_mask):
            return []
    if len(mixed) > 12:
        return None  # caller falls back to a scan
    out = []
    for flips in range(1 << len(mixed)):
        # accumulate forced ones (A) / zeros (B) over the n-cube
        A = B = 0
        for ci, (z, o) in enumerate(mixed):
            if (flips >> ci) & 1:
                A |= z
                B |= o
            else:
                A |= o
                B |= z
        # split by the anchor face
        cA = cB = False
        gA = gB = 0
        for p in _iter_bits(A):
            if (p >> face_bit) & 1:
                cA = True
            else:
                gA |= 1 << _drop_bit(p, face_bit)
        for p in _iter_bits(B):
            if (p >> face_bit) & 1:
                cB = True
            else:
                gB |= 1 << _drop_bit(p, face_bit)
        if cA and cB:
            continue
        cvals = (1,) if cA else (0,) if cB else (0, 1)
        for g in pool_index(gA, gB):
            for c in cvals:
                out.append(insert_top(g, n, face_bit, 1, c))
        if len(out) > cap:
            return None
    return out


def _iter_bits(m):
    while m:
        low = m & -m
        yield low.bit_length() - 1
        m ^= low


def _drop_bit(p, i):
    return (p & ((1 << i) - 1)) | ((p >> (i + 1)) << i)


def make_pool_query(funcs):
    """Forced-mask query over a sorted list of tables: all f with
    A subset f and B disjoint from f."""
    def query(A, B):
        return [f for f in funcs if (f & A) == A and (f & B) == 0]
    return query


class BitTrie:
    """Binary trie over fixed-width bit tables supporting forced-bit
    enumeration: all stored tables f with A subset f and B disjoint f.
    Backed by array('i') so forked workers share pages copy-on-write."""

    def __init__(self, funcs, width):
        from array import array
        self.width = width
        c0 = [-1]
        c1 = [-1]
        for f in funcs:
            node = 0
            for d in range(width):
                kids = c1 if (f >> d) & 1 else c0
                nxt = kids[node]
                if nxt == -1:
                    nxt = len(c0)
                    c0.append(-1)
                    c1.append(-1)
                    kids[node] = nxt
                node = nxt
        self.c0 = array('i', c0)
        self.c1 = array('i', c1)

    def enum(self, A, B, cap):
        """Enumerate matching tables; returns None if more than cap."""
        out = []
        c0, c1, width = self.c0, self.c1, self.width
        stack = [(0, 0, 0)]  # node, depth, value
        while stack:
            node, d, val = stack.pop()
            if d == width:
                out.append(val)
                if len(out) > cap:
                    return None
                continue
            bit_forced_1 = (A >> d) & 1
            bit_forced_0 = (B >> d) & 1
            if not bit_forced_1 and c0[node] != -1:
                stack.append((c0[node], d + 1, val))
            if not bit_forced_0 and c1[node] != -1:
                stack.append((c1[node], d + 1, val | (1 << d)))
        return out


def complete_anchor_trie(mixed, n, trie, face_mask, cap=200000):
    """Anchor completion via the below-face trie.  The anchor
    w = (x_0 ? a : g) must, on every mixed class, put all T-ones on one
    value and all T-zeros on the other.  Face points force a; off-face
    points force bits of g; classes with no face points contribute one
    free flip each.  Returns a list of (a, g) pairs (exhaustive), or None
    if the trie enumeration exceeds cap (caller falls back to a scan)."""
    # global dead check (independent of a): a class with T-zeros and
    # T-ones both on the constant face can never be separated
    split = []
    for (z, o) in mixed:
        zf = z & face_mask
        of = o & face_mask
        if zf and of:
            return []
        z_off = extract(z & ~face_mask, n, 0, 0)
        o_off = extract(o & ~face_mask, n, 0, 0)
        split.append((bool(zf), bool(of), z_off, o_off))
    out = []
    for a in (0, 1):
        A = B = 0
        free = []
        ok = True
        for (zf, of, z_off, o_off) in split:
            if zf:      # z-side value = a, o-side = 1-a
                onmask, offmask = (o_off, z_off) if a == 0 else (z_off, o_off)
            elif of:    # o-side value = a, z-side = 1-a
                onmask, offmask = (z_off, o_off) if a == 0 else (o_off, z_off)
            else:
                free.append((z_off, o_off))
                continue
            A |= onmask
            B |= offmask
            if A & B:
                ok = False
                break
        if not ok:
            continue
        for flips in range(1 << len(free)):
            A2, B2 = A, B
            bad = False
            for ci, (z_off, o_off) in enumerate(free):
                if (flips >> ci) & 1:
                    A2 |= z_off
                    B2 |= o_off
                else:
                    A2 |= o_off
                    B2 |= z_off
                if A2 & B2:
                    bad = True
                    break
            if bad:
                continue
            got = trie.enum(A2, B2, cap)
            if got is None:
                return None
            for g in got:
                out.append((a, g))
    return out


class _C4Worker:
    """Lift-and-complete worker for the C4 join.  Lift candidate lists are
    memoized per (slot, u) — every u appears in many C3 entries."""

    def __init__(self, fix):
        self.fiber5 = _fiber_index(fix[5], 5)
        self.f5 = fix[5]
        self.trie5 = BitTrie(fix[5], 32)
        self.face6 = sum(1 << p for p in range(64) if p & 1)
        self.memo = {}

    def lift(self, slot, u):
        key = (slot, u)
        got = self.memo.get(key)
        if got is None:
            a = 1 if extract(u, 5, slot - 1, 1) == full_table(4) else 0
            # u = (v'_{slot-1} ? a : e); the lift's below-face component h
            # satisfies extract(h, 5, 0, 1) = e
            e = extract(u, 5, slot - 1, 0)
            got = []
            for h in self.fiber5.get(e, []):
                m = insert_top(h, 6, slot, 1, a)
                if extract(m, 6, 0, 1) == u and member_ok_level6(m, slot):
                    got.append(m)
            self.memo[key] = got
        return got

    def entry(self, triple):
        u0, u1, u2 = triple
        l1 = self.lift(1, u0)
        if not l1:
            return 0, []
        l2 = self.lift(2, u1)
        if not l2:
            return 0, []
        l3 = self.lift(3, u2)
        if not l3:
            return 0, []
        ncombos = 0
        results = []
        for m1 in l1:
            for m2 in l2:
                for m3 in l3:
                    ncombos += 1
                    mixed = _forced_masks((m1, m2, m3), T3OF6, 6)
                    # (T3of6, 3) is UNSAT (K2), so the partial never
                    # refines on its own
                    assert mixed, "K2 violated: 3-member partial refines"
                    pairs = complete_anchor_trie(mixed, 6, self.trie5,
                                                 self.face6)
                    if pairs is None:
                        pairs = [(a, g) for g in self.f5 for a in (0, 1)]
                    for a, g in pairs:
                        m0 = insert_top(g, 6, 0, 1, a)
                        if not member_ok_level6(m0, 0):
                            continue
                        tup = (m0, m1, m2, m3)
                        if refine_fast(tup, T3OF6, 6):
                            results.append(tup)
        return ncombos, results


_C4W = None


def _c4_init(fix5, fix6):
    global _C4W
    _C4W = _C4Worker([None, None, None, None, None, fix5, fix6])


def _c4_chunk(chunk):
    total = 0
    out = []
    for triple in chunk:
        n, res = _C4W.entry(triple)
        total += n
        out.extend(res)
    return total, out


def build_c4(fix, c3, jobs=1):
    """All 4-tuples (m0, m1, m2, m3) of 6-var functions in K3 shape
    (designated positive directions 0..3, vars 4,5 spare) refining T3of6
    globally.  Built by anchor-face join: restrict to {v0=1} (m0's face):
    (m1, m2, m3) restrict to a C3 triple; lift each through the
    Fixable(5) -> Fixable(4) restriction fibers, filter by the K3 pool
    conditions, complete m0 exactly, verify globally over 64 points."""
    t0 = time.time()
    results = []
    ncombos = 0
    chunks = [c3[i:i + 2000] for i in range(0, len(c3), 2000)]
    _c4_init(fix[5], fix[6])  # built pre-fork: workers COW-share the trie
    if jobs > 1:
        import multiprocessing as mp
        with mp.Pool(jobs) as pool:
            for cidx, (n, res) in enumerate(
                    pool.imap(_c4_chunk, chunks)):
                ncombos += n
                results.extend(res)
                if cidx % 20 == 0:
                    print(f"    C4 progress: chunk {cidx}/{len(chunks)}, "
                          f"{ncombos} combos, {len(results)} tuples, "
                          f"{time.time() - t0:.0f}s", flush=True)
    else:
        for cidx, chunk in enumerate(chunks):
            n, res = _c4_chunk(chunk)
            ncombos += n
            results.extend(res)
            if cidx % 20 == 0:
                print(f"    C4 progress: chunk {cidx}/{len(chunks)}, "
                      f"{ncombos} combos, {len(results)} tuples, "
                      f"{time.time() - t0:.0f}s", flush=True)
    print(f"    |C4| = {len(results)} tuples "
          f"({ncombos} lift combos, {time.time() - t0:.0f}s)", flush=True)
    return results


class _TopWorker:
    """Lift-and-complete worker for the final join (same shape as C4,
    one level up)."""

    def __init__(self, fix6):
        self.fiber6 = _fiber_index(fix6, 6)
        self.f6 = fix6
        self.trie6 = BitTrie(fix6, 64)
        self.face7 = sum(1 << p for p in range(128) if p & 1)
        self.memo = {}

    def lift(self, slot, m):
        key = (slot, m)
        got = self.memo.get(key)
        if got is None:
            c = 1 if extract(m, 6, slot - 1, 1) == full_table(5) else 0
            h = extract(m, 6, slot - 1, 0)
            got = []
            for g in self.fiber6.get(h, []):
                w = insert_top(g, 7, slot, 1, c)
                if extract(w, 7, 0, 1) == m and witness_ok_level7(w, slot):
                    got.append(w)
            self.memo[key] = got
        return got

    def entry(self, tup):
        m1, m2, m3, m4 = tup
        lifted = []
        for slot, m in ((1, m1), (2, m2), (3, m3), (4, m4)):
            l = self.lift(slot, m)
            if not l:
                return 0, []
            lifted.append(l)
        ncombos = 0
        survivors = []
        for w1 in lifted[0]:
            for w2 in lifted[1]:
                for w3 in lifted[2]:
                    for w4 in lifted[3]:
                        ncombos += 1
                        mixed = _forced_masks((w1, w2, w3, w4), MAJ7, 7)
                        # (maj7, 4) is UNSAT, so the partial never
                        # refines on its own
                        assert mixed, "(maj7,4) violated: partial refines"
                        pairs = complete_anchor_trie(mixed, 7, self.trie6,
                                                     self.face7)
                        if pairs is None:
                            pairs = [(a, g) for g in self.f6
                                     for a in (0, 1)]
                        for a, g in pairs:
                            w0 = insert_top(g, 7, 0, 1, a)
                            if not witness_ok_level7(w0, 0):
                                continue
                            tup5 = (w0, w1, w2, w3, w4)
                            if refine_fast(tup5, MAJ7, 7):
                                survivors.append(tup5)
        return ncombos, survivors


_TOPW = None


def _top_init(fix6):
    global _TOPW
    _TOPW = _TopWorker(fix6)


def _top_chunk(chunk):
    total = 0
    out = []
    for tup in chunk:
        n, res = _TOPW.entry(tup)
        total += n
        out.extend(res)
    return total, out


def top_join(fix, c4, jobs=1):
    """The final level: for each C4 tuple (restrictions of w1..w4 to
    {x0=1}), lift each member through the Fixable(6) -> Fixable(5)
    restriction fibers, filter by the K4 pool conditions, complete w0
    exactly, verify globally over all 128 points.  Returns all surviving
    5-tuples (expected: none, or k(maj7) = 5 certificates)."""
    t0 = time.time()
    survivors = []
    ncombos = 0
    chunks = [c4[i:i + 500] for i in range(0, len(c4), 500)]
    _top_init(fix[6])  # built pre-fork: workers COW-share the trie
    if jobs > 1:
        import multiprocessing as mp
        with mp.Pool(jobs) as pool:
            for cidx, (n, res) in enumerate(pool.imap(_top_chunk, chunks)):
                ncombos += n
                survivors.extend(res)
                if cidx % 20 == 0:
                    print(f"    top progress: chunk {cidx}/{len(chunks)}, "
                          f"{ncombos} combos, {len(survivors)} survivors, "
                          f"{time.time() - t0:.0f}s", flush=True)
    else:
        for cidx, chunk in enumerate(chunks):
            n, res = _top_chunk(chunk)
            ncombos += n
            survivors.extend(res)
            if cidx % 20 == 0:
                print(f"    top progress: chunk {cidx}/{len(chunks)}, "
                      f"{ncombos} combos, {len(survivors)} survivors, "
                      f"{time.time() - t0:.0f}s", flush=True)
    print(f"  top join done: {ncombos} combos, {len(survivors)} survivors "
          f"({time.time() - t0:.0f}s)", flush=True)
    return survivors


# ---------------------------------------------------------------------------
# SECTION H: main
# ---------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--stage", choices=["controls", "ladder", "prepass",
                                        "core", "c4count", "top", "all"],
                    default="all")
    ap.add_argument("--big", action="store_true",
                    help="also compute |Fixable(7)| (RAM-heavy)")
    ap.add_argument("--prepass-seconds", type=int, default=600)
    ap.add_argument("--force-top", action="store_true",
                    help="actually run the full 5-tuple join (months of CPU)")
    ap.add_argument("--jobs", type=int,
                    default=max(1, (os.cpu_count() or 2) - 1))
    args = ap.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    _selfcheck_bit_ops()
    print("bit-op self-checks: PASS")

    t0 = time.time()
    fix = gen_fixable(6)
    print(f"Fixable layers 0..6 generated: {[len(l) for l in fix]} "
          f"({time.time() - t0:.0f}s)")

    if args.stage in ("controls", "all"):
        if not stage_controls(fix, big=args.big):
            print("CONTROLS FAILED — aborting")
            sys.exit(1)
    if args.stage in ("ladder", "all"):
        if not stage_ladder(fix, repo_root):
            print("LADDER FAILED — aborting")
            sys.exit(1)
    if args.stage in ("prepass", "all"):
        hit = prepass(fix, seconds=args.prepass_seconds)
        if hit is not None:
            print("VERDICT: SAT — k(maj7) = 5 witness found (pre-pass)")
            print(json.dumps({"verdict": "SAT",
                              "witnesses": [hex(w) for w in hit]}))
            return
    if args.stage in ("core", "all"):
        c3 = build_c3(fix)
        # measure the join scale on a strided sample and report honestly
        _c4_init(fix[5], fix[6])
        _top_init(fix[6])
        nsample = 60
        stride = max(1, len(c3) // nsample)
        sample = c3[::stride][:nsample]
        c4samp = []
        for tr in sample:
            _, res = _C4W.entry(tr)
            c4samp.extend(res)
        top_combos = 0
        for tup in c4samp:
            lifted = [_TOPW.lift(slot, mm)
                      for slot, mm in ((1, tup[0]), (2, tup[1]),
                                       (3, tup[2]), (4, tup[3]))]
            if all(lifted):
                top_combos += (len(lifted[0]) * len(lifted[1])
                               * len(lifted[2]) * len(lifted[3]))
        scale = len(c3) / len(sample)
        est_c4 = len(c4samp) * scale
        est_top = top_combos * scale
        print(f"  core scale (strided {len(sample)}-entry sample):")
        print(f"    |C3| = {len(c3)} (exhaustive)")
        print(f"    |C4| ~ {est_c4:.2e} (exact count: --stage c4count)")
        print(f"    top-join completions ~ {est_top:.2e} — OUT OF BUDGET")
        print("VERDICT: INCOMPLETE — the collapsed configuration is NOT")
        print("  exhausted; the bracket 5 <= k(maj7) <= 6 stands.")
        print("  Ruled out (exhaustively, script level): every 5-witness")
        print("  family outside the all-positive collapsed configuration")
        print("  (kill ladder; sign-purity slice kernel-proved in")
        print("  WitnessMaj7SignPurity.lean), and every family whose")
        print("  anchor-face restriction falls outside C3/C4.")
    if args.stage == "c4count":
        c3 = build_c3(fix)
        c4 = build_c4(fix, c3, jobs=args.jobs)
        print(f"exact |C4| = {len(c4)}")
    if args.stage == "top":
        if not args.force_top:
            print("refusing to run the full 5-tuple join without "
                  "--force-top (measured ~5e12 completions)")
            sys.exit(2)
        c3 = build_c3(fix)
        c4 = build_c4(fix, c3, jobs=args.jobs)
        survivors = top_join(fix, c4, jobs=args.jobs)
        if survivors:
            print("VERDICT: SAT — k(maj7) = 5 witness found (top join)")
            for tup in survivors[:5]:
                print(json.dumps({"witnesses": [hex(w) for w in tup]}))
        else:
            print("VERDICT: UNSAT — no five fixable witnesses compute maj7")
            print("core solutions: 0")


if __name__ == "__main__":
    main()
