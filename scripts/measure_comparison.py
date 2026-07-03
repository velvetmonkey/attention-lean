#!/usr/bin/env python3
"""Candidate-measure comparison for the witness number k(T).

Evidence artifact for docs/witness-measure-novelty.md: computes, exactly and
exhaustively, the classical measures on the anchor functions whose witness
numbers k(T) are established in the Lean corpus (k(parity_n) = n,
k(ip2, 2m bits) = m, k(maj_3) = 2, k(maj_5) = 4 with the >= 4 half
search-pinned).

Measures: decision-tree rank (Ehrenfeucht-Haussler, DP over restrictions),
r-decision-list rank (greedy covered-point construction + first-term lower
bound), certificate complexity C and minCert (brute force), sensitivity,
block sensitivity (exact set packing), decision-tree depth (DP).

Expected output:
  func       k(T)  rank  rDL  C   minC  s   bs  depth
  maj_3      2     2     2    2   2     2   2   3
  maj_5      4     3     3    3   3     3   3   5
  parity_3   3     3     3    3   3     3   3   3
  parity_4   4     4     4    4   4     4   4   4
  parity_5   5     5     5    5   5     5   5   5
  ip2_m2     2     2     2    4   2     4   4   4

maj_5 is the universal discriminator: every subcube-style measure surviving
parity/maj_3/ip2 equals 3 there while k = 4.
"""

from functools import lru_cache
from itertools import combinations, product


def fv(f, p):
    return (f >> p) & 1


def weight(p):
    return bin(p).count("1")


def make_funcs():
    funcs = {}
    for n in (3, 5):
        N = 1 << n
        funcs[f"maj_{n}"] = (n, sum(1 << p for p in range(N)
                                    if n < 2 * weight(p)))
    for n in (3, 4, 5):
        N = 1 << n
        funcs[f"parity_{n}"] = (n, sum(1 << p for p in range(N)
                                       if weight(p) % 2 == 1))
    for m in (2,):
        n = 2 * m
        t = 0
        for p in range(1 << n):
            acc = 0
            for i in range(m):
                acc ^= ((p >> (2 * i)) & 1) & ((p >> (2 * i + 1)) & 1)
            if acc:
                t |= 1 << p
        funcs[f"ip2_m{m}"] = (n, t)
    return funcs


def restrict(f, n, i, b):
    out = 0
    q = 0
    for p in range(1 << n):
        if ((p >> i) & 1) == b:
            if fv(f, p):
                out |= 1 << q
            q += 1
    return out


def rank(f, n, memo=None):
    if memo is None:
        memo = {}
    key = (f, n)
    if key in memo:
        return memo[key]
    full = (1 << (1 << n)) - 1
    if f == 0 or f == full:
        memo[key] = 0
        return 0
    best = 10 ** 9
    for i in range(n):
        r0 = rank(restrict(f, n, i, 0), n - 1, memo)
        r1 = rank(restrict(f, n, i, 1), n - 1, memo)
        best = min(best, max(r0, r1) if r0 != r1 else r0 + 1)
    memo[key] = best
    return best


def subcube_points(n, term):
    return [p for p in range(1 << n)
            if all(((p >> i) & 1) == b for i, b in term.items())]


def rdl_greedy(f, n, r):
    remaining = set(range(1 << n))
    guard = 0
    while remaining:
        guard += 1
        if guard > 4 ** n:
            return False
        found = False
        for size in range(0, r + 1):
            for coords in combinations(range(n), size):
                for bits in product((0, 1), repeat=size):
                    term = dict(zip(coords, bits))
                    pts = [p for p in subcube_points(n, term)
                           if p in remaining]
                    if not pts:
                        continue
                    if len({fv(f, p) for p in pts}) == 1:
                        remaining -= set(pts)
                        found = True
                        break
                if found:
                    break
            if found:
                break
        if not found:
            return False
    return True


def rdl(f, n):
    for r in range(1, n + 1):
        if rdl_greedy(f, n, r):
            return r
    return n


def cert_sizes(f, n):
    sizes = []
    for x in range(1 << n):
        v = fv(f, x)
        found = None
        for r in range(0, n + 1):
            for coords in combinations(range(n), r):
                term = {i: (x >> i) & 1 for i in coords}
                if all(fv(f, p) == v for p in subcube_points(n, term)):
                    found = r
                    break
            if found is not None:
                break
        sizes.append(found)
    return max(sizes), min(sizes)


def sens(f, n):
    return max(sum(1 for i in range(n)
                   if fv(f, x) != fv(f, x ^ (1 << i)))
               for x in range(1 << n))


def block_sens(f, n):
    best = 0
    for x in range(1 << n):
        v = fv(f, x)
        sens_blocks = [m for m in range(1, 1 << n) if fv(f, x ^ m) != v]

        @lru_cache(maxsize=None)
        def pack(used):
            b = 0
            for m in sens_blocks:
                if m & used == 0:
                    b = max(b, 1 + pack(used | m))
            return b

        best = max(best, pack(0))
        pack.cache_clear()
    return best


def dt_depth(f, n, memo=None):
    if memo is None:
        memo = {}
    key = (f, n)
    if key in memo:
        return memo[key]
    full = (1 << (1 << n)) - 1
    if f == 0 or f == full:
        memo[key] = 0
        return 0
    best = 10 ** 9
    for i in range(n):
        best = min(best, 1 + max(dt_depth(restrict(f, n, i, 0), n - 1, memo),
                                 dt_depth(restrict(f, n, i, 1), n - 1, memo)))
    memo[key] = best
    return best


def main():
    funcs = make_funcs()
    K = {"maj_3": 2, "maj_5": 4, "parity_3": 3, "parity_4": 4,
         "parity_5": 5, "ip2_m2": 2}
    print(f"{'func':10s} {'k(T)':5s} {'rank':5s} {'rDL':4s} {'C':3s} "
          f"{'minC':5s} {'s':3s} {'bs':3s} {'depth':5s}")
    for name, (n, f) in funcs.items():
        C, mc = cert_sizes(f, n)
        print(f"{name:10s} {K[name]:<5d} {rank(f, n):<5d} {rdl(f, n):<4d} "
              f"{C:<3d} {mc:<5d} {sens(f, n):<3d} {block_sens(f, n):<3d} "
              f"{dt_depth(f, n):<5d}")


if __name__ == "__main__":
    main()
