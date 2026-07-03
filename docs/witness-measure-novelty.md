# Is k(T) a known measure? — Novelty verdict

**VERDICT: k(T) is DISTINCT from every candidate known measure tested — GO for a
paper, CONDITIONAL on one thing: the entire separation case rests on k(maj₅) ≥ 4,
which today is exhaustive-search evidence (complete case analysis, positive
controls), not yet a kernel theorem. If k(maj₅) were 3, k would agree with
decision-tree rank on every anchor and "k = rank" would become the live
hypothesis. Close S2 (`maj5_no_three_fixable_witnesses`) before submitting
anything.**

Stance taken as instructed: null hypothesis "k is known", attacked hard. The
null survives parity, maj₃ and ip2 against its best candidate (decision-tree
rank matches all three) and dies only at maj₅.

## The measure

k(T) = minimum k such that T = g(w₁,…,w_k) for Fixable witnesses w_i and an
ARBITRARY outer aggregator g. Machine-checked on main: Fixable = decision
lists exactly (`fixable_iff_dl`), so

> k(T) = fewest decision-list inner functions that compute T under an
> unrestricted outer combiner — equivalently, the minimal number of
> hard-attention heads for T (heads = Fixable, `headOutput_fixable`; the
> lower-bound transfer is `attnComputes_to_fixable_witnesses` on the
> `feat/attention-bridge` scaffold).

Anchors (Lean, main): k(parity_n) = n, k(ip2 on 2m bits) = m, k(maj₃) = 2,
k(maj₅) = 4 — **with the honesty flag that the maj₅ lower half (≥ 4) is
search-pinned** (`scripts/maj5_witness_search.py`); the kernel has the bracket
3 ≤ k(maj₅) ≤ 4 plus the structural reduction and the L1 catalogs.

## Computed comparison table

All candidate values below computed exactly by `scripts/measure_comparison.py`
(exhaustive, 3–5 variable truth tables; rank/depth by DP over restrictions,
certificates/sensitivity/block-sensitivity by brute force):

| function  | k(T) | DT rank | r-DL rank | C(T) | minCert | s(T) | bs(T) | DT depth |
|-----------|------|---------|-----------|------|---------|------|-------|----------|
| parity₃   | 3    | 3       | 3         | 3    | 3       | 3    | 3     | 3        |
| parity₄   | 4    | 4       | 4         | 4    | 4       | 4    | 4     | 4        |
| parity₅   | 5    | 5       | 5         | 5    | 5       | 5    | 5     | 5        |
| maj₃      | 2    | 2       | 2         | 2    | 2       | 2    | 2     | 3        |
| ip2 (m=2) | 2    | 2       | 2         | 4    | 2       | 4    | 4     | 4        |
| **maj₅**  | **4**| **3**   | **3**     | **3**| **3**   | **3**| **3** | 5        |

maj₅ is the universal discriminator: every subcube-style candidate that
survives the first three anchors equals 3 there, while k = 4.

## Per-candidate verdicts

| # | Measure M | Relation to k | Killed by | Reason |
|---|---|---|---|---|
| 1 | **Decision-tree rank** (Ehrenfeucht–Haussler) | **rank(T) ≤ k(T), strict at maj₅** — the closest candidate | maj₅: rank 3 ≠ k 4 | ≤ direction is a THEOREM (sketch below). Matches parity_n (= n), maj₃ (= 2), ip2 (= m). Diverges only at maj₅: witness rank-3 tree = query x₀, subtrees T₂⁴/T₃⁴ each rank 2 (verified by DP). |
| 2 | **r-decision-list rank** (min r s.t. T is an r-DL) | ≤ k on anchors, strict at maj₅ | maj₅: 3 ≠ 4 | Matches parity (first term must pin all n bits), maj₃ (2-DL of pair-terms), ip2 (m). maj₅ is a 3-DL (all 3-subsets → 1, default 0) and no 2-DL (maj₅ non-constant on every codim-2 subcube — kernel lemma `maj_nonconstant_on_small_subcubes`). |
| 3 | Composed-function rank measures (Dahiya et al., arXiv:2209.12877 family) | framework-adjacent, values differ | maj₅ via rank | These reduce to rank-style quantities; killed with #1. The TEMPLATE "junta over a base class" is known (juntas of halfspaces, of parities); the instantiation at base class = decision lists, with exact values and this gap, is what we have not found named or computed anywhere. |
| 4 | DNF/CNF minimal term count | incomparable, wildly off | parity: 2^(n−1) ≠ n; maj₃: 3 terms ≠ 2 | Term counts explode on parity; no transform (log of 2^(n−1) = n−1 ≠ n fails too, and log-DNF(maj₃) = log 3 ∉ ℕ). |
| 5 | Certificate complexity C(T); minCert; **unambiguous** UC(T) | C: killed twice; minCert ≤ k with strict gap at maj₅ (our flagged phenomenon); UC killed at maj₃ | ip2: C = 2m ≠ m; maj₅: C = minCert = 3 ≠ 4; UC(maj₃) = 3 ≠ 2 | UC(maj₃): maj₃⁻¹(1) = {110,101,011,111}; its three 2-point subcubes pairwise overlap at 111, so any unambiguous cover uses at most one of them and must contain a size-3 singleton certificate. |
| 6 | Junta size; PTF (threshold) degree; sign-rank; sensitivity; block sensitivity | all separated | junta: ip2 = 2m ≠ m, maj₅ = 5 ≠ 4. PTF degree: maj is a halfspace, deg ± = 1 ≠ 2 = k(maj₃). sign-rank: O(1) on parity's XOR matrix ≠ n. s, bs: table (maj₅ 3 ≠ 4; ip2 4 ≠ 2). Real degree: deg(maj₃) = 3 ≠ 2. | — |
| + | DT depth (bonus) | separated early | maj₃: 3 ≠ 2 (majority is evasive: depth = n) | — |
| + | Functions of k halfspaces (k_LTF; 1-DLs ⊆ LTFs) | k_LTF(T) ≤ k(T), strict | maj₃: k_LTF = 1 ≠ 2 | maj is itself a halfspace. Same template as #3 with a bigger base class. |

### Why rank(T) ≤ k(T) always (the ≤ half of the closest-candidate relation)

If T = g(w₁,…,w_k) with each w_i a decision list (rank-1 function): evaluate
w₁ by a rank-1 tree; at each leaf substitute a tree for w₂, and so on. Rank is
subadditive under leaf substitution, so the stacked tree has rank ≤ k, and its
leaves determine (w₁,…,w_k)(x), hence T. Consequence: **the arbitrary outer
aggregator never pushes k below rank** — this answers the brief's discriminator
question. The gap runs the other way: at maj₅ the decision-list *inner*
restriction costs one extra witness that even an unrestricted combiner cannot
recover (k = 4 > 3 = rank).

A pleasing sandwich, both ends tight and both strict at maj₅:

> rank(T) ≤ k(T) ≤ junta(T) ≤ n, with maj₅ giving 3 < 4 < 5.

(Upper: dictators are decision lists, so k ≤ junta size.)

### Simple transforms

No max/min/shift/log combination of the listed measures has the profile
(parity_n ↦ n, maj₃ ↦ 2, ip2 ↦ m, maj₅ ↦ 4): everything that scales like n on
parity and 2 on maj₃ sits at 3 on maj₅ (rank, r-DL, C, minCert, s, bs), and
everything at ≥ 4 on maj₅ (depth = 5, junta = 5) fails maj₃ or ip2. Checked
against the table; contrived affine patches fail on the parity family's slope.

## Closest known measure + explicit separating function

**Closest: decision-tree rank** (agrees on three of four anchor families and is
provably a lower bound for k). **Separating function: maj₅** — rank 3
(DP-verified; tree: root x₀, subtrees the 4-bit thresholds, each rank 2), while
k(maj₅) = 4 (kernel bracket ≤ 4; ≥ 4 by exhaustive search over the complete
case analysis with the L1 catalogs now kernel-classified).

## What the paper is (and is not)

- NOT "a brand-new decomposition framework": k is the junta-arity template
  instantiated at the decision-list base class. The template is standard.
- IS: (1) the identification of that instantiation as EXACTLY the
  hard-attention head count (heads = Fixable = decision lists, both directions
  — forward kernel-proved, converse S1 on the bridge scaffold); (2) exact
  values on standard families, kernel-checked; (3) the separation
  rank < k < junta at a single 5-bit function, i.e. attention head count is
  not certificate complexity, not rank, not sensitivity; (4) the certificate
  measure as a proved general lower bound with the first strict gap.

## Conditions and confidence

1. **Load-bearing wall: k(maj₅) ≥ 4** (S2, `maj5_no_three_fixable_witnesses`).
   Until it is kernel-closed, the honest claim is "3 ≤ k(maj₅) ≤ 4 with = 4
   search-verified"; every separation above evaporates at k(maj₅) = 3 and the
   correct headline would flip to "k = rank on all anchors — likely known".
   Search quality: exhaustive over a complete case split, reproduces
   |Fixable(3)| = 96, |Fixable(4)| = 1050, both 24-catalogs, and the maj₃
   positive controls; I rate the risk of it being wrong low, but the paper
   cannot ride on a script.
2. Literature breadth: I cannot rule out a niche paper computing "functions of
   k decision lists" arities. Recommended targeted pre-submission check:
   "functions of k decision lists", "decision-list juntas", the Dahiya–Mahajan
   rank paper's citation graph, and the hard-attention expressivity line
   (Hahn; Angluin–Chiang; Sanford–Hsu–Telgarsky) for head-count-per-function
   measures.

**Confidence: HIGH (≈ 0.85) that k is not a named, valued measure in the
listed families, conditional on k(maj₅) = 4. Unconditionally: MEDIUM — the
verdict is hostage to S2.**

## Recommendation

GO — but sequence it: close S2 first (it is simultaneously the paper's main
theorem and the novelty certificate), then write the paper as "the head-count
measure of hard attention: exact values and a separation from rank and
certificate complexity", with the Lean corpus as the artifact.
