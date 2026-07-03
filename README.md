# attention-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](AttentionLean)
[![DOI](https://img.shields.io/badge/DOI-TODO-lightgrey)](#)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Lean 4 / Mathlib formalisation of hard attention expressivity over finite Boolean sequences.

The general parity lower bound, `parityN_requires_N_heads` (with `collision_exists_n` and the `parityN` compatibility lemmas), the windowed lower bound (`ParityWindow`), and the general achievability upper bound (`ParityAchieve`) are proved using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`, with no `native_decide`. The enumerated fixed-width results (the `Parity4*` modules and some `Compute` lemmas) additionally use `native_decide`, which introduces the `Lean.ofReduceBool` axiom.

**Head complexity of parity.** Writing `k(n)` for the least number of heads computing `parityN`: `n ≤ k(n) ≤ 2^(n-1)`, both ends formal (`parityN_requires_N_heads`, `parityN_achievable_with_exp_heads`). At `n = 2` the bounds meet: `k(2) = 2` exactly. **`k(3) = 4 = 2^(3-1)` exactly, fully machine-checked at the clean-axiom tier** (`parity3_head_complexity_four`): three heads cannot compute parity3 (`parity3_not_achievable_with_three_heads` — a STRUCTURAL proof, no enumeration, no `native_decide`: every head is constant on a half-cube and line-constant on every face; a decidable 32-shape classification forces antipodal point-indicators on constancy faces; the three signed-direction cases die by a same-inputs pair, a two-face sign clash, or the `T`-vs-antipode kill), while four heads do (`parity3_achievable_with_four_heads`). In particular "n heads suffice" is FALSE in general. The exhaustive search (`scripts/parity_head_search.py`, 0 of 152,096 three-head multisets) stands as independent cross-evidence.

## Witness separation: a general lower-bound principle

The parity lower bound is one instance of a domain-agnostic principle formalised in `WitnessSeparation` and `WitnessTheory`. Model a computation as a family of *witnesses* `w : Fin k → S → V` read by an arbitrary *aggregator* `agg : (Fin k → V) → B`, computing `fun s => agg (fun i => w i s)`.

- **Refutation kernel** (`witness_separation_fails`, on `Quot.sound` alone): if two states collide under every witness while the target separates them, no aggregator computes the target. Collision implies non-computation.
- **Exact characterization** (`witness_computable_iff_refines`): some aggregator computes the target *iff* the witness map refines it (the target is constant on witness-fibres). The kernel is its one-pair contrapositive.
- **Two orthogonal lower bounds.** Information-capacity (`witness_counting_bound`: `|A| ≤ |V|^k` for high-image targets) and sensitivity (`fixable_witnesses_lower_bound`: an everywhere-sensitive target on `n` coordinates needs `n` `Fixable` witnesses, under *any* aggregator, not just a threshold).
- **Parity is a corollary.** `parityN_requires_N_heads` is recovered verbatim from the sensitivity bound (`parityN_requires_N_heads_of_witness_theory`): a hard-attention head is a `Fixable` witness, `parityN` is everywhere-sensitive, the thresholded readout is one aggregator.

The same kernel instantiates outside attention: `potential_separation_fails` shows a family of monotone potentials over a preorder cannot certify a predicate separating two order-equivalent states (the descent / Lyapunov reading).

## Theorems proved

| Module | Theorem | Description |
|---|---|---|
| `AttentionLean.Defs` | `attentionScore_eq_scoreVal` | The attention score at position `i` is exactly the position-local score value for `x i`. |
| `AttentionLean.Compute` | `argmaxScore_two` | For two positions, deterministic argmax selects position `0` when score `0 >= score 1`, otherwise position `1`. |
| `AttentionLean.Compute` | `headOutput_two` | Unfolds the full two-token hard-attention output into argmax, value read, affine readout, and threshold. |
| `AttentionLean.Compute` | `fin2_bool_forall` | Reduces universal claims about `Fin 2 -> Bool` inputs to the four Boolean cases. |
| `AttentionLean.AndOr` | `and_one_head` | Constructs a single one-dimensional hard-attention head computing Boolean AND on two-bit inputs. |
| `AttentionLean.AndOr` | `or_one_head` | Constructs a single one-dimensional hard-attention head computing Boolean OR on two-bit inputs. |
| `AttentionLean.Xor` | `xor_not_single_head` | Proves no single hard-attention head of any internal dimension computes XOR on two-bit inputs. |
| `AttentionLean.ParityN` | `parityN_requires_N_heads` | **General lower bound (headline).** For every `n` and every `k < n`, no `k` hard-attention heads through a thresholded affine readout compute `parityN`. Axioms: `propext`, `Classical.choice`, `Quot.sound`, with no `native_decide`. |
| `AttentionLean.ParityN` | `collision_exists_n` | Fewer than `n` fixable head-functions admit an opposite-parity input pair on which all of them agree: the pigeonhole / subcube collision that drives the general bound. |
| `AttentionLean.ParityWindow` | `parityN_requires_window_union` | **Windowed lower bound.** Heads whose argmax provably stays inside windows `W i` cannot compute `parityN` when the windows jointly miss a coordinate (`card (⋃ i, W i) < n`) — with no bound on the number of heads. Incomparable to `parityN_requires_N_heads` (e.g. `n` heads all windowed on one position). Same axioms, no `native_decide`. |
| `AttentionLean.ParityWindow` | `parityN_requires_window_bound` | Corollary of the union bound: `k` heads of window ≤ `t` need `k·t ≥ n`. (This numeric form also follows from `parityN_requires_N_heads`, since `t ≥ 1` forces `k ≤ k·t < n`; it is kept as the readable "heads × window" reading.) |
| `AttentionLean.ParityWindow` | `collision_of_fixableK` | t-coordinate generalisation of the collision lemma: `k` functions, each constant after pinning ≤ `t` coordinates on any subcube (`FixableK`), admit an opposite-parity agreeing pair whenever `k·t` is below the free-coordinate count. `Fixable` embeds at `t = 1` (`fixable_fixableK`). |
| `AttentionLean.ParityAchieve` | `parityN_achievable_with_exp_heads` | **General achievability (upper bound).** For every `n`, `2^(n-1)` hard-attention heads through a thresholded affine readout compute `parityN` — one indicator head per odd-parity point (`indicatorHead`, `indicatorHead_computes`, `card_odd_points`), unit weights, zero bias. The readout shape is verbatim the positive complement of `parityN_requires_N_heads`. Axioms: `propext`, `Classical.choice`, `Quot.sound`, no `native_decide`. |
| `AttentionLean.ParityAchieve` | `parity2_achievable_with_two_heads` | The `n = 2` instance: with the lower bound at `n = 2`, the exact head complexity of parity2 is 2. |
| `AttentionLean.Parity3Clean` | `parity3_not_achievable_with_three_heads` | **Clean-tier three-head insufficiency.** No 3-head configuration of any internal dimension computes parity3 — structural proof (fixability ⇒ half-cube constancy + face line-constancy; decidable face classification; three-case kill), no enumeration. Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `native_decide`. |
| `AttentionLean.Parity3Clean` | `parity3_head_complexity_four` | **k(3) = 4 exactly**, both halves clean: the insufficiency above paired with `parity3_achievable_with_four_heads` (instance of the `2^(n-1)` construction at `n = 3`). |
| `AttentionLean.WitnessSeparation` | `witness_separation_fails` | **The collision ⇒ non-computation kernel** (axioms: `Quot.sound` alone): witnesses agreeing on two states a target separates admit NO aggregator computing the target. `Parity3Clean.kill3` routes through it; `parity3_indicator_heads_cannot_separate` reconstructs the antipode kill with concrete heads for EVERY aggregator; `potential_separation_fails` + `rank_potentials_cannot_see_flag` instantiate it for monotone potentials over a preorder (a potential family cannot certify a predicate separating order-equivalent states). |
| `AttentionLean.WitnessTheory` | `witness_computable_iff_refines` | **Characterization**: some aggregator computes the target iff the witness map refines it (target constant on witness-fibres). The refutation kernel is its one-pair contrapositive. |
| `AttentionLean.WitnessTheory` | `witness_counting_bound` | **Information-capacity lower bound**: finite witness values + target injective on `A` ⇒ `|A| ≤ |V|^k`. Tight instance: identity on `Fin 4` — one Bool witness provably fails, two provably suffice. Scope: high-image targets only; does not subsume the parity bound. |
| `AttentionLean.WitnessTheory` | `fixable_witnesses_lower_bound` | **Sensitivity lower bound (the general theorem behind the parity bound)**: an everywhere-sensitive target on `n` Boolean coordinates is computed by no aggregator over `k < n` `Fixable` witnesses. `parityN_requires_N_heads` recovered verbatim as a corollary (`parityN_requires_N_heads_of_witness_theory`); strictly more general in the aggregator. |
| `AttentionLean.WitnessEmbedding` | `restriction_embedding_lower_bound` | **Embedding lower bound**: a target with a restriction that is everywhere-sensitive on `m` free coordinates is computed by no aggregator over `k < m` `Fixable` witnesses. Crux: fixability survives restriction (`fixable_restrict`). Instance: inner product mod 2 on `2m` bits — provably NOT everywhere-sensitive, yet embeds parity on the even coordinates, so it needs ≥ m fixable witnesses (`ip2_needs_m_fixable_witnesses`). Reach note: monotone targets (e.g. majority) are OUT — restrictions of monotone functions are monotone, everywhere-sensitive functions on ≥ 2 coordinates are not. |
| `AttentionLean.WitnessMajority` | `maj_needs_half_fixable_witnesses` | **Majority settled HARD**: any aggregator over `k` fixable witnesses with `2k < n` fails against strict majority — `k(maj_n) ≥ ⌈n/2⌉` — via the subcube-nonconstancy bound `fixable_witnesses_lower_bound_of_nonconstant` (a certificate-style measure: `k` fixable witnesses pin ≤ `k` coordinates, and fewer than `n/2` pinned votes never decide majority). Upper bracket: `n` fixable dictators + `maj` as aggregator compute it (`maj_computable_by_n_fixable`); exact `k(maj)` in `[⌈n/2⌉, n]` open. |
| `AttentionLean.WitnessTightness` | `maj3_witness_number_exact` | **Tightness**: exact witness numbers — `k(maj₃) = 2` (construction `maj₃ = (x₀ ∨ (x₁∧x₂)) ∧ ¬(x₀ ∧ ¬x₁ ∧ ¬x₂)`, fixability by kernel `decide`; the certificate bound is tight at n = 3), `k(parity_n) = n` (`parityN_witness_number_exact`), `k(ip2) = m` (`ip2_witness_number_exact`, AND-pair witnesses + parity aggregator, upper end `rfl`). General `k(T) = minCert(T)` open; `maj₅` (k ∈ {3,4}) is the smallest open case. |
| `AttentionLean.WitnessMaj5` | `maj5_witness_bracket` | **k(maj₅) = 4 — the first gap**: four fixable witnesses compute maj₅ (`(x₀∧A)∧(x₀∧B) ∨ (¬x₀∧C) ∨ (¬x₀∧D)` with the T₂⁴/T₃⁴ factor pairs; equality and all fixability by kernel `decide`), two provably fail (certificate rung). No THREE fixable witnesses work — exhaustive search over the exact |Fixable(4)| = 1050 class (`scripts/maj5_witness_search.py`; catalogs of 24 threshold-refining pairs, all assemblies dead), so witness number strictly exceeds certificate complexity: `k(T) = minCert(T)` FAILS at maj₅. Machine-checked bracket 3 ≤ k ≤ 4; the k ≥ 4 half is search evidence, formalization = future work. |
| `AttentionLean.WitnessMaj5Lower` | `maj5_reduction` | **The k(maj₅) ≥ 4 reduction, formalized**: any three fixable witnesses computing maj₅ have pairwise-distinct signed constancy directions (case 1 killed — `maj5_shared_face_kill`, whence `maj5_W1W2_not_completable`), and unanimous signs when directions are pairwise distinct (`maj5_mixed_signs_kill` via the sign-separated certificate lemma `maj_nonconst_of_pin_bounds`). Remaining for the full k ≥ 4: the case-2/uniform-case-3 catalog cascades (future work; `fixable_update_restrict` is the recursion tool). |
| `AttentionLean.FixableNormalForm` | `fixable_iff_dl` | **The classification of fixable witnesses**: `Fixable` = decision lists, both directions (the forcing literal heads the list; `fixable_update_restrict` supplies the tail). Kernel-verified oracle: `card_fixable3` — \|Fixable(3)\| = 96, the priority-function count. Plus the catalog-cascade openers: maj₃ and the ±4-bit thresholds are unfixable; single-witness refinement is equality up to complement. R4a of the k(maj₅) ≥ 4 program; the catalog cascade (L1–L4) remains open. |
| `AttentionLean.ThresholdCatalog` | `T2_refining_pair_classified` | **L1 — the threshold catalogs, classified in the kernel**: every ordered fixable pair refining T₂⁴ is one of the 24 catalog pairs (subset function + complement partner, free polarities), and dually for T₃⁴ (`T3_refining_pair_classified` via `fixable_dualz`). Soundness (`catalog_sound`/`catalog3_sound`) + in-kernel \|R2\| = \|R3\| = 24 oracles. Route: positive-heads/distinct-heads/face-equation cascade → three-region `shape4` glue → 12 per-direction kernel decides (layered `Decidable` instances, fixability-first). L2–L4 remain open; k(maj₅) = 4 stays search-pinned. |
| `AttentionLean.Parity4Main` | `parity4_requires_four_heads` | Enumerated `n = 4` case: no 3 heads compute parity on 4 bits. Proved by `native_decide`, so it additionally carries `Lean.ofReduceBool`. |
| `AttentionLean.ParitySmall` | `parity3_requires_three_heads` | Enumerated `n = 3` case: no 2 heads compute parity on 3 bits. Proved by `native_decide`, so it additionally carries `Lean.ofReduceBool`. |

## Module structure

```text
AttentionLean/
├── Defs.lean:          HardAttentionHead, scores, value reads, argmax, head output
├── Compute.lean:       Computes predicate and two-token helper theorems
├── AndOr.lean:         single-head constructions for AND and OR
├── Xor.lean:           single-head lower bound for XOR
├── ParityN.lean:       general parity lower bound (parityN_requires_N_heads, collision_exists_n)
├── ParityNCompat.lean: parityN compatibility / bridge lemmas
├── ParityWindow.lean:  t-fixable generalisation + windowed lower bound (parityN_requires_window_union)
├── ParityAchieve.lean: general achievability upper bound (parityN_achievable_with_exp_heads)
├── Parity3Clean.lean:  clean-tier 3-head insufficiency for parity3 (k(3) = 4 exact)
├── WitnessSeparation.lean: abstract collision ⇒ non-computation kernel + two instances
├── WitnessTheory.lean: computability characterization + counting & fixable lower bounds
├── WitnessEmbedding.lean: restriction/embedding lower bound + inner-product instance
├── WitnessMajority.lean: subcube-nonconstancy bound; majority needs ≥ ⌈n/2⌉ witnesses
├── WitnessTightness.lean: exact witness numbers (maj₃ = 2, parity = n, ip2 = m)
├── WitnessMaj5.lean:   k(maj₅) = 4 — witness number exceeds certificate complexity
├── WitnessMaj5Lower.lean: structural reduction toward the k(maj₅) ≥ 4 formalization
├── FixableNormalForm.lean: Fixable = decision lists (R4a) + catalog-cascade openers
├── ThresholdCatalog.lean: L1 — the 24-pair threshold catalogs, kernel-classified
├── ParitySmall.lean:   enumerated n=3 lower bound (parity3_requires_three_heads)
└── Parity4*.lean:      enumerated n=4 lower bound (parity4_requires_four_heads) + achievability batches
AttentionLean.lean: root module re-exporting all submodules
```

## Building

```bash
lake build
```

## Verification

```bash
rg "sorry|admit" AttentionLean/
```

This command returns nothing for the checked source tree.

## License

MIT. See [LICENSE](LICENSE). Copyright (c) 2026 Ben Cassie.
