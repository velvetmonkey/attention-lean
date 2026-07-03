# attention-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](AttentionLean)
[![DOI](https://img.shields.io/badge/DOI-TODO-lightgrey)](#)

Lean 4 / Mathlib formalisation of hard attention expressivity over finite Boolean sequences.

The general parity lower bound, `parityN_requires_N_heads` (with `collision_exists_n` and the `parityN` compatibility lemmas), the windowed lower bound (`ParityWindow`), and the general achievability upper bound (`ParityAchieve`) are proved using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`, with no `native_decide`. The enumerated fixed-width results (the `Parity4*` modules and some `Compute` lemmas) additionally use `native_decide`, which introduces the `Lean.ofReduceBool` axiom.

**Head complexity of parity.** Writing `k(n)` for the least number of heads computing `parityN`: `n ≤ k(n) ≤ 2^(n-1)`, both ends formal (`parityN_requires_N_heads`, `parityN_achievable_with_exp_heads`). At `n = 2` the bounds meet: `k(2) = 2` exactly. **`k(3) = 4 = 2^(3-1)` exactly, fully machine-checked at the clean-axiom tier** (`parity3_head_complexity_four`): three heads cannot compute parity3 (`parity3_not_achievable_with_three_heads` — a STRUCTURAL proof, no enumeration, no `native_decide`: every head is constant on a half-cube and line-constant on every face; a decidable 32-shape classification forces antipodal point-indicators on constancy faces; the three signed-direction cases die by a same-inputs pair, a two-face sign clash, or the `T`-vs-antipode kill), while four heads do (`parity3_achievable_with_four_heads`). In particular "n heads suffice" is FALSE in general. The exhaustive search (`scripts/parity_head_search.py`, 0 of 152,096 three-head multisets) stands as independent cross-evidence.

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
