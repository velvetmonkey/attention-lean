# attention-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](AttentionLean)
[![DOI](https://img.shields.io/badge/DOI-TODO-lightgrey)](#)

Lean 4 / Mathlib formalisation of hard attention expressivity over finite Boolean sequences.

All theorems use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`.

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

## Module structure

```text
AttentionLean/
├── Defs.lean    — HardAttentionHead, scores, value reads, argmax, head output
├── Compute.lean — Computes predicate and two-token helper theorems
├── AndOr.lean   — single-head constructions for AND and OR
└── Xor.lean     — single-head lower bound for XOR
AttentionLean.lean — root module re-exporting all submodules
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
