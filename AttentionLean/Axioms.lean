/-
  AttentionLean.Axioms — the build-gated axiom transcript.

  Every headline parity theorem must sit on {propext, Classical.choice,
  Quot.sound} only — no sorryAx, no Lean.ofReduceBool. Each expected
  footprint is pinned with #guard_msgs, and the `axiom_check` executable is
  in the lake defaultTargets, so any axiom drift fails a bare `lake build`
  itself. Ported verbatim from the seal-host Test/Axioms.lean convention.

  EXPECTED-DIRTY, PINNED IN A COMPANION: the enumerated fixed-width lower
  bounds `parity3_requires_three_heads` (ParitySmall) and
  `parity4_requires_four_heads` (Parity4Main) are proved by `native_decide`,
  so they carry `Lean.ofReduceBool` and `Lean.trustCompiler` BY DESIGN
  (documented in README.md). They do NOT meet the clean-axiom bar this exe
  reports on. They ARE pinned, with their full expected footprint, in
  `AttentionLean/AxiomsDirty.lean` (a lib module built and hence gated by a
  bare `lake build`, so a `sorryAx` creep there still fails the build). They
  live in a companion rather than here because importing the native_decide
  modules into this executable root makes the `axiom_check` binary heavy to
  run; the compile-time gate is identical either way.
-/
import AttentionLean.ParityN
import AttentionLean.ParityWindow
import AttentionLean.ParityAchieve

-- General parity lower bound (headline)

/-- info: 'parityN_requires_N_heads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parityN_requires_N_heads

-- Windowed lower bounds

/--
info: 'parityN_requires_window_union' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parityN_requires_window_union

/--
info: 'parityN_requires_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parityN_requires_window_bound

-- Achievability upper bound (2^(n-1) heads)

/-- info: 'indicatorHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indicatorHead

/-- info: 'indicatorHead_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indicatorHead_computes

/-- info: 'card_odd_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_odd_points

/--
info: 'parityN_achievable_with_exp_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parityN_achievable_with_exp_heads

/--
info: 'parity2_achievable_with_two_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity2_achievable_with_two_heads

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
