/-
  AttentionLean.Axioms — the build-gated axiom transcript.

  Every headline parity theorem must sit on {propext, Classical.choice,
  Quot.sound} only — no sorryAx, no Lean.ofReduceBool. Each expected
  footprint is pinned with #guard_msgs, and the `axiom_check` executable is
  in the lake defaultTargets, so any axiom drift fails a bare `lake build`
  itself. Ported verbatim from the seal-host Test/Axioms.lean convention.

  DELIBERATELY NOT PINNED: the enumerated fixed-width lower bounds
  `parity3_requires_three_heads` (ParitySmall) and
  `parity4_requires_four_heads` (Parity4Main). Both are proved by
  `native_decide` and therefore carry `Lean.ofReduceBool` and
  `Lean.trustCompiler` BY DESIGN — documented in README.md ("The enumerated
  fixed-width results … additionally use native_decide"). They fall outside
  the clean-axiom bar this gate enforces, so they are excluded rather than
  pinned over; the general theorems below subsume their content at the
  clean-axiom tier.
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
