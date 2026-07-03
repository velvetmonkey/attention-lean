/-
  AttentionLean.AxiomsDirty — expected-dirty axiom pins (drift detection).

  Companion to AttentionLean.Axioms. The enumerated fixed-width lower bounds
  `parity3_requires_three_heads` (ParitySmall) and `parity4_requires_four_heads`
  (Parity4Main) are proved by `native_decide`, so they carry
  `Lean.ofReduceBool` and `Lean.trustCompiler` BY DESIGN (documented in
  README.md). They do NOT meet the clean-axiom bar that AttentionLean.Axioms
  enforces; the general theorem `parityN_requires_N_heads` subsumes their
  content at the clean tier.

  They are pinned here anyway, with their FULL expected footprint, so that any
  drift, most importantly a `sorryAx` creeping in, still fails a bare
  `lake build`. This module is a member of the `AttentionLean` lib (glob
  `AttentionLean.+`), so it is compiled by `lake build` and its #guard_msgs
  are enforced. It is deliberately NOT the root of the `axiom_check` exe:
  importing the native_decide modules makes that binary heavy to run, and the
  compile-time gate is identical whether or not an exe runs.
-/
import AttentionLean.ParitySmall
import AttentionLean.Parity4Main

/--
info: 'parity3_requires_three_heads' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in #print axioms parity3_requires_three_heads

/--
info: 'parity4_requires_four_heads' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in #print axioms parity4_requires_four_heads
