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
import AttentionLean.Parity3Clean
import AttentionLean.WitnessSeparation
import AttentionLean.WitnessTheory
import AttentionLean.WitnessEmbedding
import AttentionLean.WitnessMajority
import AttentionLean.WitnessTightness

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

-- Exact head complexity of parity3 at clean tier: k(3) = 4

/--
info: 'parity3_not_achievable_with_three_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity3_not_achievable_with_three_heads

/--
info: 'parity3_achievable_with_four_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity3_achievable_with_four_heads

/--
info: 'parity3_head_complexity_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity3_head_complexity_four

-- Witness separation: the abstract collision ⇒ non-computation kernel

/-- info: 'witness_separation_fails' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms witness_separation_fails

/--
info: 'parity3_indicator_heads_cannot_separate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity3_indicator_heads_cannot_separate

/-- info: 'indicator_heads_collide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms indicator_heads_collide

/-- info: 'parity_separates_antipodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parity_separates_antipodes

/-- info: 'potential_separation_fails' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms potential_separation_fails

/--
info: 'rank_potentials_cannot_see_flag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms rank_potentials_cannot_see_flag

-- Witness theory: characterization, counting bound, fixable lower bound

/--
info: 'witness_computable_iff_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms witness_computable_iff_refines

/--
info: 'witness_separation_fails_of_char' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms witness_separation_fails_of_char

/-- info: 'witness_counting_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms witness_counting_bound

/--
info: 'id_fin4_two_bool_witnesses_suffice' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms id_fin4_two_bool_witnesses_suffice

/--
info: 'id_fin4_one_bool_witness_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms id_fin4_one_bool_witness_fails

/-- info: 'exists_flip_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exists_flip_collision

/--
info: 'fixable_witnesses_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fixable_witnesses_lower_bound

/--
info: 'parityN_requires_N_heads_of_witness_theory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parityN_requires_N_heads_of_witness_theory

/--
info: 'parity3_two_fixable_witnesses_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parity3_two_fixable_witnesses_fail

-- Witness embedding: restriction lower bound past everywhere-sensitivity

/-- info: 'fixable_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixable_restrict

/--
info: 'restriction_embedding_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms restriction_embedding_lower_bound

/-- info: 'ip2_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ip2_embed

/--
info: 'ip2_not_everywhere_sensitive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ip2_not_everywhere_sensitive

/--
info: 'ip2_needs_m_fixable_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ip2_needs_m_fixable_witnesses

/--
info: 'ip2_four_bits_one_head_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ip2_four_bits_one_head_fails

-- Witness majority: subcube-nonconstancy bound; majority settled HARD

/--
info: 'fixable_witnesses_lower_bound_of_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fixable_witnesses_lower_bound_of_nonconstant

/--
info: 'maj_nonconstant_on_small_subcubes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj_nonconstant_on_small_subcubes

/--
info: 'maj_needs_half_fixable_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj_needs_half_fixable_witnesses

/-- info: 'dictator_fixable' depends on axioms: [propext] -/
#guard_msgs in #print axioms dictator_fixable

/--
info: 'maj_computable_by_n_fixable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj_computable_by_n_fixable

/-- info: 'maj3_one_head_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj3_one_head_fails

-- Witness tightness: exact witness numbers (maj3 = 2, parity = n, ip2 = m)

/-- info: 'every_target_computable_by_n_dictators' depends on axioms: [propext] -/
#guard_msgs in #print axioms every_target_computable_by_n_dictators

/-- info: 'majW1_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms majW1_fixable

/-- info: 'majW2_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms majW2_fixable

/--
info: 'maj3_eq_two_witness_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj3_eq_two_witness_combination

/--
info: 'maj3_computable_by_two_fixable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj3_computable_by_two_fixable

/--
info: 'maj3_witness_number_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj3_witness_number_exact

/--
info: 'parityN_witness_number_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms parityN_witness_number_exact

/-- info: 'and_pair_fixable' depends on axioms: [propext] -/
#guard_msgs in #print axioms and_pair_fixable

/--
info: 'ip2_witness_number_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ip2_witness_number_exact

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
