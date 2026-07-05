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
import AttentionLean.WitnessMaj5
import AttentionLean.WitnessMaj5Lower
import AttentionLean.FixableNormalForm
import AttentionLean.ThresholdCatalog
import AttentionLean.WitnessMaj5Exact
import AttentionLean.WitnessMaj5Heads
import AttentionLean.WitnessMaj5HeadsExact
import AttentionLean.DecisionListHeads
import AttentionLean.WitnessMaj7Bracket

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

-- Witness maj5: k(maj5) = 4 — the first gap past certificate complexity

/-- info: 'maj5W1_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5W1_fixable

/-- info: 'maj5W2_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5W2_fixable

/-- info: 'maj5W3_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5W3_fixable

/-- info: 'maj5W4_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5W4_fixable

/--
info: 'maj5_eq_four_witness_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_eq_four_witness_combination

/--
info: 'maj5_computable_by_four_fixable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_computable_by_four_fixable

/-- info: 'maj5_witness_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5_witness_bracket

-- Witness maj5 lower: the structural reduction toward k(maj5) >= 4

/-- info: 'fixable_const_halfcube' does not depend on any axioms -/
#guard_msgs in #print axioms fixable_const_halfcube

/-- info: 'fixable_update_restrict' depends on axioms: [propext] -/
#guard_msgs in #print axioms fixable_update_restrict

/--
info: 'maj_nonconst_of_pin_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj_nonconst_of_pin_bounds

/-- info: 'maj5_shared_face_kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5_shared_face_kill

/--
info: 'maj5_W1W2_not_completable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_W1W2_not_completable

/-- info: 'maj5_mixed_signs_kill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5_mixed_signs_kill

/-- info: 'maj5_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj5_reduction

-- Fixable normal form (R4a): Fixable = decision lists; oracle |Fixable(3)| = 96

/-- info: 'dl_fixable' depends on axioms: [propext] -/
#guard_msgs in #print axioms dl_fixable

/-- info: 'fixable_exists_dl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixable_exists_dl

/-- info: 'fixable_iff_dl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fixable_iff_dl

/-- info: 'majW1_has_dl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms majW1_has_dl

/-- info: 'card_fixable3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_fixable3

/-- info: 'maj3_not_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj3_not_fixable

/-- info: 'T2of4_not_pm_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms T2of4_not_pm_fixable

/-- info: 'T3of4_not_pm_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms T3of4_not_pm_fixable

/-- info: 'refines_single_pm' depends on axioms: [propext] -/
#guard_msgs in #print axioms refines_single_pm

-- Threshold catalog (L1): fixable pairs refining T2of4/T3of4 = the 24-element catalogs

/-- info: 'catalog_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms catalog_sound

/-- info: 'catalog_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms catalog_card

/-- info: 'refining_head_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms refining_head_positive

/--
info: 'T2_refining_pair_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms T2_refining_pair_classified

/-- info: 'fixable_dualz' depends on axioms: [propext] -/
#guard_msgs in #print axioms fixable_dualz

/-- info: 'catalog3_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms catalog3_sound

/-- info: 'catalog3_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms catalog3_card

/--
info: 'T3_refining_pair_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms T3_refining_pair_classified

-- Witness maj5 exact (S2/L2-L4): k(maj5) = 4 fully in the kernel

/-- info: 'fixable_restrictAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fixable_restrictAt

/-- info: 'face_classified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms face_classified

/-- info: 'hasLitB_of_fixable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hasLitB_of_fixable

/-- info: 'case2_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms case2_dead

/-- info: 'fixable_reindex' does not depend on any axioms -/
#guard_msgs in #print axioms fixable_reindex

/-- info: 'maj_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms maj_reindex

/-- info: 'case3_dead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms case3_dead

/--
info: 'maj5_no_three_fixable_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_no_three_fixable_witnesses

/--
info: 'maj5_witness_number_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_witness_number_exact

-- Witness maj5 heads: the attention-expressivity face of k(maj5) = 4

/--
info: 'maj5_requires_four_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_requires_four_heads

/--
info: 'maj5_three_indicator_heads_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_three_indicator_heads_fail

/--
info: 'maj5_first_three_witnesses_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_first_three_witnesses_fail

-- Witness maj5 heads exact (S1): four heads suffice; k_heads(maj5) = 4

/-- info: 'headW1_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms headW1_computes

/-- info: 'headW2_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms headW2_computes

/-- info: 'headW3_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms headW3_computes

/-- info: 'headW4_computes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms headW4_computes

/--
info: 'maj5_computable_by_four_heads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_computable_by_four_heads

/--
info: 'maj5_head_number_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj5_head_number_exact

-- Decision-list heads: the bridge theorem (Fixable = DL = head outputs)

/-- info: 'priorityDL_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms priorityDL_realizable

/-- info: 'dl_realizable_by_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dl_realizable_by_head

/--
info: 'fixable_realizable_by_head' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fixable_realizable_by_head

/--
info: 'head_output_iff_fixable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms head_output_iff_fixable

/--
info: 'heads_computability_iff_fixable_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms heads_computability_iff_fixable_witnesses

-- Witness maj7 bracket: 4 ≤ k_witness(maj7), k_heads(maj7) ≤ 6 and ≥ 4

/--
info: 'maj7_eq_six_witness_combination_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj7_eq_six_witness_combination_bits

/--
info: 'maj7_eq_six_witness_combination' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj7_eq_six_witness_combination

/--
info: 'maj7_computable_by_six_fixable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj7_computable_by_six_fixable

/--
info: 'maj7_witness_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj7_witness_bracket

/--
info: 'maj7_head_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms maj7_head_bracket

def main : IO Unit :=
  IO.println "axiom gate passed: all checks pinned by #guard_msgs at compile time"
