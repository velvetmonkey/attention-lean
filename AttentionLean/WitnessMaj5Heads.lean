/-
  AttentionLean.WitnessMaj5Heads

  THE ATTENTION-EXPRESSIVITY FACE OF k(maj₅) = 4:
  `maj5_requires_four_heads` — no three hard-attention heads combined
  through a thresholded affine readout compute strict majority on five
  bits.

  This is an INSTANTIATION, not a re-proof: the combinatorics live in
  the kernel theorem `maj5_no_three_fixable_witnesses`
  (WitnessMaj5Exact), which quantifies over ANY three fixable witnesses
  and ANY aggregator. Heads are fixable witnesses (`headOutput_fixable`,
  the same lemma behind the parity bridge), and the thresholded affine
  readout is one particular aggregator. Mirrors
  `parityN_requires_N_heads_of_witness_theory`. Note the contrast with
  parity: maj₅ is NOT everywhere-sensitive, so no sensitivity argument
  applies — the bound comes from the catalog-classification route.

  Non-vacuity: `maj5_three_indicator_heads_fail` — a concrete family of
  three indicator heads fails against EVERY aggregator (stronger than
  the affine readout); and `maj5_first_three_witnesses_fail` — even the
  first three witnesses of the shipped optimal 4-witness construction
  cannot be completed by any aggregator.

  FLAGGED, NOT LANDED: the positive side (`four heads suffice`,
  toward a `maj5_head_number_exact`). It needs the shipped witnesses
  maj5W1..W4 realized as head outputs — the decision-list-to-head
  construction (S1 of the AttentionBridge scaffold), which is a real
  score-gadget build, not an instantiation. Per the brief: flagged and
  stopped; the "three cannot" direction is the deliverable here.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`, no `sorry`. Purely additive.
-/
import AttentionLean.WitnessMaj5Exact

open Classical

noncomputable section

/-- **maj₅ requires four hard-attention heads.** For any three heads,
    weights and bias, the thresholded affine head-combination does not
    compute strict majority on five bits. -/
theorem maj5_requires_four_heads {d : ℕ}
    (h : Fin 3 → HardAttentionHead 5 d) (w : Fin 3 → ℝ) (bias : ℝ) :
    ¬ (∀ x : Fin 5 → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = maj x) := by
  intro hcomp
  exact maj5_no_three_fixable_witnesses
    (fun i => headOutput (h i))
    (fun i => headOutput_fixable (h i))
    (fun v => if (∑ i, w i * (if v i then (1 : ℝ) else 0)) + bias > 0
      then true else false)
    (funext hcomp)

/-- **Non-vacuity, head-level.** A concrete three-head family — three
    indicator heads at the all-true, all-false and one-hot points —
    fails against EVERY aggregator, not just affine readouts. -/
theorem maj5_three_indicator_heads_fail :
    ∀ agg : (Fin 3 → Bool) → Bool,
      (fun x : Fin 5 → Bool =>
        agg (fun i => headOutput
          (indicatorHead (![fun _ => true, fun _ => false,
            fun j => decide (j = 0)] i)) x))
      ≠ (maj : (Fin 5 → Bool) → Bool) :=
  fun agg => maj5_no_three_fixable_witnesses
    (fun i => headOutput (indicatorHead
      (![fun _ => true, fun _ => false, fun j => decide (j = 0)] i)))
    (fun _ => headOutput_fixable _) agg

/-- **Non-vacuity, witness-level.** The first three witnesses of the
    shipped optimal construction (`maj5W1, maj5W2, maj5W3`) cannot be
    completed to maj₅ by any aggregator: the fourth witness is genuinely
    necessary. -/
theorem maj5_first_three_witnesses_fail :
    ∀ agg : (Fin 3 → Bool) → Bool,
      (fun x => agg (fun i => ![maj5W1, maj5W2, maj5W3] i x))
      ≠ (maj : (Fin 5 → Bool) → Bool) := by
  intro agg
  apply maj5_no_three_fixable_witnesses
  intro i
  fin_cases i
  · exact maj5W1_fixable
  · exact maj5W2_fixable
  · exact maj5W3_fixable

end
