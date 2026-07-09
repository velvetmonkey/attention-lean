/- SPDX-License-Identifier: MIT -/

/-
  AttentionLean.WitnessMaj7Bracket

  A kernel-clean bracket for strict majority on seven bits:
  four fixable witnesses are necessary, and six suffice.
-/

import AttentionLean.DecisionListHeads

open Classical

noncomputable section

/-! ## §1 Six witnesses -/

/-- First dictator witness. -/
def maj7W0 : (Fin 7 → Bool) → Bool :=
  fun x => x 0

/-- Second dictator witness. -/
def maj7W1 : (Fin 7 → Bool) → Bool :=
  fun x => x 1

/-- Five-bit block witness:
    `¬x₆ ∨ (¬x₂ ∧ ¬x₃ ∧ ¬x₄)`. -/
def maj7W2 : (Fin 7 → Bool) → Bool :=
  fun x => !(x 6) || (!(x 2) && !(x 3) && !(x 4))

/-- Five-bit block witness:
    `x₅ ∧ (x₂ ∨ x₃ ∨ x₄ ∨ x₆)`. -/
def maj7W3 : (Fin 7 → Bool) → Bool :=
  fun x => x 5 && (x 2 || x 3 || x 4 || x 6)

/-- Five-bit block witness:
    `x₄ ∧ (x₂ ∨ x₃)`. -/
def maj7W4 : (Fin 7 → Bool) → Bool :=
  fun x => x 4 && (x 2 || x 3)

/-- Five-bit block witness:
    `x₃ ∧ (x₂ ∨ (x₄ ∧ x₅ ∧ x₆))`. -/
def maj7W5 : (Fin 7 → Bool) → Bool :=
  fun x => x 3 && (x 2 || (x 4 && x 5 && x 6))

def maj7DL2 : DL 7 :=
  .node 6 false true
    (.node 2 true false
      (.node 3 true false
        (.node 4 false true (.const false))))

def maj7DL3 : DL 7 :=
  .node 5 false false
    (.node 2 true true
      (.node 3 true true
        (.node 4 true true
          (.node 6 true true (.const false)))))

def maj7DL4 : DL 7 :=
  .node 4 false false
    (.node 2 true true
      (.node 3 true true (.const false)))

def maj7DL5 : DL 7 :=
  .node 3 false false
    (.node 2 true true
      (.node 4 false false
        (.node 5 false false
          (.node 6 true true (.const false)))))

set_option maxRecDepth 8192 in
theorem maj7W0_fixable : Fixable maj7W0 := by
  unfold maj7W0
  exact dictator_fixable 0

set_option maxRecDepth 8192 in
theorem maj7W1_fixable : Fixable maj7W1 := by
  unfold maj7W1
  exact dictator_fixable 1

set_option maxRecDepth 8192 in
theorem maj7W2_fixable : Fixable maj7W2 := by
  refine fixable_congr (g := maj7W2) ?_ (dl_fixable maj7DL2)
  decide +revert

set_option maxRecDepth 8192 in
theorem maj7W3_fixable : Fixable maj7W3 := by
  refine fixable_congr (g := maj7W3) ?_ (dl_fixable maj7DL3)
  decide +revert

set_option maxRecDepth 8192 in
theorem maj7W4_fixable : Fixable maj7W4 := by
  refine fixable_congr (g := maj7W4) ?_ (dl_fixable maj7DL4)
  decide +revert

set_option maxRecDepth 8192 in
theorem maj7W5_fixable : Fixable maj7W5 := by
  refine fixable_congr (g := maj7W5) ?_ (dl_fixable maj7DL5)
  decide +revert

/-- The six witnesses as one vector. -/
def maj7Ws : Fin 6 → (Fin 7 → Bool) → Bool :=
  ![maj7W0, maj7W1, maj7W2, maj7W3, maj7W4, maj7W5]

theorem maj7Ws_fixable : ∀ i, Fixable (maj7Ws i) := by
  intro i
  fin_cases i
  · exact maj7W0_fixable
  · exact maj7W1_fixable
  · exact maj7W2_fixable
  · exact maj7W3_fixable
  · exact maj7W4_fixable
  · exact maj7W5_fixable

/-! ## §2 The finite aggregator -/

/-- The arbitrary Boolean aggregator.  The last four labels determine
    whether the five-bit tail has weight at least 2, 3, or 4; the first two
    labels are the two exposed dictator bits. -/
def maj7Agg (v : Fin 6 → Bool) : Bool :=
  let p := v 0
  let q := v 1
  let A := v 2
  let B := v 3
  let C := v 4
  let D := v 5
  let twoOfBCD := (B && C) || (B && D) || (C && D)
  let ge2 := !A || B || C || D
  let ge3 := (!A && (B || C || D)) || (A && twoOfBCD)
  let ge4 := (!A && twoOfBCD) || (A && B && C && D)
  (p && q && ge2) || (((p && !q) || (!p && q)) && ge3) ||
    (!p && !q && ge4)

/-- A seven-bit input from explicit bits. -/
def bits7 (b0 b1 b2 b3 b4 b5 b6 : Bool) : Fin 7 → Bool :=
  ![b0, b1, b2, b3, b4, b5, b6]

theorem bits7_eta (x : Fin 7 → Bool) :
    bits7 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) = x := by
  funext i
  fin_cases i <;> rfl

set_option maxRecDepth 8192 in
theorem maj7_eq_six_witness_combination_bits
    (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    maj7Agg (fun i => maj7Ws i (bits7 b0 b1 b2 b3 b4 b5 b6))
      = maj (bits7 b0 b1 b2 b3 b4 b5 b6) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    cases b4 <;> cases b5 <;> cases b6 <;> decide

/-- **The equality, kernel `decide` over all 128 cube points.** -/
theorem maj7_eq_six_witness_combination :
    (fun x => maj7Agg (fun i => maj7Ws i x))
      = (maj : (Fin 7 → Bool) → Bool) := by
  funext x
  rw [← bits7_eta x]
  exact maj7_eq_six_witness_combination_bits (x 0) (x 1) (x 2) (x 3)
    (x 4) (x 5) (x 6)

/-- **k(maj₇) ≤ 6**: six fixable witnesses compute strict majority on
    seven bits. -/
theorem maj7_computable_by_six_fixable :
    ∃ w : Fin 6 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 6 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj := by
  exact ⟨maj7Ws, maj7Ws_fixable, maj7Agg, maj7_eq_six_witness_combination⟩

/-! ## §3 Brackets -/

/-- **maj₇ witness bracket.** Six fixable witnesses suffice, and three
    cannot: the certificate lower rung gives `4 ≤ k_witness(maj₇)`. -/
theorem maj7_witness_bracket :
    (∃ w : Fin 6 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 6 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj) ∧
    (∀ w : Fin 3 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 3 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ maj) :=
  ⟨maj7_computable_by_six_fixable,
   fun w hfix agg => maj_needs_half_fixable_witnesses (by norm_num) w hfix agg⟩

/-- **maj₇ head bracket.** Via `heads_computability_iff_fixable_witnesses`,
    six hard-attention heads with an arbitrary Boolean aggregator suffice,
    and three do not. -/
theorem maj7_head_bracket :
    (∃ (d : ℕ) (h : Fin 6 → HardAttentionHead 7 d)
      (agg : (Fin 6 → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x)) = maj) ∧
    (∀ (d : ℕ) (h : Fin 3 → HardAttentionHead 7 d)
      (agg : (Fin 3 → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x)) ≠ maj) := by
  constructor
  · exact (heads_computability_iff_fixable_witnesses
      (T := (maj : (Fin 7 → Bool) → Bool))).mpr maj7_computable_by_six_fixable
  · intro d h agg hcomp
    exact maj_needs_half_fixable_witnesses (by norm_num)
      (fun i => headOutput (h i)) (fun i => headOutput_fixable (h i)) agg hcomp

#guard maj7W2 (fun _ => false) == true
#guard maj7W3 (fun _ => true) == true
#guard maj (fun i : Fin 7 => decide (i.val < 4)) == true
#guard maj (fun i : Fin 7 => decide (i.val < 3)) == false

end
