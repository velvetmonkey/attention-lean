/-
  AttentionLean.ParityAchieve

  W2-T5 — Achievability: `parityN` is computed by `2^(n-1)` hard-attention
  heads under a single thresholded affine readout (the odd-point indicator
  construction).

  Context. The originally briefed target — `parityN_achievable_with_N_heads`,
  i.e. n heads suffice — is FALSE at n = 3: an exhaustive, model-exact search
  over all 96 realizable single-head output functions (the priority-function
  class; the count matches `achievable3Raw` in `ParitySmall` exactly) against
  all 104 linear threshold functions on 3 bits finds 0 of 152,096 head
  triples computing parity3, while 4 = 2^(3-1) heads do (≥ 50 witnesses).
  See `scripts/parity_head_search.py`. This module proves the corrected
  general upper bound. Together with `parityN_requires_N_heads` the head
  complexity k(n) of parityN satisfies n ≤ k(n) ≤ 2^(n-1), both ends formal;
  at n = 2 the two bounds meet, so k(2) = 2 exactly. k(3) = 4 empirically
  (the 3-head impossibility is search evidence, not Lean — formalizing it
  needs the `native_decide` enumeration substrate this file deliberately
  avoids).

  Construction. One indicator head per odd-parity point `a`: scores are 1 on
  literals disagreeing with `a` and 0 on agreeing ones, so on `x ≠ a` the
  argmax lands on the least disagreeing index and reads −1 (head silent),
  while on `x = a` all scores tie at 0, the min-index tie-break selects
  position 0, and the head reads +1 (head fires). Exactly one indicator
  fires on an odd input, none on an even one, so unit weights and zero bias
  give `parityN` through the threshold.

  Imports `Defs` + `ParityN` only — none of the `Parity4*` enumeration
  substrate. No `native_decide`. Axioms: `propext, Classical.choice,
  Quot.sound`.
-/
import AttentionLean.Defs
import AttentionLean.ParityN

open Finset Classical

noncomputable section

/-! ## The odd-point indicator head -/

/-- The indicator head for the point `a` (internal dimension 2): identity
    score matrices, coordinate-projection query and value vectors, token
    embedding `(score, read)` with score 1 exactly on literals disagreeing
    with `a`, and read value +1 exactly at the literal `(0, a 0)`. -/
def indicatorHead {n : ℕ} [NeZero n] (a : Fin n → Bool) : HardAttentionHead n 2 where
  W_Q := 1
  W_K := 1
  query := ![1, 0]
  tok := fun i b => ![if b = a i then 0 else 1,
                      if i = 0 ∧ b = a i then 1 else -1]
  W_V := ![0, 1]
  readout_w := 1
  readout_b := 0

lemma indicator_scoreVal {n : ℕ} [NeZero n] (a : Fin n → Bool) (i : Fin n) (b : Bool) :
    scoreVal (indicatorHead a) i b = if b = a i then 0 else 1 := by
  simp [scoreVal, indicatorHead, Matrix.one_mulVec, dotProduct, Fin.sum_univ_two]

lemma indicator_readVal {n : ℕ} [NeZero n] (a : Fin n → Bool) (i : Fin n) (b : Bool) :
    readVal (indicatorHead a) i b = if i = 0 ∧ b = a i then 1 else -1 := by
  simp [readVal, indicatorHead, dotProduct, Fin.sum_univ_two]

/-- On its own point the indicator head fires: all scores tie at 0, the
    min-index tie-break selects position 0, and the read there is +1. -/
lemma indicatorHead_output_self {n : ℕ} [NeZero n] (a : Fin n → Bool) :
    headOutput (indicatorHead a) a = true := by
  have hargmax : argmaxScore (attentionScore (indicatorHead a) a) = 0 :=
    argmaxScore_eq_of _ 0
      (fun j => by simp [attentionScore_eq_scoreVal, indicator_scoreVal])
      (fun j _ => Fin.zero_le j)
  simp only [headOutput, hargmax, indicator_readVal]
  norm_num [indicatorHead]

/-- Off its point the indicator head is silent: the argmax is the least
    disagreeing index, whose read is −1. -/
lemma indicatorHead_output_ne {n : ℕ} [NeZero n] (a x : Fin n → Bool)
    (hne : x ≠ a) : headOutput (indicatorHead a) x = false := by
  have hdis : (univ.filter fun j => x j ≠ a j).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra hemp
    push_neg at hemp
    exact hne (funext fun j => hemp j (mem_univ j))
  set j0 := (univ.filter fun j => x j ≠ a j).min' hdis with hj0def
  have hj0mem : j0 ∈ univ.filter fun j => x j ≠ a j := Finset.min'_mem _ _
  have hj0ne : x j0 ≠ a j0 := (Finset.mem_filter.mp hj0mem).2
  have hargmax : argmaxScore (attentionScore (indicatorHead a) x) = j0 := by
    apply argmaxScore_eq_of
    · intro j
      simp only [attentionScore_eq_scoreVal, indicator_scoreVal]
      rw [if_neg hj0ne]
      split <;> norm_num
    · intro j hj
      simp only [attentionScore_eq_scoreVal, indicator_scoreVal] at hj
      rw [if_neg hj0ne] at hj
      have hjne : x j ≠ a j := by
        intro hc
        rw [if_pos hc] at hj
        norm_num at hj
      exact Finset.min'_le (univ.filter fun k => x k ≠ a k) j
        (Finset.mem_filter.mpr ⟨mem_univ j, hjne⟩)
  have hnot : ¬ (j0 = 0 ∧ x j0 = a j0) := fun hc => hj0ne hc.2
  simp only [headOutput, hargmax, indicator_readVal, if_neg hnot]
  norm_num [indicatorHead]

/-- **The indicator head computes point equality.** -/
theorem indicatorHead_computes {n : ℕ} [NeZero n] (a x : Fin n → Bool) :
    headOutput (indicatorHead a) x = (if x = a then true else false) := by
  by_cases hx : x = a
  · subst hx
    simp [indicatorHead_output_self]
  · rw [if_neg hx, indicatorHead_output_ne a x hx]

/-! ## Counting odd points -/

/-- There are exactly `2^(n-1)` odd-parity points: flipping bit 0 is a parity-
    reversing involution, so odd and even points are equinumerous and split
    the `2^n` cube evenly. -/
theorem card_odd_points {n : ℕ} [NeZero n] :
    (univ.filter fun a : Fin n → Bool => parityN a = true).card = 2^(n-1) := by
  have hflip : ∀ a : Fin n → Bool,
      Function.update (Function.update a 0 (!a 0)) 0
        (!(Function.update a 0 (!a 0) 0)) = a := by
    intro a
    funext j
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  have hbij :
      (univ.filter fun a : Fin n → Bool => parityN a = true).card
        = (univ.filter fun a : Fin n → Bool => ¬ parityN a = true).card :=
    Finset.card_bij'
      (fun a _ => Function.update a 0 (!a 0))
      (fun a _ => Function.update a 0 (!a 0))
      (fun a ha => by
        rw [Finset.mem_filter] at ha ⊢
        have h := parityN_update_ne a 0
        rw [ha.2] at h
        exact ⟨mem_univ _, h⟩)
      (fun a ha => by
        rw [Finset.mem_filter] at ha ⊢
        have h := parityN_update_ne a 0
        have hfalse : parityN a = false := by
          cases hpar : parityN a with
          | false => rfl
          | true => exact absurd hpar ha.2
        rw [hfalse] at h
        refine ⟨mem_univ _, ?_⟩
        cases hup : parityN (Function.update a 0 (!a 0)) with
        | true => rfl
        | false => exact absurd hup h)
      (fun a _ => hflip a)
      (fun a _ => hflip a)
  have hsplit :
      (univ.filter fun a : Fin n → Bool => parityN a = true).card
        + (univ.filter fun a : Fin n → Bool => ¬ parityN a = true).card
        = 2^n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  have hn : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))
  have hpow : 2^n = 2 * 2^(n-1) := by
    conv_lhs => rw [← hn]
    rw [pow_succ]
    ring
  omega

/-! ## The capstone -/

/-- **W2-T5 — `parityN` is achievable with `2^(n-1)` heads.** One indicator
    head per odd point, unit weights, zero bias: the readout shape is
    verbatim the positive complement of `parityN_requires_N_heads` at
    `k = 2^(n-1)`. -/
theorem parityN_achievable_with_exp_heads {n : ℕ} [NeZero n] :
    ∃ (h : Fin (2^(n-1)) → HardAttentionHead n 2)
      (w : Fin (2^(n-1)) → ℝ) (bias : ℝ),
      ∀ x : Fin n → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
         then true else false) = parityN x := by
  classical
  set odd : Finset (Fin n → Bool) := univ.filter (fun a => parityN a = true)
    with hodd
  have hcard : odd.card = 2^(n-1) := card_odd_points
  let e : Fin (2^(n-1)) ≃ {a // a ∈ odd} :=
    (finCongr hcard.symm).trans odd.equivFin.symm
  refine ⟨fun i => indicatorHead (e i).1, fun _ => 1, 0, ?_⟩
  intro x
  have hsum : (∑ i : Fin (2^(n-1)),
      (1 : ℝ) * (if headOutput (indicatorHead (e i).1) x then (1 : ℝ) else 0))
      = if parityN x = true then 1 else 0 := by
    calc ∑ i : Fin (2^(n-1)),
          (1 : ℝ) * (if headOutput (indicatorHead (e i).1) x then (1 : ℝ) else 0)
        = ∑ a : {a // a ∈ odd},
            (if headOutput (indicatorHead a.1) x then (1 : ℝ) else 0) := by
          rw [← Equiv.sum_comp e
            (fun a : {a // a ∈ odd} =>
              if headOutput (indicatorHead a.1) x then (1 : ℝ) else 0)]
          simp
      _ = ∑ a ∈ odd, (if headOutput (indicatorHead a) x then (1 : ℝ) else 0) :=
          Finset.sum_coe_sort odd
            (fun a => if headOutput (indicatorHead a) x then (1 : ℝ) else 0)
      _ = ∑ a ∈ odd, (if x = a then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [indicatorHead_computes]
          by_cases hxa : x = a <;> simp [hxa]
      _ = if x ∈ odd then 1 else 0 := Finset.sum_ite_eq odd x (fun _ => (1 : ℝ))
      _ = if parityN x = true then 1 else 0 := by
          simp only [hodd, Finset.mem_filter, mem_univ, true_and]
  rw [hsum]
  cases hp : parityN x with
  | true => norm_num
  | false => norm_num

/-- The `n = 2` instance: parity2 is achievable with `2^(2-1) = 2` heads.
    With `parityN_requires_N_heads` at `n = 2` (no single head computes
    parity2), the exact head complexity of parity2 is 2. -/
theorem parity2_achievable_with_two_heads :
    ∃ (h : Fin 2 → HardAttentionHead 2 2) (w : Fin 2 → ℝ) (bias : ℝ),
      ∀ x : Fin 2 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
         then true else false) = parityN x := by
  simpa using parityN_achievable_with_exp_heads (n := 2)

end
