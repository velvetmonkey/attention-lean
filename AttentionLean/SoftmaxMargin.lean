/-
  AttentionLean.SoftmaxMargin
  SPDX-License-Identifier: MIT

  THE HARD → SOFT ATTENTION BRIDGE, at the decision-list score tables.

  `priorityDL_realizable` (DecisionListHeads) already shows the *argmax*
  (hard attention) over the `pscore`/`pread` tables computes any
  `PriorityDL.eval`. This module proves the *softmax* (soft attention)
  side over the SAME tables: for large enough inverse temperature `β`,
  the thresholded soft read has the SAME Boolean output as the hard
  decision list.

  HONEST SCOPE — read this. What is proved is THRESHOLD / sign
  AGREEMENT under a strictly positive score margin, which finite
  decision lists genuinely have (`γ = 1` in the live case, from the
  integer priority scores). What is NOT proved — and is FALSE at finite
  `β` — is exact equality of the internal soft-attention value with the
  hard selected read: a finite softmax puts positive mass on every
  position, so the soft read is a convex mixture, never the selected
  table entry. Chasing that equality is the weak-bridge trap; it is
  deliberately absent. This is the same discipline as the seal
  capability theorem's named residual: the bridge is real for Boolean
  decision-list OUTPUTS, and is labelled for exactly that.

  The argument is finite inequalities over `Real.exp` — no topology, no
  limits, no `native_decide`.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`, no `sorry`. Purely additive.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import AttentionLean.DecisionListHeads

open Finset Classical

noncomputable section

/-! ## §1 Finite softmax over a score table -/

/-- Softmax weight of position `i` at inverse temperature `β`. -/
noncomputable def softWeight {n : ℕ} [NeZero n] (β : ℝ) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (β * s i) / ∑ j, Real.exp (β * s j)

/-- Soft (softmax-weighted) read of a value table `r`. -/
noncomputable def softRead {n : ℕ} [NeZero n] (β : ℝ) (s r : Fin n → ℝ) : ℝ :=
  ∑ i, softWeight β s i * r i

/-- Threshold the soft read at 0 to a Boolean. -/
def softBool (z : ℝ) : Bool := if z > 0 then true else false

/-- Soft read specialized to an input `x` through per-coordinate score
    and read tables (the table-head form). -/
noncomputable def softReadInput {n : ℕ} [NeZero n] (β : ℝ) (s r : Fin n → Bool → ℝ)
    (x : Fin n → Bool) : ℝ :=
  softRead β (fun i => s i (x i)) (fun i => r i (x i))

/-! ## §2 Softmax weight basics -/

lemma sumExp_pos {n : ℕ} [NeZero n] (β : ℝ) (s : Fin n → ℝ) :
    0 < ∑ j, Real.exp (β * s j) :=
  Finset.sum_pos (fun i _ => Real.exp_pos _) univ_nonempty

lemma softWeight_pos {n : ℕ} [NeZero n] (β : ℝ) (s : Fin n → ℝ) (i : Fin n) :
    0 < softWeight β s i := by
  unfold softWeight
  exact div_pos (Real.exp_pos _) (sumExp_pos β s)

lemma softWeight_sum_eq_one {n : ℕ} [NeZero n] (β : ℝ) (s : Fin n → ℝ) :
    ∑ i, softWeight β s i = 1 := by
  unfold softWeight
  rw [← Finset.sum_div]
  exact div_self (sumExp_pos β s).ne'

/-- A soft read whose value table is constant `c` equals `c`. -/
lemma softRead_const {n : ℕ} [NeZero n] (β : ℝ) (s r : Fin n → ℝ) (c : ℝ)
    (hr : ∀ i, r i = c) : softRead β s r = c := by
  unfold softRead
  rw [Finset.sum_congr rfl (fun i _ => by rw [hr i]), ← Finset.sum_mul,
      softWeight_sum_eq_one, one_mul]

/-! ## §3 The margin bound (finite algebra over `Real.exp`) -/

/-- Under a score margin `s j + γ ≤ s winner`, a nonwinner's softmax
    weight is at most `exp(-βγ)` times the winner's. -/
lemma softWeight_ratio_le_of_margin {n : ℕ} [NeZero n] (β γ : ℝ) (s : Fin n → ℝ)
    (winner j : Fin n) (hβ : 0 < β) (hmargin : s j + γ ≤ s winner) :
    softWeight β s j ≤ Real.exp (-(β * γ)) * softWeight β s winner := by
  unfold softWeight
  rw [← mul_div_assoc]
  gcongr
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [hmargin, hβ.le]

/-- The total nonwinner softmax mass is bounded by
    `(card − 1) · exp(-βγ)` times the winner's weight. -/
lemma softWeight_nonwinner_mass_le_of_margin {n : ℕ} [NeZero n] (β γ : ℝ)
    (s : Fin n → ℝ) (winner : Fin n) (hβ : 0 < β)
    (hmargin : ∀ j, j ≠ winner → s j + γ ≤ s winner) :
    ∑ j ∈ univ.erase winner, softWeight β s j
      ≤ ((Fintype.card (Fin n) : ℝ) - 1)
          * (Real.exp (-(β * γ)) * softWeight β s winner) := by
  have hbound : ∀ j ∈ univ.erase winner,
      softWeight β s j ≤ Real.exp (-(β * γ)) * softWeight β s winner := by
    intro j hj
    exact softWeight_ratio_le_of_margin β γ s winner j hβ
      (hmargin j (Finset.mem_erase.1 hj).1)
  have hcard : ((univ.erase winner).card : ℝ) = (Fintype.card (Fin n) : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  calc ∑ j ∈ univ.erase winner, softWeight β s j
      ≤ ∑ _j ∈ univ.erase winner, Real.exp (-(β * γ)) * softWeight β s winner :=
        Finset.sum_le_sum hbound
    _ = ((univ.erase winner).card : ℝ)
          * (Real.exp (-(β * γ)) * softWeight β s winner) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card (Fin n) : ℝ) - 1)
          * (Real.exp (-(β * γ)) * softWeight β s winner) := by rw [hcard]

/-! ## §4 Winner dominance ⇒ soft-read sign -/

/-- If the winner's weight exceeds the total nonwinner mass and the
    winner reads `+1` with all reads `≥ −1`, the soft read is positive. -/
lemma softRead_pos_of_dominant {n : ℕ} [NeZero n] (β : ℝ) (s r : Fin n → ℝ) (w : Fin n)
    (hmass : ∑ j ∈ univ.erase w, softWeight β s j < softWeight β s w)
    (hrw : r w = 1) (hrb : ∀ j, -1 ≤ r j) :
    0 < softRead β s r := by
  have hsplit : softRead β s r
      = softWeight β s w * r w + ∑ j ∈ univ.erase w, softWeight β s j * r j := by
    unfold softRead
    exact (Finset.add_sum_erase univ (fun i => softWeight β s i * r i) (mem_univ w)).symm
  have hle : ∑ j ∈ univ.erase w, softWeight β s j * (-1 : ℝ)
      ≤ ∑ j ∈ univ.erase w, softWeight β s j * r j := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [softWeight_pos β s j, hrb j]
  rw [← Finset.sum_mul] at hle
  rw [hsplit, hrw, mul_one]
  nlinarith [hle, hmass]

/-- Dually: winner reads `−1`, all reads `≤ 1` ⇒ soft read is negative. -/
lemma softRead_neg_of_dominant {n : ℕ} [NeZero n] (β : ℝ) (s r : Fin n → ℝ) (w : Fin n)
    (hmass : ∑ j ∈ univ.erase w, softWeight β s j < softWeight β s w)
    (hrw : r w = -1) (hrb : ∀ j, r j ≤ 1) :
    softRead β s r < 0 := by
  have hsplit : softRead β s r
      = softWeight β s w * r w + ∑ j ∈ univ.erase w, softWeight β s j * r j := by
    unfold softRead
    exact (Finset.add_sum_erase univ (fun i => softWeight β s i * r i) (mem_univ w)).symm
  have hle : ∑ j ∈ univ.erase w, softWeight β s j * r j
      ≤ ∑ j ∈ univ.erase w, softWeight β s j * (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [softWeight_pos β s j, hrb j]
  rw [← Finset.sum_mul] at hle
  rw [hsplit, hrw]
  nlinarith [hle, hmass]

/-! ## §5 The abstract sign-agreement theorem (FROZEN) -/

/-- **Softmax realizes the argmax sign under a positive margin.** For a
    strictly positive score margin `γ` around a `winner`, once the
    inverse temperature `β` is large enough that
    `(card − 1) · exp(-βγ) < 1`, the thresholded soft read agrees with
    the sign of the winner's read (`want`). Finite-`β`, uniform over the
    input; NOT exact soft-value equality. -/
theorem softmax_margin_realizes_argmax_sign
    {n : ℕ} [NeZero n]
    (beta gamma : ℝ) (scores reads : Fin n → ℝ) (winner : Fin n) (want : Bool)
    (hbeta_pos : 0 < beta)
    (hgamma : 0 < gamma)
    (hbeta : ((Fintype.card (Fin n) : ℝ) - 1) * Real.exp (-(beta * gamma)) < 1)
    (hwin : ∀ j, j ≠ winner → scores j + gamma ≤ scores winner)
    (hread_win : reads winner = if want then 1 else -1)
    (hread_bound : ∀ j, -1 ≤ reads j ∧ reads j ≤ 1) :
    softBool (softRead beta scores reads) = want := by
  have hwpos := softWeight_pos beta scores winner
  have hmass : ∑ j ∈ univ.erase winner, softWeight beta scores j
      < softWeight beta scores winner := by
    have h5 := softWeight_nonwinner_mass_le_of_margin beta gamma scores winner
      hbeta_pos hwin
    have hkey : ((Fintype.card (Fin n) : ℝ) - 1)
          * (Real.exp (-(beta * gamma)) * softWeight beta scores winner)
        < softWeight beta scores winner := by
      have h := mul_lt_mul_of_pos_right hbeta hwpos
      calc ((Fintype.card (Fin n) : ℝ) - 1)
            * (Real.exp (-(beta * gamma)) * softWeight beta scores winner)
          = (((Fintype.card (Fin n) : ℝ) - 1) * Real.exp (-(beta * gamma)))
              * softWeight beta scores winner := by ring
        _ < 1 * softWeight beta scores winner := h
        _ = softWeight beta scores winner := one_mul _
    linarith [h5, hkey]
  cases want with
  | true =>
    have hpos : 0 < softRead beta scores reads :=
      softRead_pos_of_dominant beta scores reads winner hmass (by simpa using hread_win)
        (fun j => (hread_bound j).1)
    unfold softBool
    rw [if_pos hpos]
  | false =>
    have hneg : softRead beta scores reads < 0 :=
      softRead_neg_of_dominant beta scores reads winner hmass (by simpa using hread_win)
        (fun j => (hread_bound j).2)
    unfold softBool
    rw [if_neg (not_lt.2 hneg.le)]

/-! ## §6 Decision-list plumbing: the γ = 1 margin and the dead case -/

/-- Every priority read is `±1`. -/
lemma pread_eq_one_or_neg_one {n : ℕ} (l : List (Fin n × Bool × Bool)) (d : Bool)
    (i : Fin n) (b : Bool) : pread l d i b = 1 ∨ pread l d i b = -1 := by
  induction l with
  | nil =>
    show (if d then (1 : ℝ) else -1) = 1 ∨ (if d then (1 : ℝ) else -1) = -1
    cases d <;> norm_num
  | cons e t ih =>
    show (if i = e.1 ∧ b = e.2.1 then (if e.2.2 then (1 : ℝ) else -1) else pread t d i b) = 1
      ∨ (if i = e.1 ∧ b = e.2.1 then (if e.2.2 then (1 : ℝ) else -1) else pread t d i b) = -1
    by_cases h : i = e.1 ∧ b = e.2.1
    · rw [if_pos h]; cases e.2.2 <;> norm_num
    · rw [if_neg h]; exact ih

/-- Every priority score is a `ℕ`-cast (integer-valued). -/
lemma pscore_natCast {n : ℕ} (l : List (Fin n × Bool × Bool)) (i : Fin n) (b : Bool) :
    ∃ m : ℕ, pscore l i b = (m : ℝ) := by
  induction l with
  | nil => exact ⟨0, by simp [pscore]⟩
  | cons e t ih =>
    by_cases h : i = e.1 ∧ b = e.2.1
    · refine ⟨t.length + 1, ?_⟩
      show (if i = e.1 ∧ b = e.2.1 then ((t.length : ℝ) + 1) else pscore t i b) = _
      rw [if_pos h]; push_cast; ring
    · obtain ⟨m, hm⟩ := ih
      refine ⟨m, ?_⟩
      show (if i = e.1 ∧ b = e.2.1 then ((t.length : ℝ) + 1) else pscore t i b) = _
      rw [if_neg h]; exact hm

/-- Integer-valued scores turn a strict inequality into a `+1` margin. -/
lemma pscore_lt_succ_le {n : ℕ} (l : List (Fin n × Bool × Bool)) (i j : Fin n)
    (bi bj : Bool) (h : pscore l j bj < pscore l i bi) :
    pscore l j bj + 1 ≤ pscore l i bi := by
  obtain ⟨a, ha⟩ := pscore_natCast l j bj
  obtain ⟨b, hb⟩ := pscore_natCast l i bi
  rw [ha, hb] at h ⊢
  have hab : a < b := by exact_mod_cast h
  have : a + 1 ≤ b := hab
  exact_mod_cast this

/-- **The live-case γ = 1 margin.** In the live case, the priority
    winner beats every other coordinate's score by at least `1`. -/
lemma priorityDL_soft_margin_live {n : ℕ} (l : List (Fin n × Bool × Bool)) (d : Bool)
    (x : Fin n → Bool) (hlive : ∃ e ∈ l, x e.1 = e.2.1) :
    ∃ i : Fin n,
      (∀ j, j ≠ i → pscore l j (x j) + 1 ≤ pscore l i (x i)) ∧
      ((0 : ℝ) < pread l d i (x i) ↔ pevalList l d x = true) := by
  obtain ⟨i, hstrict, hiff⟩ := priority_live_winner l d x hlive
  exact ⟨i, fun j hj => pscore_lt_succ_le l i j (x i) (x j) (hstrict j hj), hiff⟩

/-- **The dead case.** With no live entry all reads are the default
    sign, so the soft read is exactly that sign. -/
lemma priorityDL_soft_all_dead {n : ℕ} [NeZero n] (β : ℝ)
    (l : List (Fin n × Bool × Bool)) (d : Bool) (x : Fin n → Bool)
    (hdead : ∀ e ∈ l, ¬ x e.1 = e.2.1) :
    softBool (softRead β (fun i => pscore l i (x i)) (fun i => pread l d i (x i)))
      = pevalList l d x := by
  rw [softRead_const β (fun i => pscore l i (x i)) (fun i => pread l d i (x i))
        (if d then 1 else -1) (fun i => pread_all_dead l d x hdead i),
      pevalList_all_dead l d x hdead]
  cases d <;> norm_num [softBool]

/-! ## §7 The decision-list bridge (FROZEN) -/

/-- **Softmax realizes any priority decision list.** For a large-enough
    inverse temperature `β` (`(card − 1) · exp(-β) < 1`), the
    thresholded soft read over the decision list's own `pscore`/`pread`
    tables computes `P.eval` on every input — the soft-attention
    counterpart of the landed hard-attention `priorityDL_realizable`.
    Boolean-output agreement at finite `β`, NOT exact soft-value
    equality (see the module header). -/
theorem softmax_margin_realizes_dl
    {n : ℕ} [NeZero n]
    (P : PriorityDL n) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hbeta : ((Fintype.card (Fin n) : ℝ) - 1) * Real.exp (-beta) < 1) :
    ∀ x : Fin n → Bool,
      softBool (softReadInput beta (pscore P.entries) (pread P.entries P.dflt) x)
        = P.eval x := by
  intro x
  unfold softReadInput
  by_cases hlive : ∃ e ∈ P.entries, x e.1 = e.2.1
  · obtain ⟨i, hmargin, hiff⟩ := priorityDL_soft_margin_live P.entries P.dflt x hlive
    have hbeta1 : ((Fintype.card (Fin n) : ℝ) - 1) * Real.exp (-(beta * 1)) < 1 := by
      rw [mul_one]; exact hbeta
    apply softmax_margin_realizes_argmax_sign beta 1
      (fun i => pscore P.entries i (x i))
      (fun i => pread P.entries P.dflt i (x i))
      i (P.eval x) hbeta_pos one_pos hbeta1
    · intro j hj
      exact hmargin j hj
    · show pread P.entries P.dflt i (x i) = if P.eval x then (1 : ℝ) else -1
      rcases pread_eq_one_or_neg_one P.entries P.dflt i (x i) with hp | hp
      · have hev : P.eval x = true := hiff.1 (by rw [hp]; norm_num)
        simp [hp, hev]
      · have hev : P.eval x = false := by
          cases hb : P.eval x with
          | false => rfl
          | true => exact absurd (hiff.2 hb) (by rw [hp]; norm_num)
        simp [hp, hev]
    · intro j
      rcases pread_eq_one_or_neg_one P.entries P.dflt j (x j) with hp | hp <;>
        refine ⟨?_, ?_⟩ <;> simp only [hp] <;> norm_num
  · push_neg at hlive
    exact priorityDL_soft_all_dead beta P.entries P.dflt x hlive

end
