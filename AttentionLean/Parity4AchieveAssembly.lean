/-
  AttentionLean.Parity4AchieveAssembly

  4-way batch-split assembly for cOutput_in_achievable4.

    achieve_all              ← case-split on (r3f, r3t), discharged
                               by the 4 native_decide batches
    mask4Full_eq_sum         ← structural bridge: mask4Full's
                               16-term unrolled mask = ∑ cOutput4
                               (SKELETON PHASE: sorry-stubbed,
                               Phase 1 will prove via Fin.sum_univ_succ
                               + cWinner4 ↔ Bool-and reduction)
    cOutput_in_achievable4_assembled
                             ← apply inAch4_sound_raw to achieve_all
                               after rewriting through the bridge

  Re-exported by Parity4Achieve.lean so cOutput_in_achievable4 has a
  real proof (no sorry of its own; transitively rests on the 4 batch
  sorries + 1 bridge sorry in this skeleton).
-/
import AttentionLean.Parity4AchieveR3FF
import AttentionLean.Parity4AchieveR3FT
import AttentionLean.Parity4AchieveR3TF
import AttentionLean.Parity4AchieveR3TT

open Finset

/-- Full 4.3 B achievability, recomposed from the four (r3f, r3t) batches
    via a single Bool × Bool case-split. -/
theorem achieve_all :
    ∀ (s0f s0t s1f s1t s2f s2t s3f s3t : Fin 8)
      (r0f r0t r1f r1t r2f r2t r3f r3t : Bool),
    inAch4 (mask4Full s0f.val s0t.val s1f.val s1t.val s2f.val s2t.val s3f.val s3t.val
            r0f r0t r1f r1t r2f r2t r3f r3t) = true := by
  intros s0f s0t s1f s1t s2f s2t s3f s3t r0f r0t r1f r1t r2f r2t r3f r3t
  cases r3f <;> cases r3t
  · exact achieve_batch_r3_ff s0f s0t s1f s1t s2f s2t s3f s3t r0f r0t r1f r1t r2f r2t
  · exact achieve_batch_r3_ft s0f s0t s1f s1t s2f s2t s3f s3t r0f r0t r1f r1t r2f r2t
  · exact achieve_batch_r3_tf s0f s0t s1f s1t s2f s2t s3f s3t r0f r0t r1f r1t r2f r2t
  · exact achieve_batch_r3_tt s0f s0t s1f s1t s2f s2t s3f s3t r0f r0t r1f r1t r2f r2t

/-- Helper A: `cWinner4` (Prop `∧`) equals the Bool `&&` winner form used by `mask4Full`.
    Closes by `by_cases` on the 6 `≥`-comparisons → 64 leaves, each `simp_all [and_assoc]`. -/
private lemma cWinner4_eq_bool_form (s0 s1 s2 s3 : ℕ) :
    cWinner4 s0 s1 s2 s3 =
    (if s0 ≥ s1 && s0 ≥ s2 && s0 ≥ s3 then (0 : Fin 4)
     else if s1 ≥ s2 && s1 ≥ s3 then 1
     else if s2 ≥ s3 then 2 else 3) := by
  unfold cWinner4
  by_cases h01 : s0 ≥ s1 <;> by_cases h02 : s0 ≥ s2 <;> by_cases h03 : s0 ≥ s3 <;>
    by_cases h12 : s1 ≥ s2 <;> by_cases h13 : s1 ≥ s3 <;> by_cases h23 : s2 ≥ s3 <;>
    simp_all [and_assoc]

/-- Helper C: collapse the readout `if x then r k true else r k false` to `r k x`. -/
private lemma r_if_eq (r : Fin 4 → Bool → Bool) (k : Fin 4) (x : Bool) :
    (if x then r k true else r k false) = r k x := by
  cases x <;> rfl

/-- Helper D: a `Fin 4` match that just dispatches a single function = the function. -/
private lemma fin4_match_apply {α : Type*} (f : Fin 4 → α) (w : Fin 4) :
    (match w with
     | (0 : Fin 4) => f 0
     | (1 : Fin 4) => f 1
     | (2 : Fin 4) => f 2
     | (3 : Fin 4) => f 3) = f w := by
  fin_cases w <;> rfl

/-- Helper B: `cOutput4` at a `Fin 16` index expands to mask4Full's `g`-body form
    (Bool `&&` winner, `sc_k := if x_k then s_k_t else s_k_f`). -/
private lemma cOutput4_eq_g_form
    (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) (i : Fin 16) :
    cOutput4 s r i =
    (let sc0 := if decodeFin4 i 0 then (s 0 true).val else (s 0 false).val
     let sc1 := if decodeFin4 i 1 then (s 1 true).val else (s 1 false).val
     let sc2 := if decodeFin4 i 2 then (s 2 true).val else (s 2 false).val
     let sc3 := if decodeFin4 i 3 then (s 3 true).val else (s 3 false).val
     let w : Fin 4 :=
       if sc0 ≥ sc1 && sc0 ≥ sc2 && sc0 ≥ sc3 then 0
       else if sc1 ≥ sc2 && sc1 ≥ sc3 then 1
       else if sc2 ≥ sc3 then 2 else 3
     r w (decodeFin4 i w)) := by
  cases h0 : decodeFin4 i 0 <;> cases h1 : decodeFin4 i 1 <;>
    cases h2 : decodeFin4 i 2 <;> cases h3 : decodeFin4 i 3 <;>
    simp [cOutput4, cWinner4_eq_bool_form, h0, h1, h2, h3]

/-- Helper E: bridge mask4Full's per-branch match form to Helper B's `r w (decodeFin4 i w)`.
    Casts the winner ONCE for general `i` (4 cases) — the restructure that avoids 16×4 blowup. -/
private lemma match_eq_r_decode (r : Fin 4 → Bool → Bool) (i : Fin 16) (w : Fin 4) :
    (match w with
     | (0 : Fin 4) => if decodeFin4 i 0 then r 0 true else r 0 false
     | (1 : Fin 4) => if decodeFin4 i 1 then r 1 true else r 1 false
     | (2 : Fin 4) => if decodeFin4 i 2 then r 2 true else r 2 false
     | (3 : Fin 4) => if decodeFin4 i 3 then r 3 true else r 3 false) =
    r w (decodeFin4 i w) := by
  fin_cases w
  · cases h : decodeFin4 i 0 <;> simp [h]
  · cases h : decodeFin4 i 1 <;> simp [h]
  · cases h : decodeFin4 i 2 <;> simp [h]
  · cases h : decodeFin4 i 3 <;> simp [h]

/-- The per-bit contribution of `mask4Full`'s body (mirrors `mask4Full`'s `if g(decoded bits)`
    structure for a general `i : Fin 16`). The whole mask is `∑ i : Fin 16, mask4Full_term s r i`. -/
private def mask4Full_term (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) (i : Fin 16) : ℕ :=
  if (let x0 := decodeFin4 i 0
      let x1 := decodeFin4 i 1
      let x2 := decodeFin4 i 2
      let x3 := decodeFin4 i 3
      let sc0 := if x0 then (s 0 true).val else (s 0 false).val
      let sc1 := if x1 then (s 1 true).val else (s 1 false).val
      let sc2 := if x2 then (s 2 true).val else (s 2 false).val
      let sc3 := if x3 then (s 3 true).val else (s 3 false).val
      let w : Fin 4 :=
        if sc0 ≥ sc1 && sc0 ≥ sc2 && sc0 ≥ sc3 then 0
        else if sc1 ≥ sc2 && sc1 ≥ sc3 then 1
        else if sc2 ≥ sc3 then 2 else 3
      match w with
      | 0 => if x0 then r 0 true else r 0 false
      | 1 => if x1 then r 1 true else r 1 false
      | 2 => if x2 then r 2 true else r 2 false
      | 3 => if x3 then r 3 true else r 3 false) then 2 ^ i.val else 0

/-- Step 1: term-wise lemma. The winner is cast 4 ways ONCE for general `i`. -/
private lemma mask4Full_term_eq
    (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) (i : Fin 16) :
    mask4Full_term s r i = if cOutput4 s r i then 2 ^ i.val else 0 := by
  unfold mask4Full_term
  rw [cOutput4_eq_g_form]
  congr 1
  simp only [match_eq_r_decode]

/-- Helper F: expand a `Fin 16` sum to literal-index 16-term form. -/
private lemma sum_univ_fin16 (f : Fin 16 → ℕ) :
    (Finset.univ : Finset (Fin 16)).sum f =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 +
    f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 + f 15 := by
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring

set_option maxHeartbeats 8000000 in
/-- Structural bridge: mask4Full's 16-term unrolled mask coincides with the
    `Finset.sum`-of-`cOutput4` form used in `cOutput_in_achievable4`. -/
private theorem mask4Full_eq_sum
    (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) :
    mask4Full (s 0 false).val (s 0 true).val (s 1 false).val (s 1 true).val
              (s 2 false).val (s 2 true).val (s 3 false).val (s 3 true).val
              (r 0 false) (r 0 true) (r 1 false) (r 1 true)
              (r 2 false) (r 2 true) (r 3 false) (r 3 true) =
    (Finset.univ : Finset (Fin 16)).sum
      (fun i => if cOutput4 s r i then 2 ^ i.val else 0) := by
  -- Bridge via mask4Full_term: both sides equal ∑ i, mask4Full_term s r i.
  trans ((Finset.univ : Finset (Fin 16)).sum (mask4Full_term s r))
  · -- mask4Full ... = ∑ mask4Full_term: expand sum to 16 literal-index terms, unfold, match.
    rw [sum_univ_fin16 (mask4Full_term s r)]
    unfold mask4Full mask4Full_term
    simp [decodeFin4]
    rfl
  · -- ∑ mask4Full_term = ∑ if cOutput4 then 2^i else 0: pointwise via Step 1.
    exact Finset.sum_congr rfl (fun i _ => mask4Full_term_eq s r i)

/-- Every `cOutput4`-mask lies in `achievable4Raw`, assembled from
    the four batches and the bridge via `inAch4_sound_raw`. -/
theorem cOutput_in_achievable4_assembled
    (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) :
    ((Finset.univ : Finset (Fin 16)).sum fun i =>
      if cOutput4 s r i then 2 ^ i.val else 0) ∈ achievable4Raw := by
  apply inAch4_sound_raw
  rw [← mask4Full_eq_sum s r]
  exact achieve_all (s 0 false) (s 0 true) (s 1 false) (s 1 true)
                    (s 2 false) (s 2 true) (s 3 false) (s 3 true)
                    (r 0 false) (r 0 true) (r 1 false) (r 1 true)
                    (r 2 false) (r 2 true) (r 3 false) (r 3 true)
