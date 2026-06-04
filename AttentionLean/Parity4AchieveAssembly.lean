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

/-- Structural bridge: mask4Full's 16-term unrolled mask coincides with the
    `Finset.sum`-of-`cOutput4` form used in `cOutput_in_achievable4`.

    SKELETON PHASE: body sorry-stubbed. Provable by unfolding
    `Finset.sum_univ_succ` 16 times and `cWinner4 ↔ Bool-and` reduction
    on the winner computation; no enumeration over scores/readouts is
    required (the proof is purely structural, not 4.3 B iterations). -/
private theorem mask4Full_eq_sum
    (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) :
    mask4Full (s 0 false).val (s 0 true).val (s 1 false).val (s 1 true).val
              (s 2 false).val (s 2 true).val (s 3 false).val (s 3 true).val
              (r 0 false) (r 0 true) (r 1 false) (r 1 true)
              (r 2 false) (r 2 true) (r 3 false) (r 3 true) =
    (Finset.univ : Finset (Fin 16)).sum
      (fun i => if cOutput4 s r i then 2 ^ i.val else 0) := by
  sorry

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
