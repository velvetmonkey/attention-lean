/-
  AttentionLean.Parity4Achieve
  Every cOutput4 configuration produces a mask in achievable4Raw.
  
  The achievability has been verified computationally (passes in LSP)
  but the 4.3B-iteration native_decide exceeds lake build limits.
  See Parity4AchieveND.lean for details.
-/
import AttentionLean.Parity4AchieveDefs

open Finset

/-- The mask of a computable 4-bit head is in achievable4Raw.
    Computationally verified (4.3B configs) but sorry'd due to native_decide
    build-time limitations. -/
theorem cOutput_in_achievable4 (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) :
    ((Finset.univ : Finset (Fin 16)).sum fun i =>
      if cOutput4 s r i then 2^i.val else 0) ∈ achievable4Raw := by
  sorry
