/-
  AttentionLean.Parity4Achieve
  Every cOutput4 configuration produces a mask in achievable4Raw.

  Proof via 4-way batch split — see Parity4AchieveAssembly.lean
  (which case-splits on (r3f, r3t) and bridges mask4Full ↔ ∑ cOutput4).
-/
import AttentionLean.Parity4AchieveDefs
import AttentionLean.Parity4AchieveAssembly

open Finset

/-- The mask of a computable 4-bit head is in `achievable4Raw`. -/
theorem cOutput_in_achievable4 (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool) :
    ((Finset.univ : Finset (Fin 16)).sum fun i =>
      if cOutput4 s r i then 2^i.val else 0) ∈ achievable4Raw :=
  cOutput_in_achievable4_assembled s r
