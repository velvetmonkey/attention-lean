import AttentionLean.Compute
import AttentionLean.Parity4Triple
import AttentionLean.Parity4Achieve
import Mathlib

noncomputable section
open Finset Classical

def parity4M : (Fin 4 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (xor (x 2) (x 3))

/-- For sums of distinct powers of 2, testBit recovers the function. -/
theorem sum16_testBit : ∀ (f : Fin 16 → Bool) (j : Fin 16),
    Nat.testBit (∑ i : Fin 16, if f i then 2 ^ i.val else 0) j.val = f j := by
  native_decide

theorem collision_exists_4 (d : ℕ) (h₁ h₂ h₃ : HardAttentionHead 4 d) :
    ∃ x y : Fin 4 → Bool,
      parity4M x ≠ parity4M y ∧
      headOutput h₁ x = headOutput h₁ y ∧
      headOutput h₂ x = headOutput h₂ y ∧
      headOutput h₃ x = headOutput h₃ y := by
  sorry

end
