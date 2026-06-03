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

theorem parity4_requires_four_heads (d : ℕ)
    (h₁ h₂ h₃ : HardAttentionHead 4 d) (w₁ w₂ w₃ bias : ℝ) :
    ¬ (∀ x : Fin 4 → Bool,
      (if w₁ * (if headOutput h₁ x then (1 : ℝ) else 0) +
          w₂ * (if headOutput h₂ x then (1 : ℝ) else 0) +
          w₃ * (if headOutput h₃ x then (1 : ℝ) else 0) + bias > 0
       then true else false) = parity4M x) := by
  intro hcomp
  obtain ⟨x, y, hparity, hh1, hh2, hh3⟩ := collision_exists_4 d h₁ h₂ h₃
  have hx := hcomp x
  have hy := hcomp y
  simp only [hh1, hh2, hh3] at hx
  exact hparity (hx.symm.trans hy)

end
