import AttentionLean.Compute
import AttentionLean.Parity4Triple
import AttentionLean.Parity4Achieve
import AttentionLean.ParitySmall
import Mathlib

noncomputable section
open Finset Classical

def parity4M : (Fin 4 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (xor (x 2) (x 3))

/-- For sums of distinct powers of 2, testBit recovers the function. -/
theorem sum16_testBit : ∀ (f : Fin 16 → Bool) (j : Fin 16),
    Nat.testBit (∑ i : Fin 16, if f i then 2 ^ i.val else 0) j.val = f j := by
  native_decide

private theorem encodeFin4Bool_decodeFin4 (i : Fin 16) :
    encodeFin4Bool (decodeFin4 i) = i := by
  fin_cases i <;> decide

private theorem mask_collision_4
    (m₁ m₂ m₃ : ℕ) (hm₁ : m₁ ∈ achievable4Raw)
    (hm₂ : m₂ ∈ achievable4Raw) (hm₃ : m₃ ∈ achievable4Raw) :
    ∃ e o : Fin 16, parity4M (decodeFin4 e) ≠ parity4M (decodeFin4 o) ∧
      m₁.testBit e.val = m₁.testBit o.val ∧
      m₂.testBit e.val = m₂.testBit o.val ∧
      m₃.testBit e.val = m₃.testBit o.val := by
  have h_collision : hasCollision4 m₁ m₂ m₃ = true := by
    have htv := every_triple_has_collision_4
    have h1 := List.forall_iff_forall_mem.mp htv m₁ hm₁
    have h2 := List.forall_iff_forall_mem.mp h1 m₂ hm₂
    exact List.forall_iff_forall_mem.mp h2 m₃ hm₃
  simp only [hasCollision4, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
             and_assoc] at h_collision
  obtain ⟨e_nat, he_mem, o_nat, ho_mem, hb1, hb2, hb3⟩ := h_collision
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he_mem ho_mem
  have he_lt : e_nat < 16 := by
    rcases he_mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have ho_lt : o_nat < 16 := by
    rcases ho_mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  refine ⟨⟨e_nat, he_lt⟩, ⟨o_nat, ho_lt⟩, ?_, hb1, hb2, hb3⟩
  rcases he_mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases ho_mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      decide +revert

theorem collision_exists_4 (d : ℕ) (h₁ h₂ h₃ : HardAttentionHead 4 d) :
    ∃ x y : Fin 4 → Bool,
      parity4M x ≠ parity4M y ∧
      headOutput h₁ x = headOutput h₁ y ∧
      headOutput h₂ x = headOutput h₂ y ∧
      headOutput h₃ x = headOutput h₃ y := by
  obtain ⟨s₁, r₁, hs₁⟩ := headOutput_eq_cOutput4 h₁
  obtain ⟨s₂, r₂, hs₂⟩ := headOutput_eq_cOutput4 h₂
  obtain ⟨s₃, r₃, hs₃⟩ := headOutput_eq_cOutput4 h₃
  obtain ⟨e, o, hpar, hb1, hb2, hb3⟩ := mask_collision_4
    ((Finset.univ : Finset (Fin 16)).sum fun i => if cOutput4 s₁ r₁ i then 2 ^ i.val else 0)
    ((Finset.univ : Finset (Fin 16)).sum fun i => if cOutput4 s₂ r₂ i then 2 ^ i.val else 0)
    ((Finset.univ : Finset (Fin 16)).sum fun i => if cOutput4 s₃ r₃ i then 2 ^ i.val else 0)
    (cOutput_in_achievable4 s₁ r₁)
    (cOutput_in_achievable4 s₂ r₂)
    (cOutput_in_achievable4 s₃ r₃)
  rw [sum16_testBit (cOutput4 s₁ r₁) e, sum16_testBit (cOutput4 s₁ r₁) o] at hb1
  rw [sum16_testBit (cOutput4 s₂ r₂) e, sum16_testBit (cOutput4 s₂ r₂) o] at hb2
  rw [sum16_testBit (cOutput4 s₃ r₃) e, sum16_testBit (cOutput4 s₃ r₃) o] at hb3
  refine ⟨decodeFin4 e, decodeFin4 o, hpar, ?_, ?_, ?_⟩
  · rw [hs₁ (decodeFin4 e), hs₁ (decodeFin4 o),
        encodeFin4Bool_decodeFin4, encodeFin4Bool_decodeFin4]
    exact hb1
  · rw [hs₂ (decodeFin4 e), hs₂ (decodeFin4 o),
        encodeFin4Bool_decodeFin4, encodeFin4Bool_decodeFin4]
    exact hb2
  · rw [hs₃ (decodeFin4 e), hs₃ (decodeFin4 o),
        encodeFin4Bool_decodeFin4, encodeFin4Bool_decodeFin4]
    exact hb3

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
