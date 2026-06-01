/-
  AttentionLean.Xor
  Phase 2: XOR on 2 Boolean inputs is NOT computable by any single
  hard-attention head, regardless of embedding dimension.
-/
import AttentionLean.Compute

open Finset Classical

noncomputable section

/-- XOR on 2 Boolean inputs. -/
def xorFn : (Fin 2 → Bool) → Bool := fun x => xor (x 0) (x 1)

/-- Helper: extracting real-number facts from boolean-if equations -/
private theorem ite_true_eq_false {a : ℝ} :
    (if a > 0 then true else false) = false ↔ ¬ a > 0 := by
  split_ifs with h <;> simp [h]

private theorem ite_true_eq_true {a : ℝ} :
    (if a > 0 then true else false) = true ↔ a > 0 := by
  split_ifs with h <;> simp [h]

/-
XOR on 2 inputs cannot be computed by any single hard-attention head.
-/
theorem xor_not_computable (d : ℕ) (head : HardAttentionHead 2 d) :
    ¬ Computes head xorFn := by
  intro h;
  -- Let's unfold the definition of `Computes`.
  unfold Computes at h;
  simp_all +decide [ headOutput_two ];
  have h1 := h ![false, false]; have h2 := h ![false, true]; have h3 := h ![true, false]; have h4 := h ![true, true]; simp_all +decide [ xorFn ] ;
  split_ifs at * <;> linarith!;

end