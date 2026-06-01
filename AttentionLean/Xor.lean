/-
  AttentionLean.Xor
  Lower bound: no single hard-attention head with affine readout computes XOR.
-/
import AttentionLean.Compute

open Finset Classical Matrix

noncomputable section

/-- The XOR function on 2-bit inputs. -/
def xor2 : (Fin 2 → Bool) → Bool := fun x => xor (x 0) (x 1)

/-
No single hard-attention head (of any dimension `d`) computes XOR on 2-bit inputs.

    Proof sketch (4-point Boolean enumeration):
    The score at position `i` depends only on `x(i)` (by the structure of `attentionScore`).
    For the four inputs `(0,0), (0,1), (1,0), (1,1)`, consider the argmax winner and the
    affine readout. By case analysis on which position wins in each input, every assignment
    leads to a contradiction via `linarith` (either the same value is required to be both
    positive and non-positive, or the score decomposition forces an inconsistent ordering).
-/
theorem xor_not_single_head (d : ℕ) (head : HardAttentionHead 2 d) :
    ¬ Computes head xor2 := by
  -- Assume that the head computes XOR.
  by_contra h_contra
  have h00 := h_contra ![false, false]
  have h01 := h_contra ![false, true]
  have h10 := h_contra ![true, false]
  have h11 := h_contra ![true, true];
  unfold xor2 at *; simp_all +decide [ headOutput_two ] ;
  split_ifs at * <;> linarith!;

end