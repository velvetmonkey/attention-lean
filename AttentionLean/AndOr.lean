/-
  AttentionLean.AndOr
  Constructive proofs that a single hard-attention head computes AND and OR on 2-bit inputs.
-/
import AttentionLean.Compute

open Finset Classical Matrix

noncomputable section

/-! ### AND head construction -/

/-- A hard-attention head that computes AND on `Fin 2 → Bool`.
    Strategy: score(i,b) = −b, so false-valued positions win the argmax.
    The readout then mirrors the value at the winning position. -/
def andHead : HardAttentionHead 2 1 where
  W_Q := 1
  W_K := 1
  query := ![(-1 : ℝ)]
  tok := fun _i b => if b then ![(1 : ℝ)] else ![(0 : ℝ)]
  W_V := ![(1 : ℝ)]
  readout_w := 1
  readout_b := -(1 / 2)

/-- The AND function on 2-bit inputs. -/
def and2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1

theorem and_one_head : Computes andHead and2 := by
  intro x;
  -- By definition of `andHead`, we know that `headOutput andHead x` is equal to `and2 x` for all `x`.
  simp [andHead, headOutput_two, and2];
  fin_cases x <;> simp +decide [ scoreVal, readVal ];
  · simp +decide [ Multiset.Pi.cons ];
    norm_num;
  · simp +decide [ Multiset.Pi.cons ];
  · simp +decide [ Multiset.Pi.cons ];
  · simp +decide [ Multiset.Pi.cons ]

/-! ### OR head construction -/

/-- A hard-attention head that computes OR on `Fin 2 → Bool`.
    Strategy: score(i,b) = b, so true-valued positions win the argmax.
    The readout mirrors the value at the winning position. -/
def orHead : HardAttentionHead 2 1 where
  W_Q := 1
  W_K := 1
  query := ![(1 : ℝ)]
  tok := fun _i b => if b then ![(1 : ℝ)] else ![(0 : ℝ)]
  W_V := ![(1 : ℝ)]
  readout_w := 1
  readout_b := -(1 / 2)

/-- The OR function on 2-bit inputs. -/
def or2 : (Fin 2 → Bool) → Bool := fun x => x 0 || x 1

theorem or_one_head : Computes orHead or2 := by
  intro x; fin_cases x <;> unfold orHead <;> unfold or2 <;> norm_num [ headOutput_two ] ;
  · unfold scoreVal; norm_num [ readVal, Multiset.Pi.cons ] ;
  · unfold scoreVal readVal; norm_num [ Multiset.Pi.cons ] ;
  · unfold scoreVal readVal; norm_num [ Multiset.Pi.cons ] ;
  · unfold scoreVal; norm_num [ readVal, Multiset.Pi.cons ] ;

end