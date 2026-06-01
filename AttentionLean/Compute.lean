/-
  AttentionLean.Compute
  The `Computes` predicate and helper lemmas for `n = 2`.
-/
import AttentionLean.Defs

open Finset Classical

noncomputable section

variable {n d : ℕ}

/-- A head *computes* a Boolean function `f` when its output matches `f` on every input. -/
def Computes [NeZero n] (head : HardAttentionHead n d) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, headOutput head x = f x

/-! ### Specialisation lemmas for `n = 2` -/

/-
For `n = 2`, the argmax selects position 0 when score 0 ≥ score 1, else position 1.
-/
theorem argmaxScore_two (scores : Fin 2 → ℝ) :
    argmaxScore scores = if scores 0 ≥ scores 1 then (0 : Fin 2) else 1 := by
  split_ifs <;> simp_all +decide [argmaxScore];
  · refine' le_antisymm _ _ <;> simp +decide [ *, Finset.min' ];
    exact le_antisymm ( Finset.le_sup' ( fun x => scores x ) ( Finset.mem_univ 0 ) ) ( Finset.sup'_le _ _ fun x hx => by fin_cases x <;> aesop );
  · refine' le_antisymm _ _ <;> simp_all +decide [ Fin.univ_succ ];
    exact Finset.min'_le _ _ ( by simp +decide [ *, max_eq_right_of_lt ] )

/-- The `headOutput` for `n = 2`, fully unfolded. -/
theorem headOutput_two (head : HardAttentionHead 2 d) (x : Fin 2 → Bool) :
    headOutput head x =
      let w := if scoreVal head 0 (x 0) ≥ scoreVal head 1 (x 1) then (0 : Fin 2) else 1
      if head.readout_w * readVal head w (x w) + head.readout_b > 0 then true else false := by
  simp only [headOutput, attentionScore_eq_scoreVal, argmaxScore_two]

/-
Every `Fin 2 → Bool` is one of four cases.
-/
theorem fin2_bool_forall (P : (Fin 2 → Bool) → Prop)
    (h00 : P ![false, false])
    (h01 : P ![false, true])
    (h10 : P ![true, false])
    (h11 : P ![true, true]) :
    ∀ x, P x := by
  -- Since Fin 2 has only two elements, any function x can be represented as a pair (x 0, x 1). The possible pairs are (false, false), (false, true), (true, false), and (true, true). Each of these cases is covered by the hypotheses h00, h01, h10, and h11.
  intro x
  have h_cases : x = ![false, false] ∨ x = ![false, true] ∨ x = ![true, false] ∨ x = ![true, true] := by
    native_decide +revert;
  rcases h_cases with ( rfl | rfl | rfl | rfl ) <;> assumption

end