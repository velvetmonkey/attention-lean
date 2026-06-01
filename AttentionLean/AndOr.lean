/-
  AttentionLean.AndOr
  Phase 2: AND and OR on 2 Boolean inputs are each computable
  by a single hard-attention head.
-/
import AttentionLean.Compute

open Finset Classical Matrix

noncomputable section

/-! ### The AND head (d = 2)

  Strategy: use dimension 0 for scores and dimension 1 for read values.
  W_Q = W_K = identity.
  Token embeddings:
    tok 0 false = ![2, 0]   -- high score, zero read
    tok 0 true  = ![0, 0]   -- low score, zero read
    tok 1 false = ![1, 0]   -- mid score, zero read
    tok 1 true  = ![1, 1]   -- mid score, one read

  Scores:  scoreVal 0 F = 2, scoreVal 0 T = 0, scoreVal 1 F = 1, scoreVal 1 T = 1
  Reads:   readVal 0 F = 0, readVal 0 T = 0, readVal 1 F = 0, readVal 1 T = 1
  readout_w = 1, readout_b = 0

  Behavior:
    (F,F): score 2≥1, attend 0, read 0 → output false  ✓
    (F,T): score 2≥1, attend 0, read 0 → output false  ✓
    (T,F): score 0<1, attend 1, read 0 → output false  ✓
    (T,T): score 0<1, attend 1, read 1 → output true   ✓
-/

def andHead : HardAttentionHead 2 2 where
  W_Q := 1
  W_K := 1
  query := ![1, 0]
  tok := fun i b => match i, b with
    | ⟨0, _⟩, false => ![2, 0]
    | ⟨0, _⟩, true  => ![0, 0]
    | ⟨1, _⟩, false => ![1, 0]
    | ⟨1, _⟩, true  => ![1, 1]
  W_V := ![0, 1]
  readout_w := 1
  readout_b := 0

/-
Score and read value lemmas
-/
theorem andHead_scoreVal_0_false : scoreVal andHead 0 false = 2 := by
  unfold scoreVal; norm_num [ dotProduct, Matrix.mulVec ] ;
  unfold andHead; norm_num;

theorem andHead_scoreVal_0_true : scoreVal andHead 0 true = 0 := by
  -- By definition of andHead, we know that scoreVal andHead 0 true = 0.
  unfold scoreVal andHead; norm_num [ Matrix.mulVec ]

theorem andHead_scoreVal_1_false : scoreVal andHead 1 false = 1 := by
  unfold scoreVal; norm_num [ dotProduct, Matrix.mulVec ] ;
  unfold andHead; norm_num;

theorem andHead_scoreVal_1_true : scoreVal andHead 1 true = 1 := by
  unfold scoreVal; norm_num [ dotProduct, Matrix.mulVec ] ;
  unfold andHead; norm_num;

theorem andHead_readVal_0_false : readVal andHead 0 false = 0 := by
  unfold readVal;
  unfold andHead; norm_num;

theorem andHead_readVal_0_true : readVal andHead 0 true = 0 := by
  unfold readVal; unfold andHead; norm_num [ Fin.sum_univ_succ ] ;

theorem andHead_readVal_1_false : readVal andHead 1 false = 0 := by
  unfold readVal; unfold andHead; norm_num [ Fin.sum_univ_succ ] ;

theorem andHead_readVal_1_true : readVal andHead 1 true = 1 := by
  unfold readVal; unfold andHead; norm_num [ Fin.sum_univ_succ, dotProduct ] ;

/-
AND on 2 Boolean inputs is computable by a single hard-attention head.
-/
theorem and_computes : Computes andHead (fun x : Fin 2 → Bool => x 0 && x 1) := by
  intro x;
  fin_cases x <;> simp +decide [ headOutput_two ];
  · simp +decide [ Multiset.Pi.cons ];
    split_ifs <;> norm_num [ andHead_scoreVal_0_false, andHead_scoreVal_0_true, andHead_scoreVal_1_false, andHead_scoreVal_1_true, andHead_readVal_0_false, andHead_readVal_0_true, andHead_readVal_1_false, andHead_readVal_1_true ] at *;
    · exact show 0 < ( 1 : ℝ ) + 0 by norm_num;
    · linarith [ andHead_scoreVal_0_false, andHead_scoreVal_0_true, andHead_scoreVal_1_false, andHead_scoreVal_1_true ];
  · -- By definition of `andHead`, we know that `readout_w = 1` and `readout_b = 0`.
    simp [Multiset.Pi.cons, andHead];
    unfold scoreVal readVal; norm_num [ Fin.sum_univ_succ, dotProduct ] ;
  · unfold andHead; simp +decide [ scoreVal, readVal ] ;
    simp +decide [ Multiset.Pi.cons ];
  · unfold andHead; norm_num [ dotProduct, Multiset.Pi.cons ] ;
    unfold scoreVal readVal; norm_num [ dotProduct, Matrix.mulVec ] ;

/-! ### The OR head (d = 2)

  Token embeddings:
    tok 0 false = ![0, 0]   -- low score, zero read
    tok 0 true  = ![2, 1]   -- high score, one read
    tok 1 false = ![1, 0]   -- mid score, zero read
    tok 1 true  = ![1, 1]   -- mid score, one read

  Scores:  scoreVal 0 F = 0, scoreVal 0 T = 2, scoreVal 1 F = 1, scoreVal 1 T = 1
  Reads:   readVal 0 F = 0, readVal 0 T = 1, readVal 1 F = 0, readVal 1 T = 1
  readout_w = 1, readout_b = 0

  Behavior:
    (F,F): score 0<1, attend 1, read 0 → output false  ✓
    (F,T): score 0<1, attend 1, read 1 → output true   ✓
    (T,F): score 2≥1, attend 0, read 1 → output true   ✓
    (T,T): score 2≥1, attend 0, read 1 → output true   ✓
-/

def orHead : HardAttentionHead 2 2 where
  W_Q := 1
  W_K := 1
  query := ![1, 0]
  tok := fun i b => match i, b with
    | ⟨0, _⟩, false => ![0, 0]
    | ⟨0, _⟩, true  => ![2, 1]
    | ⟨1, _⟩, false => ![1, 0]
    | ⟨1, _⟩, true  => ![1, 1]
  W_V := ![0, 1]
  readout_w := 1
  readout_b := 0

/-
Score and read value lemmas
-/
theorem orHead_scoreVal_0_false : scoreVal orHead 0 false = 0 := by
  unfold scoreVal; norm_num [ orHead ] ;

theorem orHead_scoreVal_0_true : scoreVal orHead 0 true = 2 := by
  unfold scoreVal; norm_num [ orHead ] ;

theorem orHead_scoreVal_1_false : scoreVal orHead 1 false = 1 := by
  unfold scoreVal; norm_num [ orHead ] ;

theorem orHead_scoreVal_1_true : scoreVal orHead 1 true = 1 := by
  unfold scoreVal; norm_num [ orHead ] ;

theorem orHead_readVal_0_false : readVal orHead 0 false = 0 := by
  unfold readVal orHead;
  norm_num [ dotProduct ]

theorem orHead_readVal_0_true : readVal orHead 0 true = 1 := by
  unfold readVal; norm_num [ orHead ] ;

theorem orHead_readVal_1_false : readVal orHead 1 false = 0 := by
  unfold readVal orHead; norm_num;

theorem orHead_readVal_1_true : readVal orHead 1 true = 1 := by
  unfold readVal; norm_num [ orHead ] ;

/-
OR on 2 Boolean inputs is computable by a single hard-attention head.
-/
set_option linter.unusedSimpArgs false in
theorem or_computes : Computes orHead (fun x : Fin 2 → Bool => x 0 || x 1) := by
  intro x;
  fin_cases x <;> simp +decide [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true, orHead_readVal_0_false, orHead_readVal_0_true, orHead_readVal_1_false, orHead_readVal_1_true, headOutput_two ];
  · simp +decide [ Multiset.Pi.cons ];
    unfold orHead; norm_num [ scoreVal, readVal ] ;
  · simp +decide [ Multiset.Pi.cons ];
    split_ifs <;> norm_num [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true, orHead_readVal_0_false, orHead_readVal_0_true, orHead_readVal_1_false, orHead_readVal_1_true ];
    · exact show 0 < ( 1 : ℝ ) + 0 by norm_num;
    · linarith [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true ];
    · grobner;
    · linarith;
  · simp +decide [ Multiset.Pi.cons ];
    split_ifs <;> norm_num [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true, orHead_readVal_0_false, orHead_readVal_0_true, orHead_readVal_1_false, orHead_readVal_1_true ];
    · linarith [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true ];
    · exact show 0 < ( 1 : ℝ ) + 0 by norm_num;
    · linarith [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true ];
    · linarith;
  · simp +decide [ Multiset.Pi.cons ];
    split_ifs <;> norm_num [ orHead_scoreVal_0_false, orHead_scoreVal_0_true, orHead_scoreVal_1_false, orHead_scoreVal_1_true, orHead_readVal_0_false, orHead_readVal_0_true, orHead_readVal_1_false, orHead_readVal_1_true ];
    · exact le_rfl;
    · exact le_rfl;
    · linarith;
    · linarith

end
