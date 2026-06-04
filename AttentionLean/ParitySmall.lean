/-
  AttentionLean.ParitySmall
  Parity on 3 bits cannot be computed by 2 hard-attention heads,
  and parity on 4 bits cannot be computed by 3 hard-attention heads,
  each with affine readout.
-/
import AttentionLean.Compute
import AttentionLean.Parity4Triple
import AttentionLean.Parity4Achieve
import Mathlib

open Finset Classical

/-! ## Part 1: Finite verification -/
section Computable3

/-- Computable winner for 3 positions (same tie-breaking as argmaxScore). -/
def cWinner3 (s0 s1 s2 : ℕ) : Fin 3 :=
  if s0 ≥ s1 ∧ s0 ≥ s2 then 0
  else if s1 ≥ s2 then 1
  else 2

/-- Decode index to Bool triple: bit j of i gives position j. -/
def decodeFin3 (i : Fin 8) : Fin 3 → Bool := fun j =>
  match j with
  | 0 => i.val % 2 == 1
  | 1 => (i.val / 2) % 2 == 1
  | 2 => (i.val / 4) % 2 == 1

/-- Computable output of a 3-bit head for input index i. -/
def cOutput3 (s : Fin 3 → Bool → Fin 6) (r : Fin 3 → Bool → Bool) (i : Fin 8) : Bool :=
  let x := decodeFin3 i
  let w := cWinner3 (s 0 (x 0)).val (s 1 (x 1)).val (s 2 (x 2)).val
  r w (x w)

/-- The 96 achievable 3-bit output functions as 8-bit masks. -/
def achievable3Raw : List ℕ :=
  [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21,
   31, 32, 34, 35, 42, 47, 48, 49, 50, 51, 55, 59, 63, 64, 68, 69,
   76, 79, 80, 81, 84, 85, 87, 93, 95, 112, 115, 117, 119, 127, 128,
   136, 138, 140, 143, 160, 162, 168, 170, 171, 174, 175, 176, 179,
   186, 187, 191, 192, 196, 200, 204, 205, 206, 207, 208, 213, 220,
   221, 223, 224, 234, 236, 238, 239, 240, 241, 242, 243, 244, 245,
   247, 248, 250, 251, 252, 253, 254, 255]

/-- Check collision: does some even-parity input match some odd-parity input? -/
def hasCollision3 (f1 f2 : ℕ) : Bool :=
  let evens := [0, 3, 5, 6]  -- even-parity inputs for parity3
  let odds := [1, 2, 4, 7]   -- odd-parity inputs
  evens.any fun e => odds.any fun o =>
    (f1 / 2^e) % 2 == (f1 / 2^o) % 2 && (f2 / 2^e) % 2 == (f2 / 2^o) % 2

/-- Every pair of achievable functions has a parity collision. -/
theorem every_pair_has_collision_3 :
    achievable3Raw.Forall (fun f1 =>
      achievable3Raw.Forall (fun f2 => hasCollision3 f1 f2 = true)) := by native_decide

/-- The 8-bit mask of a computable head is in achievable3Raw. -/
theorem cOutput_in_achievable :
    ∀ (s : Fin 3 → Bool → Fin 6) (r : Fin 3 → Bool → Bool),
    ((Finset.univ : Finset (Fin 8)).sum fun i =>
      if cOutput3 s r i then 2^i.val else 0) ∈ achievable3Raw := by native_decide

end Computable3



/-! The n=4 computable infrastructure is in Parity4Data/Triple/Achieve. -/

/- achievable4Raw etc. are now imported from Parity4Data -/

/-! ## Part 2: Formal proofs -/
noncomputable section

def parity3 : (Fin 3 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (x 2)
def parity4 : (Fin 4 → Bool) → Bool := fun x => xor (xor (x 0) (x 1)) (xor (x 2) (x 3))

theorem argmaxScore_three (scores : Fin 3 → ℝ) :
    argmaxScore scores =
      if scores 0 ≥ scores 1 ∧ scores 0 ≥ scores 2 then (0 : Fin 3)
      else if scores 1 ≥ scores 2 then 1
      else 2 := by
        split_ifs <;> simp_all +decide [argmaxScore];
        · refine' le_antisymm _ _ <;> simp +decide [Finset.min', *];
          exact le_antisymm (Finset.le_sup' _ (Finset.mem_univ _)) (Finset.sup'_le _ _ fun i _ => by fin_cases i <;> linarith!);
        · refine' le_antisymm _ _ <;> simp_all +decide [Fin.univ_succ];
          · simp +decide [Finset.min', Finset.mem_filter];
            cases max_cases (scores 0) (scores 1) <;> aesop;
          · grind;
        · refine' le_antisymm _ _ <;> simp_all +decide [Fin.univ_succ];
          · lia;
          · cases max_cases (scores 0) (max (scores 1) (scores 2)) <;> cases max_cases (scores 1) (scores 2) <;> linarith

theorem headOutput_three (head : HardAttentionHead 3 d) (x : Fin 3 → Bool) :
    headOutput head x =
      let s0 := scoreVal head 0 (x 0)
      let s1 := scoreVal head 1 (x 1)
      let s2 := scoreVal head 2 (x 2)
      let w : Fin 3 := if s0 ≥ s1 ∧ s0 ≥ s2 then 0
               else if s1 ≥ s2 then 1 else 2
      if head.readout_w * readVal head w (x w) + head.readout_b > 0 then true else false := by
  simp only [headOutput, attentionScore_eq_scoreVal, argmaxScore_three]

theorem headOutput_stable (head : HardAttentionHead 3 d)
    (x y : Fin 3 → Bool) (j : Fin 3)
    (hdiff : ∀ i : Fin 3, i ≠ j → x i = y i)
    (hwx : argmaxScore (fun i => attentionScore head x i) ≠ j)
    (hwy : argmaxScore (fun i => attentionScore head y i) ≠ j) :
    headOutput head x = headOutput head y := by
      revert j x y;
      simp +decide [headOutput, argmaxScore_three];
      grind

/-! ### Ranking lemma -/

/-
For any k real numbers, the rank function (counting values strictly less)
    preserves ≥. This maps reals to {0, ..., k-1}.
-/
theorem rank_preserves_ge {k : ℕ} (v : Fin k → ℝ) :
    ∃ n : Fin k → ℕ,
      (∀ i, n i < k) ∧
      (∀ i j, v i ≥ v j ↔ n i ≥ n j) := by
        by_contra! h_contra;
        -- Let's choose any $k$ real numbers and derive a contradiction.
        set S : Finset ℝ := Finset.image v Finset.univ with hS_def;
        -- Since $S$ is a finite set of real numbers, we can order its elements.
        obtain ⟨s, hs⟩ : ∃ s : Fin (Finset.card S) → ℝ, StrictMono s ∧ ∀ i, s i ∈ S := by
          exact ⟨ fun i => S.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => Finset.orderEmbOfFin_mem _ _ _ ⟩;
        -- Define the rank function n based on the order of elements in S.
        obtain ⟨n, hn⟩ : ∃ n : Fin k → Fin (Finset.card S), ∀ i, v i = s (n i) := by
          have h_rank : ∀ i, ∃ j : Fin (Finset.card S), v i = s j := by
            intro i
            have h_exists_j : v i ∈ Finset.image s Finset.univ := by
              have h_exists_j : Finset.image s Finset.univ = S := by
                exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hs.2 i ) ( by rw [ Finset.card_image_of_injective _ hs.1.injective, Finset.card_fin ] );
              exact h_exists_j.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
            rw [ Finset.mem_image ] at h_exists_j; obtain ⟨ j, _, hj ⟩ := h_exists_j; exact ⟨ j, hj.symm ⟩ ;
          exact ⟨ fun i => Classical.choose ( h_rank i ), fun i => Classical.choose_spec ( h_rank i ) ⟩;
        obtain ⟨ i, j, hij ⟩ := h_contra ( fun i => n i |> Fin.val ) ( fun i => lt_of_lt_of_le ( Fin.is_lt _ ) ( by simpa using Finset.card_image_le.trans ( by simpa ) ) ) ; simp_all +decide [ hs.1.le_iff_le ] ;
        exact hij.elim ( fun h => h.2.not_ge h.1 ) fun h => h.1.not_ge <| hs.1.monotone h.2

/-! ### Bridge: headOutput matches computable model -/

/-- Encode Fin 3 → Bool as Fin 8. -/
def encodeFin3Bool (x : Fin 3 → Bool) : Fin 8 :=
  ⟨(if x 0 then 1 else 0) + 2 * (if x 1 then 1 else 0) + 4 * (if x 2 then 1 else 0),
   by cases x 0 <;> cases x 1 <;> cases x 2 <;> simp <;> omega⟩

/-
Every headOutput on 3 bits matches some computable configuration.
-/
theorem headOutput_eq_cOutput (head : HardAttentionHead 3 d) :
    ∃ (s : Fin 3 → Bool → Fin 6) (r : Fin 3 → Bool → Bool),
      ∀ x : Fin 3 → Bool, headOutput head x = cOutput3 s r (encodeFin3Bool x) := by
        have := @rank_preserves_ge;
        obtain ⟨n, hn⟩ := @this 6 (fun i => if i = 0 then scoreVal head 0 false else if i = 1 then scoreVal head 0 true else if i = 2 then scoreVal head 1 false else if i = 3 then scoreVal head 1 true else if i = 4 then scoreVal head 2 false else scoreVal head 2 true);
        refine' ⟨ fun i b => if i = 0 then if b = false then ⟨ n 0, by linarith [ hn.1 0 ] ⟩ else ⟨ n 1, by linarith [ hn.1 1 ] ⟩ else if i = 1 then if b = false then ⟨ n 2, by linarith [ hn.1 2 ] ⟩ else ⟨ n 3, by linarith [ hn.1 3 ] ⟩ else if i = 2 then if b = false then ⟨ n 4, by linarith [ hn.1 4 ] ⟩ else ⟨ n 5, by linarith [ hn.1 5 ] ⟩ else ⟨ 0, by norm_num ⟩, fun i b => head.readout_w * readVal head i b + head.readout_b > 0, _ ⟩;
        intro x;
        rw [ headOutput_three, cOutput3 ];
        unfold cWinner3 decodeFin3 encodeFin3Bool;
        grind

/-! ### Collision lemma -/

theorem collision_exists_3 (d : ℕ) (h₁ h₂ : HardAttentionHead 3 d) :
    ∃ x y : Fin 3 → Bool,
      parity3 x ≠ parity3 y ∧
      headOutput h₁ x = headOutput h₁ y ∧
      headOutput h₂ x = headOutput h₂ y := by
        -- By the bridge lemma, there exist integer score configurations (s₁, r₁) and (s₂, r₂) such that headOutput h₁ x = cOutput3 s₁ r₁ (encodeFin3Bool x) and headOutput h₂ x = cOutput3 s₂ r₂ (encodeFin3Bool x).
        obtain ⟨s₁, r₁, hs₁⟩ := headOutput_eq_cOutput h₁
        obtain ⟨s₂, r₂, hs₂⟩ := headOutput_eq_cOutput h₂;
        -- By the finite verification lemma, there exist even and odd inputs e and o such that the masks m₁ and m₂ have the same bits at positions e and o.
        obtain ⟨e, o, he, ho, h_eq⟩ : ∃ e o : Fin 8, parity3 (decodeFin3 e) ≠ parity3 (decodeFin3 o) ∧ (cOutput3 s₁ r₁ e = cOutput3 s₁ r₁ o) ∧ (cOutput3 s₂ r₂ e = cOutput3 s₂ r₂ o) := by
          have h_mask_collision : ∀ (m₁ m₂ : ℕ), m₁ ∈ achievable3Raw → m₂ ∈ achievable3Raw → ∃ e o : Fin 8, parity3 (decodeFin3 e) ≠ parity3 (decodeFin3 o) ∧ (m₁ / 2^e.val) % 2 = (m₁ / 2^o.val) % 2 ∧ (m₂ / 2^e.val) % 2 = (m₂ / 2^o.val) % 2 := by
            intros m₁ m₂ hm₁ hm₂
            have h_collision : hasCollision3 m₁ m₂ = true := by
              have := every_pair_has_collision_3;
              rw [ List.forall_iff_forall_mem ] at this;
              exact List.forall_iff_forall_mem.mp ( this m₁ hm₁ ) m₂ hm₂;
            all_goals revert m₁; revert m₂; native_decide;
          obtain ⟨ e, o, h₁, h₂, h₃ ⟩ := h_mask_collision ( ( Finset.univ : Finset ( Fin 8 ) ).sum fun i => if cOutput3 s₁ r₁ i then 2 ^ i.val else 0 ) ( ( Finset.univ : Finset ( Fin 8 ) ).sum fun i => if cOutput3 s₂ r₂ i then 2 ^ i.val else 0 ) ( cOutput_in_achievable s₁ r₁ ) ( cOutput_in_achievable s₂ r₂ ) ; use e, o; simp_all +decide [ Finset.sum_ite ] ;
          have h_bit_eq : ∀ (m : ℕ) (i : Fin 8), (m / 2^i.val) % 2 = if m.testBit i.val then 1 else 0 := by
            grind;
          simp_all +decide [ Finset.sum_ite ];
          have h_bit_eq : ∀ (s : Finset (Fin 8)), (∀ x ∈ s, x.val < 8) → ∀ (i : Fin 8), (∑ x ∈ s, 2 ^ x.val).testBit i.val = (i ∈ s) := by
            native_decide +revert;
          grind;
        use decodeFin3 e, decodeFin3 o;
        simp_all +decide [ encodeFin3Bool, decodeFin3 ];
        fin_cases e <;> fin_cases o <;> trivial

/-! ### Main theorems -/

theorem parity3_requires_three_heads (d : ℕ)
    (h₁ h₂ : HardAttentionHead 3 d) (w₁ w₂ bias : ℝ) :
    ¬ (∀ x : Fin 3 → Bool,
      (if w₁ * (if headOutput h₁ x then (1 : ℝ) else 0) +
          w₂ * (if headOutput h₂ x then (1 : ℝ) else 0) + bias > 0
       then true else false) = parity3 x) := by
  intro hcomp
  obtain ⟨x, y, hparity, hh1, hh2⟩ := collision_exists_3 d h₁ h₂
  have hx := hcomp x
  have hy := hcomp y
  simp only [hh1, hh2] at hx
  exact hparity (hx.symm.trans hy)

/-! ### n=4 structural lemmas -/

theorem argmaxScore_four (scores : Fin 4 → ℝ) :
    argmaxScore scores =
      if scores 0 ≥ scores 1 ∧ scores 0 ≥ scores 2 ∧ scores 0 ≥ scores 3 then (0 : Fin 4)
      else if scores 1 ≥ scores 2 ∧ scores 1 ≥ scores 3 then 1
      else if scores 2 ≥ scores 3 then 2
      else 3 := by
        split_ifs <;> simp_all +decide [ argmaxScore ];
        · refine' le_antisymm _ _ <;> simp +decide [ Finset.min', * ];
          exact le_antisymm ( Finset.le_sup' _ ( Finset.mem_univ _ ) ) ( Finset.sup'_le _ _ fun i _ => by fin_cases i <;> linarith! );
        · refine' le_antisymm _ _ <;> simp_all +decide [ Finset.min', Finset.mem_filter ];
          · simp +decide [ Fin.univ_succ ];
            grind;
          · grind +suggestions;
        · refine' le_antisymm _ _ <;> simp_all +decide [ Fin.univ_succ ];
          · grind +suggestions;
          · grind;
        · refine' le_antisymm _ _ <;> simp +decide [ Finset.min', * ];
          · simp +decide [ Fin.univ_succ ];
            grind;
          · grind +suggestions

theorem headOutput_four (head : HardAttentionHead 4 d) (x : Fin 4 → Bool) :
    headOutput head x =
      let s0 := scoreVal head 0 (x 0)
      let s1 := scoreVal head 1 (x 1)
      let s2 := scoreVal head 2 (x 2)
      let s3 := scoreVal head 3 (x 3)
      let w : Fin 4 := if s0 ≥ s1 ∧ s0 ≥ s2 ∧ s0 ≥ s3 then 0
               else if s1 ≥ s2 ∧ s1 ≥ s3 then 1
               else if s2 ≥ s3 then 2 else 3
      if head.readout_w * readVal head w (x w) + head.readout_b > 0 then true else false := by
  simp only [headOutput, attentionScore_eq_scoreVal, argmaxScore_four]

/-- Encode Fin 4 → Bool as Fin 16. -/
def encodeFin4Bool (x : Fin 4 → Bool) : Fin 16 :=
  ⟨(if x 0 then 1 else 0) + 2 * (if x 1 then 1 else 0) +
   4 * (if x 2 then 1 else 0) + 8 * (if x 3 then 1 else 0),
   by cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> simp <;> omega⟩

private theorem decodeFin4_encodeFin4Bool (x : Fin 4 → Bool) (j : Fin 4) :
    decodeFin4 (encodeFin4Bool x) j = x j := by
  fin_cases j <;> simp [decodeFin4, encodeFin4Bool] <;>
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> simp

private theorem cWinner4_of_iff {a0 a1 a2 a3 : ℝ} {b0 b1 b2 b3 : ℕ}
    (h01 : a0 ≥ a1 ↔ b0 ≥ b1) (h02 : a0 ≥ a2 ↔ b0 ≥ b2)
    (h03 : a0 ≥ a3 ↔ b0 ≥ b3) (h12 : a1 ≥ a2 ↔ b1 ≥ b2)
    (h13 : a1 ≥ a3 ↔ b1 ≥ b3) (h23 : a2 ≥ a3 ↔ b2 ≥ b3) :
    (if a0 ≥ a1 ∧ a0 ≥ a2 ∧ a0 ≥ a3 then (0 : Fin 4)
     else if a1 ≥ a2 ∧ a1 ≥ a3 then 1
     else if a2 ≥ a3 then 2 else 3) =
    cWinner4 b0 b1 b2 b3 := by
  unfold cWinner4; simp only [h01, h02, h03, h12, h13, h23]

theorem headOutput_eq_cOutput4 (head : HardAttentionHead 4 d) :
    ∃ (s : Fin 4 → Bool → Fin 8) (r : Fin 4 → Bool → Bool),
      ∀ x : Fin 4 → Bool, headOutput head x = cOutput4 s r (encodeFin4Bool x) := by
  have h_rank : ∃ n : Fin 4 → Bool → ℕ, (∀ j b, n j b < 8) ∧ (∀ j b j' b', scoreVal head j b ≥ scoreVal head j' b' ↔ n j b ≥ n j' b') := by
    convert rank_preserves_ge ( fun i : Fin 8 => scoreVal head ( Fin.mk ( i / 2 ) ( by fin_cases i <;> trivial ) ) ( if i % 2 = 0 then Bool.false else Bool.true ) ) using 1;
    constructor <;> rintro ⟨ n, hn₁, hn₂ ⟩;
    · exact ⟨ fun i => n ⟨ i / 2, by fin_cases i <;> trivial ⟩ ( if i % 2 = 0 then false else true ), fun i => hn₁ _ _, fun i j => hn₂ _ _ _ _ ⟩;
    · use fun j b => n ( if b then ⟨ 2 * j + 1, by fin_cases j <;> trivial ⟩ else ⟨ 2 * j, by fin_cases j <;> trivial ⟩ );
      simp_all +decide [ Fin.forall_fin_succ ];
  obtain ⟨ n, hn₁, hn₂ ⟩ := h_rank; use fun j b => ⟨ n j b, by linarith [ hn₁ j b ] ⟩ ; use fun j b => head.readout_w * readVal head j b + head.readout_b > 0; simp +decide [ cOutput4 ] ;
  intro x; rw [ headOutput_four ] ; simp +decide [ cWinner4, hn₂ ] ;
  simp +decide only [decodeFin4_encodeFin4Bool]

/- collision_exists_4 and parity4_requires_four_heads moved to Parity4Main.lean -/

end