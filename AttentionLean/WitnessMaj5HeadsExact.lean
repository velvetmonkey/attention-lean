/-
  AttentionLean.WitnessMaj5HeadsExact

  S1 — THE POSITIVE HALF AT THE HEAD LEVEL, and exactness:
  `maj5_head_number_exact` — four hard-attention heads with a
  thresholded affine readout compute strict majority on five bits, and
  three cannot (`maj5_requires_four_heads`, merged).

  THE CONSTRUCTION. Each shipped witness `maj5W1..maj5W4` is a
  five-literal decision list testing every coordinate exactly once, so
  it is realized by a `tableHead` (the `indicatorHead` pattern:
  identity score matrices, coordinate-projection query/value vectors,
  token embedding = (score, read)): give the list's literals strictly
  decreasing positive scores in list order, their complements score 0,
  and read values +1/−1 by branch output, −1 on complements (the
  default). On any input the argmax lands on the first live list
  literal, or — when the whole list misses — on the score-0 tie broken
  to position 0, whose read is the default. The aggregator
  `(v₀ ∧ v₁) ∨ v₂ ∨ v₃` of the witness theorem is the linear threshold
  `v₀ + v₁ + 2v₂ + 2v₃ > 3/2`.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`, no `sorry`. Purely additive.
-/
import AttentionLean.WitnessMaj5Heads

open Classical

noncomputable section

/-! ## §1 Heads with prescribed score/read tables -/

/-- A head with prescribed score and read tables (dimension 2) — the
    `indicatorHead` construction with both tables free. -/
def tableHead (s r : Fin 5 → Bool → ℝ) : HardAttentionHead 5 2 where
  W_Q := 1
  W_K := 1
  query := ![1, 0]
  tok := fun i b => ![s i b, r i b]
  W_V := ![0, 1]
  readout_w := 1
  readout_b := 0

lemma tableHead_score (s r : Fin 5 → Bool → ℝ) (i : Fin 5) (b : Bool) :
    scoreVal (tableHead s r) i b = s i b := by
  simp [scoreVal, tableHead, Matrix.one_mulVec, dotProduct,
    Fin.sum_univ_two]

lemma tableHead_read (s r : Fin 5 → Bool → ℝ) (i : Fin 5) (b : Bool) :
    readVal (tableHead s r) i b = r i b := by
  simp [readVal, tableHead, dotProduct, Fin.sum_univ_two]

/-- Output through a designated winner (weak version: needs the
    min-index side condition). -/
lemma tableHead_output_eq (s r : Fin 5 → Bool → ℝ) (x : Fin 5 → Bool)
    (i : Fin 5) (hmax : ∀ j, s j (x j) ≤ s i (x i))
    (hmin : ∀ j, s j (x j) = s i (x i) → i ≤ j) :
    headOutput (tableHead s r) x
      = (if r i (x i) > 0 then true else false) := by
  have hwin : argmaxScore (attentionScore (tableHead s r) x) = i :=
    argmaxScore_eq_of _ i
      (fun j => by
        simp only [attentionScore_eq_scoreVal, tableHead_score]
        exact hmax j)
      (fun j hj => by
        simp only [attentionScore_eq_scoreVal, tableHead_score] at hj
        exact hmin j hj)
  simp only [headOutput, hwin, tableHead_read]
  norm_num [tableHead]

/-- Output through a strictly maximal winner. -/
lemma tableHead_output_strict (s r : Fin 5 → Bool → ℝ) (x : Fin 5 → Bool)
    (i : Fin 5) (hmax : ∀ j, j ≠ i → s j (x j) < s i (x i)) :
    headOutput (tableHead s r) x
      = (if r i (x i) > 0 then true else false) := by
  apply tableHead_output_eq
  · intro j
    by_cases hji : j = i
    · rw [hji]
    · exact (hmax j hji).le
  · intro j hj
    by_cases hji : j = i
    · rw [hji]
    · exact absurd hj (ne_of_lt (hmax j hji))

/-! ## §2 The four decision-list heads -/

def w1s : Fin 5 → Bool → ℝ := fun i b =>
  if i = 0 then (if b then 0 else 10)
  else if i = 1 then (if b then 9 else 0)
  else if i = 2 then (if b then 0 else 7)
  else if i = 3 then (if b then 8 else 0)
  else (if b then 6 else 0)

def w1r : Fin 5 → Bool → ℝ := fun i b =>
  if b ∧ (i = 1 ∨ i = 3 ∨ i = 4) then 1 else -1

def w2s : Fin 5 → Bool → ℝ := fun i b =>
  if i = 0 then (if b then 0 else 10)
  else if i = 2 then (if b then 9 else 0)
  else if i = 4 then (if b then 8 else 0)
  else if i = 1 then (if b then 0 else 7)
  else (if b then 6 else 0)

def w2r : Fin 5 → Bool → ℝ := fun i b =>
  if b ∧ (i = 2 ∨ i = 3 ∨ i = 4) then 1 else -1

def w3s : Fin 5 → Bool → ℝ := fun i b =>
  if i = 0 then (if b then 10 else 0)
  else if i = 1 then (if b then 0 else 9)
  else if i = 3 then (if b then 0 else 8)
  else if i = 2 then (if b then 7 else 0)
  else (if b then 6 else 0)

def w3r : Fin 5 → Bool → ℝ := fun i b =>
  if b ∧ (i = 2 ∨ i = 4) then 1 else -1

def w4s : Fin 5 → Bool → ℝ := fun i b =>
  if i = 0 then (if b then 10 else 0)
  else if i = 2 then (if b then 0 else 9)
  else if i = 4 then (if b then 0 else 8)
  else if i = 1 then (if b then 7 else 0)
  else (if b then 6 else 0)

def w4r : Fin 5 → Bool → ℝ := fun i b =>
  if b ∧ (i = 1 ∨ i = 3) then 1 else -1

/-- The head for `maj5W1`. -/
theorem headW1_computes (x : Fin 5 → Bool) :
    headOutput (tableHead w1s w1r) x = maj5W1 x := by
  cases hx0 : x 0 with
  | false =>
      have hm : ∀ j, j ≠ (0 : Fin 5) → w1s j (x j) < w1s 0 (x 0) := by
        intro j hji
        rw [hx0]
        fin_cases j
        · exact absurd rfl hji
        · show w1s 1 (x 1) < w1s 0 false
          cases hxj : x 1 <;> norm_num [w1s, Fin.ext_iff]
        · show w1s 2 (x 2) < w1s 0 false
          cases hxj : x 2 <;> norm_num [w1s, Fin.ext_iff]
        · show w1s 3 (x 3) < w1s 0 false
          cases hxj : x 3 <;> norm_num [w1s, Fin.ext_iff]
        · show w1s 4 (x 4) < w1s 0 false
          cases hxj : x 4 <;> norm_num [w1s, Fin.ext_iff]
      rw [tableHead_output_strict w1s w1r x 0 hm, hx0]
      norm_num [w1r, maj5W1, hx0, Fin.ext_iff]
  | true =>
      cases hx1 : x 1 with
      | true =>
          have hm : ∀ j, j ≠ (1 : Fin 5) → w1s j (x j) < w1s 1 (x 1) := by
            intro j hji
            rw [hx1]
            fin_cases j
            · show w1s 0 (x 0) < w1s 1 true
              rw [hx0]
              norm_num [w1s, Fin.ext_iff]
            · exact absurd rfl hji
            · show w1s 2 (x 2) < w1s 1 true
              cases hxj : x 2 <;> norm_num [w1s, Fin.ext_iff]
            · show w1s 3 (x 3) < w1s 1 true
              cases hxj : x 3 <;> norm_num [w1s, Fin.ext_iff]
            · show w1s 4 (x 4) < w1s 1 true
              cases hxj : x 4 <;> norm_num [w1s, Fin.ext_iff]
          rw [tableHead_output_strict w1s w1r x 1 hm, hx1]
          norm_num [w1r, maj5W1, hx0, hx1, Fin.ext_iff]
      | false =>
          cases hx3 : x 3 with
          | true =>
              have hm : ∀ j, j ≠ (3 : Fin 5) → w1s j (x j) < w1s 3 (x 3) := by
                intro j hji
                rw [hx3]
                fin_cases j
                · show w1s 0 (x 0) < w1s 3 true
                  rw [hx0]
                  norm_num [w1s, Fin.ext_iff]
                · show w1s 1 (x 1) < w1s 3 true
                  rw [hx1]
                  norm_num [w1s, Fin.ext_iff]
                · show w1s 2 (x 2) < w1s 3 true
                  cases hxj : x 2 <;> norm_num [w1s, Fin.ext_iff]
                · exact absurd rfl hji
                · show w1s 4 (x 4) < w1s 3 true
                  cases hxj : x 4 <;> norm_num [w1s, Fin.ext_iff]
              rw [tableHead_output_strict w1s w1r x 3 hm, hx3]
              norm_num [w1r, maj5W1, hx0, hx1, hx3, Fin.ext_iff]
          | false =>
              cases hx2 : x 2 with
              | false =>
                  have hm : ∀ j, j ≠ (2 : Fin 5) → w1s j (x j) < w1s 2 (x 2) := by
                    intro j hji
                    rw [hx2]
                    fin_cases j
                    · show w1s 0 (x 0) < w1s 2 false
                      rw [hx0]
                      norm_num [w1s, Fin.ext_iff]
                    · show w1s 1 (x 1) < w1s 2 false
                      rw [hx1]
                      norm_num [w1s, Fin.ext_iff]
                    · exact absurd rfl hji
                    · show w1s 3 (x 3) < w1s 2 false
                      rw [hx3]
                      norm_num [w1s, Fin.ext_iff]
                    · show w1s 4 (x 4) < w1s 2 false
                      cases hxj : x 4 <;> norm_num [w1s, Fin.ext_iff]
                  rw [tableHead_output_strict w1s w1r x 2 hm, hx2]
                  norm_num [w1r, maj5W1, hx0, hx1, hx2, hx3, Fin.ext_iff]
              | true =>
                  cases hx4 : x 4 with
                  | true =>
                      have hm : ∀ j, j ≠ (4 : Fin 5) → w1s j (x j) < w1s 4 (x 4) := by
                        intro j hji
                        rw [hx4]
                        fin_cases j
                        · show w1s 0 (x 0) < w1s 4 true
                          rw [hx0]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 1 (x 1) < w1s 4 true
                          rw [hx1]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 2 (x 2) < w1s 4 true
                          rw [hx2]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 3 (x 3) < w1s 4 true
                          rw [hx3]
                          norm_num [w1s, Fin.ext_iff]
                        · exact absurd rfl hji
                      rw [tableHead_output_strict w1s w1r x 4 hm, hx4]
                      norm_num [w1r, maj5W1, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]
                  | false =>
                      have hm : ∀ j, w1s j (x j) ≤ w1s 0 (x 0) := by
                        intro j
                        rw [hx0]
                        fin_cases j
                        · show w1s 0 (x 0) ≤ w1s 0 true
                          rw [hx0]
                        · show w1s 1 (x 1) ≤ w1s 0 true
                          rw [hx1]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 2 (x 2) ≤ w1s 0 true
                          rw [hx2]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 3 (x 3) ≤ w1s 0 true
                          rw [hx3]
                          norm_num [w1s, Fin.ext_iff]
                        · show w1s 4 (x 4) ≤ w1s 0 true
                          rw [hx4]
                          norm_num [w1s, Fin.ext_iff]
                      rw [tableHead_output_eq w1s w1r x 0 hm (fun j _ => Fin.zero_le j), hx0]
                      norm_num [w1r, maj5W1, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]

/-- The head for `maj5W2`. -/
theorem headW2_computes (x : Fin 5 → Bool) :
    headOutput (tableHead w2s w2r) x = maj5W2 x := by
  cases hx0 : x 0 with
  | false =>
      have hm : ∀ j, j ≠ (0 : Fin 5) → w2s j (x j) < w2s 0 (x 0) := by
        intro j hji
        rw [hx0]
        fin_cases j
        · exact absurd rfl hji
        · show w2s 1 (x 1) < w2s 0 false
          cases hxj : x 1 <;> norm_num [w2s, Fin.ext_iff]
        · show w2s 2 (x 2) < w2s 0 false
          cases hxj : x 2 <;> norm_num [w2s, Fin.ext_iff]
        · show w2s 3 (x 3) < w2s 0 false
          cases hxj : x 3 <;> norm_num [w2s, Fin.ext_iff]
        · show w2s 4 (x 4) < w2s 0 false
          cases hxj : x 4 <;> norm_num [w2s, Fin.ext_iff]
      rw [tableHead_output_strict w2s w2r x 0 hm, hx0]
      norm_num [w2r, maj5W2, hx0, Fin.ext_iff]
  | true =>
      cases hx2 : x 2 with
      | true =>
          have hm : ∀ j, j ≠ (2 : Fin 5) → w2s j (x j) < w2s 2 (x 2) := by
            intro j hji
            rw [hx2]
            fin_cases j
            · show w2s 0 (x 0) < w2s 2 true
              rw [hx0]
              norm_num [w2s, Fin.ext_iff]
            · show w2s 1 (x 1) < w2s 2 true
              cases hxj : x 1 <;> norm_num [w2s, Fin.ext_iff]
            · exact absurd rfl hji
            · show w2s 3 (x 3) < w2s 2 true
              cases hxj : x 3 <;> norm_num [w2s, Fin.ext_iff]
            · show w2s 4 (x 4) < w2s 2 true
              cases hxj : x 4 <;> norm_num [w2s, Fin.ext_iff]
          rw [tableHead_output_strict w2s w2r x 2 hm, hx2]
          norm_num [w2r, maj5W2, hx0, hx2, Fin.ext_iff]
      | false =>
          cases hx4 : x 4 with
          | true =>
              have hm : ∀ j, j ≠ (4 : Fin 5) → w2s j (x j) < w2s 4 (x 4) := by
                intro j hji
                rw [hx4]
                fin_cases j
                · show w2s 0 (x 0) < w2s 4 true
                  rw [hx0]
                  norm_num [w2s, Fin.ext_iff]
                · show w2s 1 (x 1) < w2s 4 true
                  cases hxj : x 1 <;> norm_num [w2s, Fin.ext_iff]
                · show w2s 2 (x 2) < w2s 4 true
                  rw [hx2]
                  norm_num [w2s, Fin.ext_iff]
                · show w2s 3 (x 3) < w2s 4 true
                  cases hxj : x 3 <;> norm_num [w2s, Fin.ext_iff]
                · exact absurd rfl hji
              rw [tableHead_output_strict w2s w2r x 4 hm, hx4]
              norm_num [w2r, maj5W2, hx0, hx2, hx4, Fin.ext_iff]
          | false =>
              cases hx1 : x 1 with
              | false =>
                  have hm : ∀ j, j ≠ (1 : Fin 5) → w2s j (x j) < w2s 1 (x 1) := by
                    intro j hji
                    rw [hx1]
                    fin_cases j
                    · show w2s 0 (x 0) < w2s 1 false
                      rw [hx0]
                      norm_num [w2s, Fin.ext_iff]
                    · exact absurd rfl hji
                    · show w2s 2 (x 2) < w2s 1 false
                      rw [hx2]
                      norm_num [w2s, Fin.ext_iff]
                    · show w2s 3 (x 3) < w2s 1 false
                      cases hxj : x 3 <;> norm_num [w2s, Fin.ext_iff]
                    · show w2s 4 (x 4) < w2s 1 false
                      rw [hx4]
                      norm_num [w2s, Fin.ext_iff]
                  rw [tableHead_output_strict w2s w2r x 1 hm, hx1]
                  norm_num [w2r, maj5W2, hx0, hx1, hx2, hx4, Fin.ext_iff]
              | true =>
                  cases hx3 : x 3 with
                  | true =>
                      have hm : ∀ j, j ≠ (3 : Fin 5) → w2s j (x j) < w2s 3 (x 3) := by
                        intro j hji
                        rw [hx3]
                        fin_cases j
                        · show w2s 0 (x 0) < w2s 3 true
                          rw [hx0]
                          norm_num [w2s, Fin.ext_iff]
                        · show w2s 1 (x 1) < w2s 3 true
                          rw [hx1]
                          norm_num [w2s, Fin.ext_iff]
                        · show w2s 2 (x 2) < w2s 3 true
                          rw [hx2]
                          norm_num [w2s, Fin.ext_iff]
                        · exact absurd rfl hji
                        · show w2s 4 (x 4) < w2s 3 true
                          rw [hx4]
                          norm_num [w2s, Fin.ext_iff]
                      rw [tableHead_output_strict w2s w2r x 3 hm, hx3]
                      norm_num [w2r, maj5W2, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]
                  | false =>
                      have hm : ∀ j, w2s j (x j) ≤ w2s 0 (x 0) := by
                        intro j
                        rw [hx0]
                        fin_cases j
                        · show w2s 0 (x 0) ≤ w2s 0 true
                          rw [hx0]
                        · show w2s 1 (x 1) ≤ w2s 0 true
                          rw [hx1]
                          norm_num [w2s, Fin.ext_iff]
                        · show w2s 2 (x 2) ≤ w2s 0 true
                          rw [hx2]
                          norm_num [w2s, Fin.ext_iff]
                        · show w2s 3 (x 3) ≤ w2s 0 true
                          rw [hx3]
                          norm_num [w2s, Fin.ext_iff]
                        · show w2s 4 (x 4) ≤ w2s 0 true
                          rw [hx4]
                          norm_num [w2s, Fin.ext_iff]
                      rw [tableHead_output_eq w2s w2r x 0 hm (fun j _ => Fin.zero_le j), hx0]
                      norm_num [w2r, maj5W2, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]

/-- The head for `maj5W3`. -/
theorem headW3_computes (x : Fin 5 → Bool) :
    headOutput (tableHead w3s w3r) x = maj5W3 x := by
  cases hx0 : x 0 with
  | true =>
      have hm : ∀ j, j ≠ (0 : Fin 5) → w3s j (x j) < w3s 0 (x 0) := by
        intro j hji
        rw [hx0]
        fin_cases j
        · exact absurd rfl hji
        · show w3s 1 (x 1) < w3s 0 true
          cases hxj : x 1 <;> norm_num [w3s, Fin.ext_iff]
        · show w3s 2 (x 2) < w3s 0 true
          cases hxj : x 2 <;> norm_num [w3s, Fin.ext_iff]
        · show w3s 3 (x 3) < w3s 0 true
          cases hxj : x 3 <;> norm_num [w3s, Fin.ext_iff]
        · show w3s 4 (x 4) < w3s 0 true
          cases hxj : x 4 <;> norm_num [w3s, Fin.ext_iff]
      rw [tableHead_output_strict w3s w3r x 0 hm, hx0]
      norm_num [w3r, maj5W3, hx0, Fin.ext_iff]
  | false =>
      cases hx1 : x 1 with
      | false =>
          have hm : ∀ j, j ≠ (1 : Fin 5) → w3s j (x j) < w3s 1 (x 1) := by
            intro j hji
            rw [hx1]
            fin_cases j
            · show w3s 0 (x 0) < w3s 1 false
              rw [hx0]
              norm_num [w3s, Fin.ext_iff]
            · exact absurd rfl hji
            · show w3s 2 (x 2) < w3s 1 false
              cases hxj : x 2 <;> norm_num [w3s, Fin.ext_iff]
            · show w3s 3 (x 3) < w3s 1 false
              cases hxj : x 3 <;> norm_num [w3s, Fin.ext_iff]
            · show w3s 4 (x 4) < w3s 1 false
              cases hxj : x 4 <;> norm_num [w3s, Fin.ext_iff]
          rw [tableHead_output_strict w3s w3r x 1 hm, hx1]
          norm_num [w3r, maj5W3, hx0, hx1, Fin.ext_iff]
      | true =>
          cases hx3 : x 3 with
          | false =>
              have hm : ∀ j, j ≠ (3 : Fin 5) → w3s j (x j) < w3s 3 (x 3) := by
                intro j hji
                rw [hx3]
                fin_cases j
                · show w3s 0 (x 0) < w3s 3 false
                  rw [hx0]
                  norm_num [w3s, Fin.ext_iff]
                · show w3s 1 (x 1) < w3s 3 false
                  rw [hx1]
                  norm_num [w3s, Fin.ext_iff]
                · show w3s 2 (x 2) < w3s 3 false
                  cases hxj : x 2 <;> norm_num [w3s, Fin.ext_iff]
                · exact absurd rfl hji
                · show w3s 4 (x 4) < w3s 3 false
                  cases hxj : x 4 <;> norm_num [w3s, Fin.ext_iff]
              rw [tableHead_output_strict w3s w3r x 3 hm, hx3]
              norm_num [w3r, maj5W3, hx0, hx1, hx3, Fin.ext_iff]
          | true =>
              cases hx2 : x 2 with
              | true =>
                  have hm : ∀ j, j ≠ (2 : Fin 5) → w3s j (x j) < w3s 2 (x 2) := by
                    intro j hji
                    rw [hx2]
                    fin_cases j
                    · show w3s 0 (x 0) < w3s 2 true
                      rw [hx0]
                      norm_num [w3s, Fin.ext_iff]
                    · show w3s 1 (x 1) < w3s 2 true
                      rw [hx1]
                      norm_num [w3s, Fin.ext_iff]
                    · exact absurd rfl hji
                    · show w3s 3 (x 3) < w3s 2 true
                      rw [hx3]
                      norm_num [w3s, Fin.ext_iff]
                    · show w3s 4 (x 4) < w3s 2 true
                      cases hxj : x 4 <;> norm_num [w3s, Fin.ext_iff]
                  rw [tableHead_output_strict w3s w3r x 2 hm, hx2]
                  norm_num [w3r, maj5W3, hx0, hx1, hx2, hx3, Fin.ext_iff]
              | false =>
                  cases hx4 : x 4 with
                  | true =>
                      have hm : ∀ j, j ≠ (4 : Fin 5) → w3s j (x j) < w3s 4 (x 4) := by
                        intro j hji
                        rw [hx4]
                        fin_cases j
                        · show w3s 0 (x 0) < w3s 4 true
                          rw [hx0]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 1 (x 1) < w3s 4 true
                          rw [hx1]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 2 (x 2) < w3s 4 true
                          rw [hx2]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 3 (x 3) < w3s 4 true
                          rw [hx3]
                          norm_num [w3s, Fin.ext_iff]
                        · exact absurd rfl hji
                      rw [tableHead_output_strict w3s w3r x 4 hm, hx4]
                      norm_num [w3r, maj5W3, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]
                  | false =>
                      have hm : ∀ j, w3s j (x j) ≤ w3s 0 (x 0) := by
                        intro j
                        rw [hx0]
                        fin_cases j
                        · show w3s 0 (x 0) ≤ w3s 0 false
                          rw [hx0]
                        · show w3s 1 (x 1) ≤ w3s 0 false
                          rw [hx1]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 2 (x 2) ≤ w3s 0 false
                          rw [hx2]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 3 (x 3) ≤ w3s 0 false
                          rw [hx3]
                          norm_num [w3s, Fin.ext_iff]
                        · show w3s 4 (x 4) ≤ w3s 0 false
                          rw [hx4]
                          norm_num [w3s, Fin.ext_iff]
                      rw [tableHead_output_eq w3s w3r x 0 hm (fun j _ => Fin.zero_le j), hx0]
                      norm_num [w3r, maj5W3, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]

/-- The head for `maj5W4`. -/
theorem headW4_computes (x : Fin 5 → Bool) :
    headOutput (tableHead w4s w4r) x = maj5W4 x := by
  cases hx0 : x 0 with
  | true =>
      have hm : ∀ j, j ≠ (0 : Fin 5) → w4s j (x j) < w4s 0 (x 0) := by
        intro j hji
        rw [hx0]
        fin_cases j
        · exact absurd rfl hji
        · show w4s 1 (x 1) < w4s 0 true
          cases hxj : x 1 <;> norm_num [w4s, Fin.ext_iff]
        · show w4s 2 (x 2) < w4s 0 true
          cases hxj : x 2 <;> norm_num [w4s, Fin.ext_iff]
        · show w4s 3 (x 3) < w4s 0 true
          cases hxj : x 3 <;> norm_num [w4s, Fin.ext_iff]
        · show w4s 4 (x 4) < w4s 0 true
          cases hxj : x 4 <;> norm_num [w4s, Fin.ext_iff]
      rw [tableHead_output_strict w4s w4r x 0 hm, hx0]
      norm_num [w4r, maj5W4, hx0, Fin.ext_iff]
  | false =>
      cases hx2 : x 2 with
      | false =>
          have hm : ∀ j, j ≠ (2 : Fin 5) → w4s j (x j) < w4s 2 (x 2) := by
            intro j hji
            rw [hx2]
            fin_cases j
            · show w4s 0 (x 0) < w4s 2 false
              rw [hx0]
              norm_num [w4s, Fin.ext_iff]
            · show w4s 1 (x 1) < w4s 2 false
              cases hxj : x 1 <;> norm_num [w4s, Fin.ext_iff]
            · exact absurd rfl hji
            · show w4s 3 (x 3) < w4s 2 false
              cases hxj : x 3 <;> norm_num [w4s, Fin.ext_iff]
            · show w4s 4 (x 4) < w4s 2 false
              cases hxj : x 4 <;> norm_num [w4s, Fin.ext_iff]
          rw [tableHead_output_strict w4s w4r x 2 hm, hx2]
          norm_num [w4r, maj5W4, hx0, hx2, Fin.ext_iff]
      | true =>
          cases hx4 : x 4 with
          | false =>
              have hm : ∀ j, j ≠ (4 : Fin 5) → w4s j (x j) < w4s 4 (x 4) := by
                intro j hji
                rw [hx4]
                fin_cases j
                · show w4s 0 (x 0) < w4s 4 false
                  rw [hx0]
                  norm_num [w4s, Fin.ext_iff]
                · show w4s 1 (x 1) < w4s 4 false
                  cases hxj : x 1 <;> norm_num [w4s, Fin.ext_iff]
                · show w4s 2 (x 2) < w4s 4 false
                  rw [hx2]
                  norm_num [w4s, Fin.ext_iff]
                · show w4s 3 (x 3) < w4s 4 false
                  cases hxj : x 3 <;> norm_num [w4s, Fin.ext_iff]
                · exact absurd rfl hji
              rw [tableHead_output_strict w4s w4r x 4 hm, hx4]
              norm_num [w4r, maj5W4, hx0, hx2, hx4, Fin.ext_iff]
          | true =>
              cases hx1 : x 1 with
              | true =>
                  have hm : ∀ j, j ≠ (1 : Fin 5) → w4s j (x j) < w4s 1 (x 1) := by
                    intro j hji
                    rw [hx1]
                    fin_cases j
                    · show w4s 0 (x 0) < w4s 1 true
                      rw [hx0]
                      norm_num [w4s, Fin.ext_iff]
                    · exact absurd rfl hji
                    · show w4s 2 (x 2) < w4s 1 true
                      rw [hx2]
                      norm_num [w4s, Fin.ext_iff]
                    · show w4s 3 (x 3) < w4s 1 true
                      cases hxj : x 3 <;> norm_num [w4s, Fin.ext_iff]
                    · show w4s 4 (x 4) < w4s 1 true
                      rw [hx4]
                      norm_num [w4s, Fin.ext_iff]
                  rw [tableHead_output_strict w4s w4r x 1 hm, hx1]
                  norm_num [w4r, maj5W4, hx0, hx1, hx2, hx4, Fin.ext_iff]
              | false =>
                  cases hx3 : x 3 with
                  | true =>
                      have hm : ∀ j, j ≠ (3 : Fin 5) → w4s j (x j) < w4s 3 (x 3) := by
                        intro j hji
                        rw [hx3]
                        fin_cases j
                        · show w4s 0 (x 0) < w4s 3 true
                          rw [hx0]
                          norm_num [w4s, Fin.ext_iff]
                        · show w4s 1 (x 1) < w4s 3 true
                          rw [hx1]
                          norm_num [w4s, Fin.ext_iff]
                        · show w4s 2 (x 2) < w4s 3 true
                          rw [hx2]
                          norm_num [w4s, Fin.ext_iff]
                        · exact absurd rfl hji
                        · show w4s 4 (x 4) < w4s 3 true
                          rw [hx4]
                          norm_num [w4s, Fin.ext_iff]
                      rw [tableHead_output_strict w4s w4r x 3 hm, hx3]
                      norm_num [w4r, maj5W4, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]
                  | false =>
                      have hm : ∀ j, w4s j (x j) ≤ w4s 0 (x 0) := by
                        intro j
                        rw [hx0]
                        fin_cases j
                        · show w4s 0 (x 0) ≤ w4s 0 false
                          rw [hx0]
                        · show w4s 1 (x 1) ≤ w4s 0 false
                          rw [hx1]
                          norm_num [w4s, Fin.ext_iff]
                        · show w4s 2 (x 2) ≤ w4s 0 false
                          rw [hx2]
                          norm_num [w4s, Fin.ext_iff]
                        · show w4s 3 (x 3) ≤ w4s 0 false
                          rw [hx3]
                          norm_num [w4s, Fin.ext_iff]
                        · show w4s 4 (x 4) ≤ w4s 0 false
                          rw [hx4]
                          norm_num [w4s, Fin.ext_iff]
                      rw [tableHead_output_eq w4s w4r x 0 hm (fun j _ => Fin.zero_le j), hx0]
                      norm_num [w4r, maj5W4, hx0, hx1, hx2, hx3, hx4, Fin.ext_iff]


/-! ## §3 Assembly and exactness -/

/-- **Four heads suffice.** The four decision-list heads with the
    linear-threshold readout `v₀ + v₁ + 2v₂ + 2v₃ > 3/2` compute maj₅. -/
theorem maj5_computable_by_four_heads :
    ∃ (d : ℕ) (h : Fin 4 → HardAttentionHead 5 d) (w : Fin 4 → ℝ)
      (bias : ℝ),
      ∀ x : Fin 5 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
            + bias > 0
         then true else false) = maj x := by
  refine ⟨2, ![tableHead w1s w1r, tableHead w2s w2r, tableHead w3s w3r,
    tableHead w4s w4r], ![1, 1, 2, 2], -(3/2), fun x => ?_⟩
  have hmaj := congrFun maj5_eq_four_witness_combination x
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  simp only [headW1_computes, headW2_computes, headW3_computes,
    headW4_computes]
  rw [← hmaj]
  cases maj5W1 x <;> cases maj5W2 x <;> cases maj5W3 x <;>
    cases maj5W4 x <;> norm_num

/-- **k_heads(maj₅) = 4 — exactness at the attention level.** Four
    hard-attention heads with a thresholded affine readout compute
    strict majority on five bits, and three cannot. -/
theorem maj5_head_number_exact :
    (∃ (d : ℕ) (h : Fin 4 → HardAttentionHead 5 d) (w : Fin 4 → ℝ)
      (bias : ℝ),
      ∀ x : Fin 5 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
            + bias > 0
         then true else false) = maj x) ∧
    (∀ (d : ℕ) (h : Fin 3 → HardAttentionHead 5 d) (w : Fin 3 → ℝ)
      (bias : ℝ),
      ¬ (∀ x : Fin 5 → Bool,
        (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
            + bias > 0
         then true else false) = maj x)) :=
  ⟨maj5_computable_by_four_heads,
   fun _ h w bias => maj5_requires_four_heads h w bias⟩

end
