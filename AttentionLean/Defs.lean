/-
  AttentionLean.Defs
  Core structures and definitions for hard attention over finite Boolean sequences.
-/
import Mathlib

open Finset Classical

noncomputable section

/-- A single hard-attention head operating on `n`-position Boolean sequences,
    with internal dimension `d`.

    *  `W_Q`, `W_K` are score matrices (query / key weights).
    *  `query` is the fixed query vector.
    *  `tok` is a fixed positional + value token embedding.
    *  `W_V` is the value-projection vector.
    *  `readout_w`, `readout_b` form the affine readout (weight and bias). -/
structure HardAttentionHead (n d : ℕ) where
  W_Q : Matrix (Fin d) (Fin d) ℝ
  W_K : Matrix (Fin d) (Fin d) ℝ
  query : Fin d → ℝ
  tok : Fin n → Bool → (Fin d → ℝ)
  W_V : Fin d → ℝ
  readout_w : ℝ
  readout_b : ℝ

variable {n d : ℕ}

/-- Attention score at position `i` for input `x`.
    Defined as ⟪W_Q · query, W_K · tok(i, x(i))⟫. -/
def attentionScore (head : HardAttentionHead n d) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  dotProduct (head.W_Q.mulVec head.query) (head.W_K.mulVec (head.tok i (x i)))

/-- The score at position `i` depends only on `i` and `x i` — a convenience wrapper. -/
def scoreVal (head : HardAttentionHead n d) (i : Fin n) (b : Bool) : ℝ :=
  dotProduct (head.W_Q.mulVec head.query) (head.W_K.mulVec (head.tok i b))

@[simp]
theorem attentionScore_eq_scoreVal (head : HardAttentionHead n d) (x : Fin n → Bool) (i : Fin n) :
    attentionScore head x i = scoreVal head i (x i) := rfl

/-- Value read at position `i` when the input there is `b`. -/
def readVal (head : HardAttentionHead n d) (i : Fin n) (b : Bool) : ℝ :=
  dotProduct head.W_V (head.tok i b)

/-- Deterministic argmax with smallest-index tie-breaking.
    Returns the smallest `Fin n` index achieving the maximum score.
    Uses `Finset.sup'` for the maximum value and `Finset.min'` for the tie-break. -/
def argmaxScore [NeZero n] (scores : Fin n → ℝ) : Fin n :=
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty
  let M := univ.sup' hne scores
  have hfilt : (univ.filter (fun i => scores i = M)).Nonempty := by
    obtain ⟨i, hi, hv⟩ := exists_mem_eq_sup' hne scores
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hv.symm⟩⟩
  (univ.filter (fun i => scores i = M)).min' hfilt

/-- Full output of a hard-attention head on input `x`.
    1. Compute attention scores.
    2. Select the argmax position (smallest-index tie-break).
    3. Read the value at the winning position.
    4. Apply affine readout and threshold at 0. -/
def headOutput [NeZero n] (head : HardAttentionHead n d) (x : Fin n → Bool) : Bool :=
  let winner := argmaxScore (attentionScore head x)
  let val := readVal head winner (x winner)
  if head.readout_w * val + head.readout_b > 0 then true else false

end
