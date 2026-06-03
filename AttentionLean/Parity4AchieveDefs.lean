/-
  AttentionLean.Parity4AchieveDefs
  Efficient definitions and the main 4.3B native_decide for achievability.
-/
import AttentionLean.Parity4Data

/-- Array-based O(1) membership check in achievable4Raw. -/
def ach4Arr : Array Bool :=
  let base := Array.replicate 65536 false
  achievable4Raw.foldl (fun a n => if n < 65536 then a.set! n true else a) base

@[inline] def inAch4 (m : ℕ) : Bool :=
  if m < 65536 then ach4Arr[m]! else false

/-- Inline mask computation — all 16 args explicit, no function types. -/
@[inline] def mask4Full (s0f s0t s1f s1t s2f s2t s3f s3t : ℕ)
    (r0f r0t r1f r1t r2f r2t r3f r3t : Bool) : ℕ :=
  let g (x0 x1 x2 x3 : Bool) : Bool :=
    let sc0 := if x0 then s0t else s0f
    let sc1 := if x1 then s1t else s1f
    let sc2 := if x2 then s2t else s2f
    let sc3 := if x3 then s3t else s3f
    let w : Fin 4 :=
      if sc0 ≥ sc1 && sc0 ≥ sc2 && sc0 ≥ sc3 then 0
      else if sc1 ≥ sc2 && sc1 ≥ sc3 then 1
      else if sc2 ≥ sc3 then 2 else 3
    match w with
    | 0 => if x0 then r0t else r0f
    | 1 => if x1 then r1t else r1f
    | 2 => if x2 then r2t else r2f
    | 3 => if x3 then r3t else r3f
  let b (x0 x1 x2 x3 : Bool) (bit : ℕ) : ℕ :=
    if g x0 x1 x2 x3 then 2^bit else 0
  b false false false false 0 + b true false false false 1 +
  b false true false false 2 + b true true false false 3 +
  b false false true false 4 + b true false true false 5 +
  b false true true false 6 + b true true true false 7 +
  b false false false true 8 + b true false false true 9 +
  b false true false true 10 + b true true false true 11 +
  b false false true true 12 + b true false true true 13 +
  b false true true true 14 + b true true true true 15

theorem inAch4_lt (m : ℕ) (h : inAch4 m = true) : m < 65536 := by
  simp only [inAch4] at h
  split at h <;> [assumption; exact absurd h Bool.false_ne_true]

theorem inAch4_sound_raw (m : ℕ) (h : inAch4 m = true) : m ∈ achievable4Raw := by
  have hlt := inAch4_lt m h
  have : ∀ n : Fin 65536, inAch4 n.val = true → n.val ∈ achievable4Raw := by native_decide
  exact this ⟨m, hlt⟩ h
