/- SPDX-License-Identifier: MIT -/

/-
  AttentionLean.WitnessMaj7Lower

  **k(maj₇) ≥ 5 — the bracket tightens to [5, 6], structurally.**

  The previous lower rung for maj₇ was the certificate bound
  `maj_needs_half_fixable_witnesses` (⌈7/2⌉ = 4). This module raises it
  to 5 with NO enumeration over the 7-cube, via a witness-killing
  descent:

  THE SMARTER LEMMA (`maj_witness_descent`). Suppose k + 1 fixable
  witnesses and an aggregator compute strict majority on n + 2 bits.
  The first witness, being fixable, is constant on some half-cube
  {x_{i₀} = b} (instantiate `Fixable` at the full cube: its first
  decision-list literal). Pin a SECOND coordinate j₀ ≠ i₀ to the
  OPPOSITE value !b. The double pin is balanced — one 1 and one 0 —
  so strict majority on the n + 2 cube restricts to strict majority
  on the n free coordinates (2·(c+1) > n+2 ↔ 2·c > n). On this
  subcube the first witness is a known constant, so it contributes
  nothing: the remaining k witnesses (still fixable, by the frozen
  crux `fixable_restrict`) together with the curried aggregator
  compute maj on n bits. One witness dies per balanced double pin.

  Consequences:
  - `maj7_no_four_fixable_witnesses`: 4 fixable witnesses cannot
    compute maj₇ — descent + `maj5_no_three_fixable_witnesses`
    (the in-kernel maj₅ result). So k_witness(maj₇) ≥ 5.
  - `maj7_witness_bracket_tight` / `maj7_head_bracket_tight`:
    5 ≤ k(maj₇) ≤ 6, witness and head forms. The old `[4, 6]`
    bracket theorems are untouched; these are strictly sharper
    additions.
  - `maj_odd_ladder`: the descent iterates — for every j, no j + 3
    fixable witnesses compute maj on 2j + 5 bits. Reading off:
    k_witness(maj_n) ≥ (n + 3) / 2 for every odd n ≥ 5, one better
    than the certificate bound ⌈n/2⌉ everywhere on the odd ladder.

  Why this dodges the blow-up: the maj₅ exact analysis (catalogs +
  case kills) is invoked as a black box on the 5-cube; nothing here
  looks at 2⁷ points. The exact value of k(maj₇) in {5, 6} stays
  OPEN; closing it needs a genuinely new analysis (a "no five
  witnesses" argument cannot fall out of this descent, since five
  minus one is four, and four witnesses DO compute maj₅).

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`, no `sorry`. Purely additive.
-/
import AttentionLean.WitnessMaj7Bracket

open Classical Finset

noncomputable section

/-! ## §1 Small helpers -/

/-- The full cube: `memCube` against the all-`none` pin pattern is trivial. -/
theorem memCube_top {n : ℕ} (x : Fin n → Bool) :
    memCube (fun _ => none) x := fun _ _ h => by simp at h

/-- A fixable function is constant on some half-cube — its "first literal".
    (`Fixable` instantiated at the full cube.) -/
theorem fixable_halfcube_const {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Fixable f) :
    ∃ (i : Fin n) (b : Bool) (c : Bool),
      ∀ x : Fin n → Bool, x i = b → f x = c := by
  obtain ⟨i, b, -, c, hconst⟩ := hf (fun _ => none)
  exact ⟨i, b, c, fun x hx => hconst x (memCube_top x) hx⟩

/-! ## §2 The balanced double pin -/

section Descent

variable {n : ℕ}

/-- Ones-count of a balanced embedding: freezing one coordinate to `b` and
    another to `!b` adds exactly one set bit, whatever `b` is. -/
theorem card_ones_cubeEmbed_balanced
    (i₀ : Fin (n + 2)) (q : Fin (n + 1)) (b : Bool)
    (bg : Fin (n + 2) → Bool)
    (hbgi : bg i₀ = b) (hbgj : bg (i₀.succAbove q) = !b)
    (y : Fin n → Bool) :
    (univ.filter fun t =>
        cubeEmbed (fun m => i₀.succAbove (q.succAbove m)) bg y t = true).card
      = (univ.filter fun m => y m = true).card + 1 := by
  set σ : Fin n → Fin (n + 2) := fun m => i₀.succAbove (q.succAbove m) with hσ
  have hσinj : Function.Injective σ :=
    fun a a' h => Fin.succAbove_right_injective
      (Fin.succAbove_right_injective h)
  -- the embedding off the image of σ
  have hnot_i₀ : ¬ ∃ m, σ m = i₀ := by
    rintro ⟨m, hm⟩
    exact Fin.succAbove_ne i₀ (q.succAbove m) hm
  have hnot_j₀ : ¬ ∃ m, σ m = i₀.succAbove q := by
    rintro ⟨m, hm⟩
    exact Fin.succAbove_ne q m (Fin.succAbove_right_injective (p := i₀) hm)
  have hei : cubeEmbed σ bg y i₀ = b := by
    rw [cubeEmbed_apply_not_mem σ bg y i₀ hnot_i₀, hbgi]
  have hej : cubeEmbed σ bg y (i₀.succAbove q) = !b := by
    rw [cubeEmbed_apply_not_mem σ bg y _ hnot_j₀, hbgj]
  have hon : ∀ m : Fin n,
      cubeEmbed σ bg y (i₀.succAbove (q.succAbove m)) = y m :=
    fun m => cubeEmbed_apply_mem σ hσinj bg y m
  rw [Finset.card_filter, Finset.card_filter]
  rw [Fin.sum_univ_succAbove
      (fun t => if cubeEmbed σ bg y t = true then 1 else 0) i₀]
  rw [Fin.sum_univ_succAbove
      (fun t => if cubeEmbed σ bg y (i₀.succAbove t) = true then 1 else 0) q]
  simp only [hei, hej, hon]
  cases b <;> simp [add_comm]

/-- Strict majority survives a balanced double pin: on the subcube with one
    coordinate frozen to `b` and another to `!b`, `maj` on `n + 2` bits is
    `maj` on the `n` free bits. -/
theorem maj_cubeEmbed_balanced
    (i₀ : Fin (n + 2)) (q : Fin (n + 1)) (b : Bool)
    (bg : Fin (n + 2) → Bool)
    (hbgi : bg i₀ = b) (hbgj : bg (i₀.succAbove q) = !b)
    (y : Fin n → Bool) :
    maj (cubeEmbed (fun m => i₀.succAbove (q.succAbove m)) bg y) = maj y := by
  unfold maj
  rw [card_ones_cubeEmbed_balanced i₀ q b bg hbgi hbgj y]
  exact decide_eq_decide.mpr (by omega)

/-- **THE DESCENT (the smarter lemma).** If `k + 1` fixable witnesses and an
    aggregator compute strict majority on `n + 2` bits, then `k` fixable
    witnesses and an aggregator compute strict majority on `n` bits.

    Proof: the first witness is constant (value `c`) on a half-cube
    `{x i₀ = b}`; pin a second coordinate `j₀ ≠ i₀` to `!b`. The double pin
    is balanced, so `maj` descends to the free coordinates; the surviving
    `k` witnesses restrict to fixable witnesses (`fixable_restrict`), and
    the aggregator is curried with the dead witness's constant `c`. -/
theorem maj_witness_descent [NeZero n] {k : ℕ}
    (w : Fin (k + 1) → (Fin (n + 2) → Bool) → Bool)
    (hfix : ∀ i, Fixable (w i))
    (agg : (Fin (k + 1) → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin (n + 2) → Bool) → Bool)) :
    ∃ w' : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (w' i)) ∧
      ∃ agg' : (Fin k → Bool) → Bool,
        (fun y => agg' (fun i => w' i y))
          = (maj : (Fin n → Bool) → Bool) := by
  -- the first witness's constant half-cube {x i₀ = b}, value c
  obtain ⟨i₀, b, c, hconst⟩ := fixable_halfcube_const (hfix 0)
  -- a second, automatically distinct coordinate j₀ = i₀.succAbove q
  set q : Fin (n + 1) := 0 with hqdef
  -- the balanced background: i₀ ↦ b, j₀ ↦ !b, elsewhere false
  set j₀ : Fin (n + 2) := i₀.succAbove q with hj₀def
  set bg : Fin (n + 2) → Bool :=
    fun t => if t = i₀ then b else if t = j₀ then !b else false with hbgdef
  have hbgi : bg i₀ = b := by simp [hbgdef]
  have hbgj : bg j₀ = !b := by
    have hne : j₀ ≠ i₀ := Fin.succAbove_ne i₀ q
    simp [hbgdef, hne]
  set σ : Fin n → Fin (n + 2) := fun m => i₀.succAbove (q.succAbove m)
    with hσdef
  have hσinj : Function.Injective σ :=
    fun a a' h => Fin.succAbove_right_injective
      (Fin.succAbove_right_injective h)
  -- the embedding hits the first witness's constant half-cube
  have hnot_i₀ : ¬ ∃ m, σ m = i₀ := by
    rintro ⟨m, hm⟩
    exact Fin.succAbove_ne i₀ (q.succAbove m) hm
  have hei : ∀ y : Fin n → Bool, cubeEmbed σ bg y i₀ = b := fun y => by
    rw [cubeEmbed_apply_not_mem σ bg y i₀ hnot_i₀, hbgi]
  -- assemble the k-witness configuration on the free cube
  refine ⟨fun i y => w i.succ (cubeEmbed σ bg y),
    fun i => fixable_restrict σ hσinj bg (w i.succ) (hfix i.succ),
    fun v => agg (Fin.cons c v), ?_⟩
  funext y
  have h0 : w 0 (cubeEmbed σ bg y) = c := hconst _ (hei y)
  have hvec : (Fin.cons c (fun i => w i.succ (cubeEmbed σ bg y))
      : Fin (k + 1) → Bool) = fun i => w i (cubeEmbed σ bg y) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [Fin.cons_zero, h0]
    · rw [Fin.cons_succ]
  show agg (Fin.cons c fun i => w i.succ (cubeEmbed σ bg y)) = maj y
  rw [hvec, congrFun heq (cubeEmbed σ bg y),
    maj_cubeEmbed_balanced i₀ q b bg hbgi hbgj y]

end Descent

/-! ## §3 maj₇: the bracket tightens to [5, 6] -/

/-- **Four fixable witnesses cannot compute maj₇** — so k_witness(maj₇) ≥ 5.
    One descent step lands on the in-kernel maj₅ impossibility; no
    enumeration over the 7-cube occurs. -/
theorem maj7_no_four_fixable_witnesses :
    ∀ w : Fin 4 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) →
    ∀ agg : (Fin 4 → Bool) → Bool,
      (fun x => agg (fun i => w i x)) ≠ (maj : (Fin 7 → Bool) → Bool) := by
  intro w hfix agg heq
  obtain ⟨w', hfix', agg', heq'⟩ :=
    maj_witness_descent (n := 5) (k := 3) w hfix agg heq
  exact maj5_no_three_fixable_witnesses w' hfix' agg' heq'

/-- **maj₇ witness bracket, tightened: 5 ≤ k ≤ 6.** Six fixable witnesses
    suffice (frozen upper half of `maj7_witness_bracket`), and four cannot.
    Strictly sharper than the `[4, 6]` bracket; the exact value in {5, 6}
    remains open. -/
theorem maj7_witness_bracket_tight :
    (∃ w : Fin 6 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 6 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj) ∧
    (∀ w : Fin 4 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 4 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ maj) :=
  ⟨maj7_computable_by_six_fixable, maj7_no_four_fixable_witnesses⟩

/-- **maj₇ requires five hard-attention heads**: no four heads, through ANY
    Boolean aggregator, compute strict majority on seven bits — heads are
    fixable witnesses. -/
theorem maj7_requires_five_heads :
    ∀ (d : ℕ) (h : Fin 4 → HardAttentionHead 7 d)
      (agg : (Fin 4 → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x))
        ≠ (maj : (Fin 7 → Bool) → Bool) :=
  fun _ h agg => maj7_no_four_fixable_witnesses
    (fun i => headOutput (h i)) (fun i => headOutput_fixable (h i)) agg

/-- **maj₇ head bracket, tightened: 5 ≤ k ≤ 6** (arbitrary Boolean
    aggregator on both ends, as in `maj7_head_bracket`). -/
theorem maj7_head_bracket_tight :
    (∃ (d : ℕ) (h : Fin 6 → HardAttentionHead 7 d)
      (agg : (Fin 6 → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x)) = maj) ∧
    (∀ (d : ℕ) (h : Fin 4 → HardAttentionHead 7 d)
      (agg : (Fin 4 → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x)) ≠ maj) :=
  ⟨((heads_computability_iff_fixable_witnesses
      (T := (maj : (Fin 7 → Bool) → Bool))).mpr
        maj7_computable_by_six_fixable),
   maj7_requires_five_heads⟩

/-! ## §4 The odd ladder: the descent iterates -/

/-- **The odd-majority ladder.** For every `j`, no `j + 3` fixable witnesses
    compute strict majority on `2j + 5` bits. Base `j = 0` is the in-kernel
    maj₅ result; each step is one balanced double pin. Reading off:
    `k_witness(maj_n) ≥ (n + 3) / 2` for every odd `n ≥ 5` — one better
    than the certificate bound `⌈n/2⌉` everywhere on the odd ladder. -/
theorem maj_odd_ladder :
    ∀ (j : ℕ) (w : Fin (j + 3) → (Fin (2 * j + 5) → Bool) → Bool),
      (∀ i, Fixable (w i)) → ∀ agg : (Fin (j + 3) → Bool) → Bool,
      (fun x => agg (fun i => w i x))
        ≠ (maj : (Fin (2 * j + 5) → Bool) → Bool) := by
  intro j
  induction j with
  | zero => exact maj5_no_three_fixable_witnesses
  | succ j ih =>
      intro w hfix agg heq
      obtain ⟨w', hfix', agg', heq'⟩ :=
        maj_witness_descent (n := 2 * j + 5) (k := j + 3) w hfix agg heq
      exact ih w' hfix' agg' heq'

-- Sanity: the ladder at j = 1 re-proves the maj₇ rung.
example :
    ∀ w : Fin 4 → (Fin 7 → Bool) → Bool, (∀ i, Fixable (w i)) →
    ∀ agg : (Fin 4 → Bool) → Bool,
      (fun x => agg (fun i => w i x)) ≠ (maj : (Fin 7 → Bool) → Bool) :=
  maj_odd_ladder 1

end
