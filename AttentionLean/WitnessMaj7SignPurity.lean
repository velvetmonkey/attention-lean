/- SPDX-License-Identifier: MIT -/

/-
  AttentionLean.WitnessMaj7SignPurity

  **Sign purity for five-witness computations of maj₇.**

  The exact value of k(maj₇) ∈ {5, 6} is open (`maj7_witness_bracket_tight`).
  This module rules out, in-kernel, a large slice of the remaining
  five-witness search space: in ANY five-fixable-witness computation of
  strict majority on seven bits, every constancy half-cube of every witness
  carries the SAME sign — all of the form {xᵢ = true}, or all of the form
  {xᵢ = false}.  Mixed-sign families are impossible.

  THE MECHANISM (`maj_witness_descent_pair`): the balanced double pin of
  `maj_witness_descent` (WitnessMaj7Lower) kills ONE witness per pin — but
  if TWO distinct witnesses are constant on half-cubes that one balanced
  pin covers simultaneously, both die at once: 5 witnesses on maj₇ descend
  to 3 witnesses on maj₅, contradicting the in-kernel
  `maj5_no_three_fixable_witnesses`.  One balanced pin covers two
  half-cubes exactly when they are

    * opposite signs on distinct coordinates ({x_d = b}, {x_e = !b}), or
    * the same half-cube ({x_d = b} shared by both witnesses),

  giving `maj7_no_mixed_sign_pair` and `maj7_no_shared_face_pair`.  The
  remaining mixed configuration — opposite signs on the SAME coordinate —
  dies through a third witness (`maj7_no_opposite_pair_same_direction`):
  its own constancy half-cube must pair with one of the two, whatever it
  is.  `maj7_five_witness_sign_purity` assembles the full statement.

  Consequence for the open endpoint: a hypothetical 5-witness computation
  of maj₇ is now confined (up to the maj self-duality) to the single
  configuration where every witness is constant on a positive half-cube,
  no two witnesses share one, and — by `maj7_no_four_fixable_witnesses` —
  no witness is constant.  The companion search artifact
  `scripts/maj7_witness_search.py` explores exactly that configuration.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`.
  No `native_decide`, no `sorry`.  Purely additive.
-/
import AttentionLean.WitnessMaj7Lower

open Classical

noncomputable section

/-! ## §1 The pair descent: one balanced pin, two witnesses die -/

section PairDescent

variable {n : ℕ}

/-- **Core pair descent.**  If `k + 2` fixable witnesses and an aggregator
    compute strict majority on `n + 2` bits, and two DISTINCT witnesses
    (indices `a` and `a.succAbove p`) are each constant on the balanced
    subcube {x_d = b, x_{d.succAbove q} = !b}, then `k` fixable witnesses
    and an aggregator compute strict majority on `n` bits.

    This is `maj_witness_descent` with two witnesses curried away at one
    pin: majority survives the balanced pin (`maj_cubeEmbed_balanced`),
    the surviving witnesses restrict to fixable functions
    (`fixable_restrict`), and the aggregator absorbs both dead witnesses'
    constants via a double `Fin.insertNth`. -/
theorem maj_witness_descent_pair [NeZero n] {k : ℕ}
    (w : Fin (k + 2) → (Fin (n + 2) → Bool) → Bool)
    (hfix : ∀ i, Fixable (w i))
    (agg : (Fin (k + 2) → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin (n + 2) → Bool) → Bool))
    (a : Fin (k + 2)) (p : Fin (k + 1))
    (d : Fin (n + 2)) (q : Fin (n + 1)) (b : Bool) (c c' : Bool)
    (hca : ∀ x : Fin (n + 2) → Bool,
      x d = b → x (d.succAbove q) = !b → w a x = c)
    (hca' : ∀ x : Fin (n + 2) → Bool,
      x d = b → x (d.succAbove q) = !b → w (a.succAbove p) x = c') :
    ∃ w' : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (w' i)) ∧
      ∃ agg' : (Fin k → Bool) → Bool,
        (fun y => agg' (fun i => w' i y))
          = (maj : (Fin n → Bool) → Bool) := by
  -- the balanced background: d ↦ b, j₀ ↦ !b, elsewhere false
  set j₀ : Fin (n + 2) := d.succAbove q with hj₀def
  set bg : Fin (n + 2) → Bool :=
    fun t => if t = d then b else if t = j₀ then !b else false with hbgdef
  have hbgi : bg d = b := by simp [hbgdef]
  have hbgj : bg j₀ = !b := by
    have hne : j₀ ≠ d := Fin.succAbove_ne d q
    simp [hbgdef, hne]
  set σ : Fin n → Fin (n + 2) := fun m => d.succAbove (q.succAbove m)
    with hσdef
  have hσinj : Function.Injective σ :=
    fun x x' h => Fin.succAbove_right_injective
      (Fin.succAbove_right_injective h)
  have hnot_d : ¬ ∃ m, σ m = d := by
    rintro ⟨m, hm⟩
    exact Fin.succAbove_ne d (q.succAbove m) hm
  have hnot_j₀ : ¬ ∃ m, σ m = j₀ := by
    rintro ⟨m, hm⟩
    exact Fin.succAbove_ne q m (Fin.succAbove_right_injective (p := d) hm)
  -- the embedding lands on the pinned subcube
  have hei : ∀ y : Fin n → Bool, cubeEmbed σ bg y d = b := fun y => by
    rw [cubeEmbed_apply_not_mem σ bg y d hnot_d, hbgi]
  have hej : ∀ y : Fin n → Bool, cubeEmbed σ bg y j₀ = !b := fun y => by
    rw [cubeEmbed_apply_not_mem σ bg y j₀ hnot_j₀, hbgj]
  -- both designated witnesses are constant along the embedding
  have h0 : ∀ y, w a (cubeEmbed σ bg y) = c :=
    fun y => hca _ (hei y) (hej y)
  have h1 : ∀ y, w (a.succAbove p) (cubeEmbed σ bg y) = c' :=
    fun y => hca' _ (hei y) (hej y)
  -- assemble the k-witness configuration on the free cube
  refine ⟨fun i y => w (a.succAbove (p.succAbove i)) (cubeEmbed σ bg y),
    fun i => fixable_restrict σ hσinj bg _ (hfix _),
    fun v => agg (a.insertNth c (p.insertNth c' v)), ?_⟩
  funext y
  have hvec : (a.insertNth c (p.insertNth c'
      (fun m => w (a.succAbove (p.succAbove m)) (cubeEmbed σ bg y)))
      : Fin (k + 2) → Bool) = fun i => w i (cubeEmbed σ bg y) := by
    funext i
    by_cases hia : i = a
    · subst hia
      rw [Fin.insertNth_apply_same, h0]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hia
      rw [Fin.insertNth_apply_succAbove]
      by_cases hjp : j = p
      · subst hjp
        rw [Fin.insertNth_apply_same, h1]
      · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hjp
        rw [Fin.insertNth_apply_succAbove]
  show agg (a.insertNth c (p.insertNth c'
    (fun i => w (a.succAbove (p.succAbove i)) (cubeEmbed σ bg y)))) = maj y
  rw [hvec, congrFun heq (cubeEmbed σ bg y),
    maj_cubeEmbed_balanced d q b bg hbgi hbgj y]

end PairDescent

/-! ## §2 The two one-pin kills on maj₇ -/

/-- **No mixed-sign pair, distinct directions.**  Among five fixable
    witnesses computing maj₇, no two distinct witnesses are constant on
    half-cubes of opposite signs over distinct coordinates: one balanced
    pin covers both half-cubes, and 5 − 2 = 3 witnesses would compute
    maj₅. -/
theorem maj7_no_mixed_sign_pair
    (w : Fin 5 → (Fin 7 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin 5 → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin 7 → Bool) → Bool))
    (a a' : Fin 5) (haa' : a' ≠ a) (d e : Fin 7) (hde : e ≠ d)
    (b c c' : Bool)
    (hca : ∀ x, x d = b → w a x = c)
    (hca' : ∀ x, x e = !b → w a' x = c') : False := by
  obtain ⟨p, rfl⟩ := Fin.exists_succAbove_eq haa'
  obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq hde
  obtain ⟨w', hfix', agg', heq'⟩ :=
    maj_witness_descent_pair (n := 5) (k := 3) w hfix agg heq a p d q b c c'
      (fun x hd _ => hca x hd) (fun x _ he => hca' x he)
  exact maj5_no_three_fixable_witnesses w' hfix' agg' heq'

/-- **No shared half-cube.**  Among five fixable witnesses computing maj₇,
    no two distinct witnesses are constant on the SAME half-cube: a
    balanced pin through that half-cube (second coordinate arbitrary)
    covers both, and 3 witnesses would compute maj₅. -/
theorem maj7_no_shared_face_pair
    (w : Fin 5 → (Fin 7 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin 5 → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin 7 → Bool) → Bool))
    (a a' : Fin 5) (haa' : a' ≠ a) (d : Fin 7) (b c c' : Bool)
    (hca : ∀ x, x d = b → w a x = c)
    (hca' : ∀ x, x d = b → w a' x = c') : False := by
  obtain ⟨p, rfl⟩ := Fin.exists_succAbove_eq haa'
  obtain ⟨w', hfix', agg', heq'⟩ :=
    maj_witness_descent_pair (n := 5) (k := 3) w hfix agg heq a p d 0 b c c'
      (fun x hd _ => hca x hd) (fun x hd _ => hca' x hd)
  exact maj5_no_three_fixable_witnesses w' hfix' agg' heq'

/-! ## §3 Opposite signs on one direction die through a third witness -/

/-- Fin 5 always offers a third index. -/
private theorem fin5_third :
    ∀ a a' : Fin 5, ∃ l : Fin 5, l ≠ a ∧ l ≠ a' := by decide

/-- **No opposite-sign pair on one direction.**  Among five fixable
    witnesses computing maj₇, no two witnesses (not necessarily distinct
    — the `a = a'` case covers a single witness constant on both sides)
    are constant on the two opposite half-cubes of a single coordinate.
    A third witness exists and is itself constant on some half-cube;
    whatever that half-cube is, it forms a shared-face or mixed-sign pair
    with one of the two. -/
theorem maj7_no_opposite_pair_same_direction
    (w : Fin 5 → (Fin 7 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin 5 → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin 7 → Bool) → Bool))
    (a a' : Fin 5) (d : Fin 7) (c c' : Bool)
    (hpos : ∀ x, x d = true → w a x = c)
    (hneg : ∀ x, x d = false → w a' x = c') : False := by
  obtain ⟨l, hla, hla'⟩ := fin5_third a a'
  obtain ⟨f, β, cl, hlface⟩ := fixable_halfcube_const (hfix l)
  by_cases hfd : f = d
  · rw [hfd] at hlface
    cases β
    · -- l shares the negative half-cube {x d = false} with a'
      exact maj7_no_shared_face_pair w hfix agg heq a' l hla' d false c' cl
        hneg hlface
    · -- l shares the positive half-cube {x d = true} with a
      exact maj7_no_shared_face_pair w hfix agg heq a l hla d true c cl
        hpos hlface
  · cases β
    · -- a positive on d, l negative on f, d ≠ f
      exact maj7_no_mixed_sign_pair w hfix agg heq a l hla d f hfd
        true c cl hpos (by simpa using hlface)
    · -- l positive on f, a' negative on d, f ≠ d
      exact maj7_no_mixed_sign_pair w hfix agg heq l a' (Ne.symm hla')
        f d (fun h => hfd h.symm) true cl c' hlface (by simpa using hneg)

/-! ## §4 Sign purity -/

/-- **Sign purity.**  In any five-fixable-witness computation of maj₇,
    all constancy half-cubes carry one sign: there is a single `s : Bool`
    such that every half-cube {x_d = b} on which any witness is constant
    has `b = s`.  Mixed-sign five-witness families cannot compute maj₇. -/
theorem maj7_five_witness_sign_purity
    (w : Fin 5 → (Fin 7 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin 5 → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x))
             = (maj : (Fin 7 → Bool) → Bool)) :
    ∃ s : Bool, ∀ (i : Fin 5) (d : Fin 7) (b c : Bool),
      (∀ x, x d = b → w i x = c) → b = s := by
  by_contra h
  push_neg at h
  -- a negative face (b ≠ true) and a positive face (b ≠ false)
  obtain ⟨i₁, d₁, b₁, c₁, hface₁, hb₁⟩ := h true
  obtain ⟨i₂, d₂, b₂, c₂, hface₂, hb₂⟩ := h false
  simp only [ne_eq, Bool.not_eq_true, Bool.not_eq_false] at hb₁ hb₂
  subst hb₁; subst hb₂
  -- now: w i₁ constant on {x d₁ = false}, w i₂ constant on {x d₂ = true}
  by_cases hdd : d₁ = d₂
  · -- opposite signs on one direction (distinctness of witnesses not needed)
    subst hdd
    exact maj7_no_opposite_pair_same_direction w hfix agg heq i₂ i₁
      d₁ c₂ c₁ hface₂ hface₁
  · by_cases hii : i₁ = i₂
    · -- one witness, faces of both signs on distinct directions: pair it
      -- with any other witness's half-cube
      subst hii
      obtain ⟨l, hl, -⟩ := fin5_third i₁ i₁
      obtain ⟨f, β, cl, hlface⟩ := fixable_halfcube_const (hfix l)
      cases β
      · -- i₁ positive on d₂, l negative on f
        by_cases hfd : f = d₂
        · rw [hfd] at hlface
          exact maj7_no_opposite_pair_same_direction w hfix agg heq i₁ l
            d₂ c₂ cl hface₂ hlface
        · exact maj7_no_mixed_sign_pair w hfix agg heq i₁ l hl d₂ f hfd
            true c₂ cl hface₂ (by simpa using hlface)
      · -- l positive on f, i₁ negative on d₁
        by_cases hfd : f = d₁
        · rw [hfd] at hlface
          exact maj7_no_opposite_pair_same_direction w hfix agg heq l i₁
            d₁ cl c₁ hlface hface₁
        · exact maj7_no_mixed_sign_pair w hfix agg heq l i₁ (Ne.symm hl)
            f d₁ (fun hdf => hfd hdf.symm) true cl c₁ hlface
            (by simpa using hface₁)
    · -- distinct witnesses, opposite signs, distinct directions
      exact maj7_no_mixed_sign_pair w hfix agg heq i₂ i₁ hii d₂ d₁ hdd
        true c₂ c₁ hface₂ (by simpa using hface₁)

end
