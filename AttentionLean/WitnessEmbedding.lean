/-
  AttentionLean.WitnessEmbedding

  Rung 2b of the witness theory: the restriction/embedding lower bound.
  `fixable_witnesses_lower_bound` needs the target EVERYWHERE-sensitive —
  parity maxes that measure, but inner-product and majority go flat in
  places. This module extends the reach to any target that merely CONTAINS
  a maximally-sensitive subfunction under a restriction.

  STEP 0 — THE CRUX LEMMA (frozen, assessed before proving). Restricting a
  `Fixable` witness to a subcube — embedding an m-cube into the n-cube
  along an injection `σ` with the off-image coordinates frozen to a
  background `bg` — yields a `Fixable` witness on the m free coordinates:

    `fixable_restrict : Fixable f → Fixable (fun y => f (cubeEmbed σ bg y))`

  VERDICT: HOLDS, cleanly, from the `Fixable` definition. Given a subcube
  `τ` on the m-cube, lift it to the n-cube (free coordinates carry `τ`,
  frozen coordinates pinned to `some (bg j)`) and run `f`'s fixability
  there. Two cases for the returned literal `(i_n, b)`:
  * `i_n` is a free coordinate `σ i₀`: the literal TRANSFERS — the
    not-excluded side condition transfers because the lifted cube stores
    exactly `τ i₀` at `σ i₀`, and the constancy transfers through the
    embedding.
  * `i_n` is a frozen coordinate: not-excludedness forces `bg i_n = b`, so
    EVERY embedded point already satisfies the pin — the restricted
    witness is constant on the whole subcube, and any legal literal
    finishes.
  Honest boundary: the lemma needs `m ≥ 1` (`[NeZero m]`): on the empty
  cube even a constant function is not `Fixable` — there is no literal to
  pin. Harmless downstream, where `k < m` supplies it.

  PRIMARY — `restriction_embedding_lower_bound`: if some restriction
  leaves the target everywhere-sensitive on its m free coordinates, then
  no aggregator over `k < m` fixable witnesses computes the target.
  Restrict the witnesses (crux), apply `fixable_witnesses_lower_bound` on
  the m-cube, lift the failure back through the embedding.

  INSTANCE — inner product mod 2, `ip2 x := ⊕_i (x(2i) && x(2i+1))` on
  `2m` bits. NOT everywhere-sensitive (at all-zeros, flipping one factor
  of a dead pair changes nothing — build-gated exhibit), yet fixing every
  odd coordinate to `true` leaves `parityN` on the m even coordinates
  (`ip2_embed`), so `ip2` needs ≥ m fixable witnesses
  (`ip2_needs_m_fixable_witnesses`). Non-vacuity at m = 2: one real head
  witness on 4 bits provably fails (`ip2_four_bits_one_head_fails`).

  HONEST REACH ASSESSMENT. The technique reaches exactly the targets that
  EMBED a full parity (more precisely: admit a restriction that is
  everywhere-sensitive). IN: inner product mod 2 (this module); address /
  multiplexer-style selectors and bent-function relatives that expose a
  parity subcube the same way. OUT: MAJORITY and every monotone target —
  a restriction of a monotone function is monotone, and an
  everywhere-sensitive function on m ≥ 2 coordinates is never monotone
  (flipping a coordinate up must sometimes flip the output down), so no
  monotone target admits such a restriction with m ≥ 2 and the technique
  caps at the vacuous k < 1 for them. A fixable-witness lower bound for
  majority needs a different richness measure (block sensitivity or
  fractional certificates), not this embedding argument.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessTheory

open Classical

noncomputable section

/-! ## §1 Cube embeddings and the crux lemma -/

/-- Embed an m-cube point into the n-cube along `σ`, freezing the off-image
    coordinates to the background `bg`. -/
def cubeEmbed {m n : ℕ} (σ : Fin m → Fin n) (bg : Fin n → Bool)
    (y : Fin m → Bool) : Fin n → Bool :=
  fun j => if h : ∃ i, σ i = j then y h.choose else bg j

theorem cubeEmbed_apply_mem {m n : ℕ} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (bg : Fin n → Bool) (y : Fin m → Bool)
    (i : Fin m) : cubeEmbed σ bg y (σ i) = y i := by
  have h : ∃ i', σ i' = σ i := ⟨i, rfl⟩
  simp only [cubeEmbed, dif_pos h]
  congr 1
  exact hσ h.choose_spec

theorem cubeEmbed_apply_not_mem {m n : ℕ} (σ : Fin m → Fin n)
    (bg : Fin n → Bool) (y : Fin m → Bool) (j : Fin n)
    (hj : ¬ ∃ i, σ i = j) : cubeEmbed σ bg y j = bg j := by
  simp only [cubeEmbed, dif_neg hj]

/-- The embedded point lies in the lifted subcube. -/
theorem memCube_cubeEmbed {m n : ℕ} (σ : Fin m → Fin n)
    (bg : Fin n → Bool) (τ : Fin m → Option Bool) (y : Fin m → Bool)
    (hy : memCube τ y) :
    memCube (fun j => if h : ∃ i, σ i = j then τ h.choose else some (bg j))
      (cubeEmbed σ bg y) := by
  intro j bj hj
  have hj' : (if h : ∃ i, σ i = j then τ h.choose else some (bg j))
      = some bj := hj
  by_cases hjm : ∃ i, σ i = j
  · rw [dif_pos hjm] at hj'
    show cubeEmbed σ bg y j = bj
    simp only [cubeEmbed, dif_pos hjm]
    exact hy _ bj hj'
  · rw [dif_neg hjm] at hj'
    have hbj : bg j = bj := Option.some.inj hj'
    show cubeEmbed σ bg y j = bj
    simp only [cubeEmbed, dif_neg hjm]
    exact hbj

/-- **THE CRUX (frozen).** Restricting a fixable witness along a cube
    embedding yields a fixable witness on the free coordinates. -/
theorem fixable_restrict {m n : ℕ} [NeZero m] (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (bg : Fin n → Bool)
    (f : (Fin n → Bool) → Bool) (hf : Fixable f) :
    Fixable (fun y => f (cubeEmbed σ bg y)) := by
  intro τ
  obtain ⟨i_n, b, hexcl, c, hconst⟩ :=
    hf (fun j => if h : ∃ i, σ i = j then τ h.choose else some (bg j))
  by_cases hmem : ∃ i, σ i = i_n
  · -- the literal sits on a free coordinate: transfer it
    refine ⟨hmem.choose, b, ?_, c, fun y hy hyi => ?_⟩
    · intro hτ
      apply hexcl
      rw [dif_pos hmem]
      exact hτ
    · apply hconst (cubeEmbed σ bg y) (memCube_cubeEmbed σ bg τ y hy)
      rw [← hmem.choose_spec, cubeEmbed_apply_mem σ hσ]
      exact hyi
  · -- the literal sits on a frozen coordinate: the restriction is constant
    have hbg : bg i_n = b := by
      by_contra hne
      apply hexcl
      rw [dif_neg hmem]
      have hnot : bg i_n = !b := by cases hb : bg i_n <;> cases b <;> simp_all
      rw [hnot]
    obtain ⟨b₁, hleg⟩ : ∃ b₁ : Bool, τ 0 ≠ some (!b₁) := by
      cases hτ0 : τ 0 with
      | none => exact ⟨true, by simp⟩
      | some v => exact ⟨v, by simp⟩
    refine ⟨0, b₁, hleg, c, fun y hy _ => ?_⟩
    apply hconst (cubeEmbed σ bg y) (memCube_cubeEmbed σ bg τ y hy)
    simp only [cubeEmbed, dif_neg hmem]
    exact hbg

/-! ## §2 The embedding lower bound -/

/-- **Restriction/embedding lower bound (frozen).** If some restriction —
    an injection `σ` of `m` free coordinates with the rest frozen to `bg` —
    leaves the target everywhere-sensitive on the free coordinates, then no
    aggregator over `k < m` fixable witnesses computes the target. -/
theorem restriction_embedding_lower_bound {m n k : ℕ} {B : Type*}
    (hk : k < m) (σ : Fin m → Fin n) (hσ : Function.Injective σ)
    (bg : Fin n → Bool) (T : (Fin n → Bool) → B)
    (hsens : ∀ (y : Fin m → Bool) (j : Fin m),
      T (cubeEmbed σ bg (Function.update y j (!y j)))
        ≠ T (cubeEmbed σ bg y))
    (w : Fin k → (Fin n → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin k → Bool) → B) :
    (fun x => agg (fun i => w i x)) ≠ T := by
  intro heq
  haveI : NeZero m := ⟨by omega⟩
  apply fixable_witnesses_lower_bound hk (fun y => T (cubeEmbed σ bg y))
    hsens (fun i y => w i (cubeEmbed σ bg y))
    (fun i => fixable_restrict σ hσ bg (w i) (hfix i)) agg
  funext y
  exact congrFun heq (cubeEmbed σ bg y)

/-! ## §3 The win: inner product mod 2 -/

/-- Even slot of the `i`-th pair. -/
def evenIdx {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨2 * i.val, by omega⟩

/-- Odd slot of the `i`-th pair. -/
def oddIdx {m : ℕ} (i : Fin m) : Fin (2 * m) := ⟨2 * i.val + 1, by omega⟩

/-- Inner product mod 2 on `2m` bits: the parity of the pairwise ANDs. -/
def ip2 {m : ℕ} (x : Fin (2 * m) → Bool) : Bool :=
  parityN (fun i : Fin m => x (evenIdx i) && x (oddIdx i))

theorem evenIdx_injective {m : ℕ} :
    Function.Injective (evenIdx (m := m)) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [evenIdx] at hv
  exact Fin.ext (by omega)

theorem oddIdx_not_even {m : ℕ} (i : Fin m) :
    ¬ ∃ i', evenIdx i' = oddIdx i := by
  rintro ⟨i', h⟩
  have hv := congrArg Fin.val h
  simp only [evenIdx, oddIdx] at hv
  omega

/-- Freezing every odd coordinate to `true` restricts `ip2` to parity on
    the `m` even coordinates. -/
theorem ip2_embed {m : ℕ} (y : Fin m → Bool) :
    ip2 (cubeEmbed evenIdx (fun _ => true) y) = parityN y := by
  unfold ip2
  congr 1
  funext i
  rw [cubeEmbed_apply_mem evenIdx evenIdx_injective,
    cubeEmbed_apply_not_mem evenIdx _ _ _ (oddIdx_not_even i)]
  simp

/-- **`ip2` is NOT everywhere-sensitive (build-gated exhibit)**: at
    all-zeros on 4 bits, flipping the first coordinate changes nothing —
    its partner is dead. So `fixable_witnesses_lower_bound` cannot touch
    `ip2`; the embedding bound below can. -/
theorem ip2_not_everywhere_sensitive :
    ∃ (x : Fin (2 * 2) → Bool) (j : Fin (2 * 2)),
      ip2 (Function.update x j (!x j)) = ip2 x :=
  ⟨fun _ => false, ⟨0, by omega⟩, by decide⟩

/-- **INSTANCE.** Inner product mod 2 on `2m` bits needs ≥ m fixable
    witnesses: it embeds parity on the even coordinates, so no aggregator
    over `k < m` fixable witnesses computes it. -/
theorem ip2_needs_m_fixable_witnesses {m k : ℕ} (hk : k < m)
    (w : Fin k → (Fin (2 * m) → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin k → Bool) → Bool) :
    (fun x => agg (fun i => w i x)) ≠ ip2 :=
  restriction_embedding_lower_bound hk evenIdx evenIdx_injective
    (fun _ => true) ip2
    (fun y j => by rw [ip2_embed, ip2_embed]; exact parityN_update_ne y j)
    w hfix agg

/-- Non-vacuity at `m = 2`: a REAL single-head witness on 4 bits — an
    indicator head, fixable by `headOutput_fixable` — fails against `ip2`
    for every aggregator. -/
theorem ip2_four_bits_one_head_fails :
    ∀ agg : (Fin 1 → Bool) → Bool,
      (fun x : Fin (2 * 2) → Bool =>
        agg (fun _ => headOutput (indicatorHead (fun _ => true)) x))
      ≠ ip2 :=
  fun agg => ip2_needs_m_fixable_witnesses (by norm_num)
    (fun _ => headOutput (indicatorHead (fun _ => true)))
    (fun _ => headOutput_fixable _) agg

end
