/-
  AttentionLean.WitnessMajority

  Majority, settled for the fixable-witness model.

  STEP 0 — VERDICT (frozen): **HARD**, with a linear lower bound —
  `maj` on `n` bits needs `k ≥ ⌈n/2⌉` fixable witnesses (theorem below:
  any aggregator over `k` fixable witnesses with `2k < n` is refuted).
  One-line reason: the refutation kernel needs only SOME target-separated
  pair on the pinned subcube — not a sensitive edge — and majority stays
  non-constant on every subcube with fewer than `n/2` pinned coordinates
  (all-free-zeros has at most `k` ones, all-free-ones at least `n − k`).
  The "steering to a balanced sensitive point" route from the task brief
  is thus unnecessary: plain subcube non-constancy already fires.

  THE RIGHT MEASURE. `fixable_witnesses_lower_bound_of_nonconstant`: if a
  target is non-constant on EVERY subcube with at most `k` pinned
  coordinates, no aggregator over `k` fixable witnesses computes it. This
  is a certificate-complexity-flavoured measure: a target constant on a
  subcube is "certified" by its pins, so the theorem reads — `k` fixable
  witnesses cannot compute a target whose smallest certificate exceeds
  `k`. It subsumes the everywhere-sensitivity route conceptually (an
  everywhere-sensitive target is non-constant on any subcube with a free
  coordinate: flip it), and it is exactly what majority needs: a majority
  certificate requires ⌈(n+1)/2⌉ pinned agreeing votes, so `k < n/2` pins
  never certify.

  SCOPE BRACKET (honest): majority IS computable by `n` fixable
  witnesses — the dictators are fixable and the aggregator can be `maj`
  itself (`maj_computable_by_n_fixable`). So `⌈n/2⌉ ≤ k(maj_n) ≤ n`,
  both ends machine-checked; the exact constant between them is OPEN
  here. This vindicates the WitnessEmbedding OUT-verdict in the precise
  sense: majority escapes the parity-embedding technique yet is still
  hard — it needed this different measure, as predicted there.

  Non-vacuity: `maj` value guards; `maj3_one_head_fails` — a real single
  indicator-head witness on 3 bits refuted for every aggregator
  (`2·1 < 3`).

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessTheory

open Classical

noncomputable section

/-- Strict majority: true iff more than half the bits are set. -/
def maj {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (n < 2 * (Finset.univ.filter fun i => x i = true).card)

-- Build-gated value witnesses on 3 bits.
#guard maj (fun _ : Fin 3 => true) == true
#guard maj (fun _ : Fin 3 => false) == false
#guard maj (fun i : Fin 3 => decide (i.val < 2)) == true
#guard maj (fun i : Fin 3 => decide (i.val < 1)) == false

/-! ## §1 The subcube-nonconstancy lower bound (the right measure) -/

/-- **Lower bound from subcube non-constancy.** If the target is
    non-constant on every subcube with at most `k` pinned coordinates,
    then no aggregator over `k` fixable witnesses computes it. The kernel
    needs only a separated pair, not a sensitive edge. -/
theorem fixable_witnesses_lower_bound_of_nonconstant {n k : ℕ} {B : Type*}
    (T : (Fin n → Bool) → B)
    (hT : ∀ ρ : Fin n → Option Bool, (pins ρ).card ≤ k →
      ∃ x y, memCube ρ x ∧ memCube ρ y ∧ T x ≠ T y)
    (w : Fin k → (Fin n → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin k → Bool) → B) :
    (fun x => agg (fun i => w i x)) ≠ T := by
  obtain ⟨ρ', hcard, -, hconst⟩ := fixable_pin_list (List.ofFn w)
    (by
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact hfix i)
    (fun _ => none)
  have hk' : (pins ρ').card ≤ k := by
    have h0 : (pins (fun _ : Fin n => none)).card = 0 := by simp [pins]
    rw [h0, List.length_ofFn] at hcard
    omega
  obtain ⟨x, y, hx, hy, hTxy⟩ := hT ρ' hk'
  refine witness_separation_fails T w agg x y (fun i => ?_) hTxy
  obtain ⟨c, hc⟩ := hconst (w i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  rw [hc x hx, hc y hy]

/-! ## §2 Majority is non-constant on small subcubes -/

/-- With fewer than `n/2` pins, majority is non-constant on the subcube:
    all-free-zeros has at most `k` ones, all-free-ones at least `n − k`. -/
theorem maj_nonconstant_on_small_subcubes {n k : ℕ} (hk : 2 * k < n)
    (ρ : Fin n → Option Bool) (hρ : (pins ρ).card ≤ k) :
    ∃ x y, memCube ρ x ∧ memCube ρ y ∧ maj x ≠ maj y := by
  refine ⟨fun j => (ρ j).getD false, fun j => (ρ j).getD true, ?_, ?_, ?_⟩
  · intro j bj hj
    simp [hj]
  · intro j bj hj
    simp [hj]
  · have hsub0 : (Finset.univ.filter fun j => (ρ j).getD false = true)
        ⊆ pins ρ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [pins, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hρj : ρ j with
      | none => rw [hρj] at hj; simp at hj
      | some b => simp
    have hsub1 : (Finset.univ.filter fun j => ¬ ((ρ j).getD true = true))
        ⊆ pins ρ := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [pins, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hρj : ρ j with
      | none => rw [hρj] at hj; simp at hj
      | some b => simp
    have hc0 : (Finset.univ.filter fun j => (ρ j).getD false = true).card ≤ k :=
      le_trans (Finset.card_le_card hsub0) hρ
    have hc1 : (Finset.univ.filter fun j => ¬ ((ρ j).getD true = true)).card
        ≤ k :=
      le_trans (Finset.card_le_card hsub1) hρ
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => (ρ j).getD true = true)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    have h0 : maj (fun j => (ρ j).getD false) = false := by
      simp only [maj, decide_eq_false_iff_not]
      omega
    have h1 : maj (fun j => (ρ j).getD true) = true := by
      simp only [maj, decide_eq_true_eq]
      omega
    rw [h0, h1]
    simp

/-! ## §3 The verdict, both ends -/

/-- **MAJORITY IS HARD (lower bound).** Any aggregator over `k` fixable
    witnesses with `2k < n` fails against strict majority on `n` bits:
    `k(maj_n) ≥ ⌈n/2⌉`. -/
theorem maj_needs_half_fixable_witnesses {n k : ℕ} (hk : 2 * k < n)
    (w : Fin k → (Fin n → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin k → Bool) → Bool) :
    (fun x => agg (fun i => w i x)) ≠ maj :=
  fixable_witnesses_lower_bound_of_nonconstant maj
    (fun ρ hρ => maj_nonconstant_on_small_subcubes hk ρ hρ) w hfix agg

/-- Dictators are fixable: on any subcube, pinning their own coordinate
    (respecting an existing pin) makes them constant. -/
theorem dictator_fixable {n : ℕ} (i : Fin n) : Fixable (fun x => x i) := by
  intro ρ
  cases hρ : ρ i with
  | none => exact ⟨i, true, by simp [hρ], true, fun x _ hx => hx⟩
  | some v => exact ⟨i, v, by simp [hρ], v, fun x _ hx => hx⟩

/-- **The scope bracket (upper end).** Majority IS computable by `n`
    fixable witnesses: the dictators, aggregated by `maj` itself. So
    `⌈n/2⌉ ≤ k(maj_n) ≤ n`; the exact constant is open here. -/
theorem maj_computable_by_n_fixable {n : ℕ} :
    ∃ w : Fin n → (Fin n → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin n → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj :=
  ⟨fun i x => x i, dictator_fixable, maj, rfl⟩

/-- Non-vacuity: a REAL single-head witness on 3 bits — an indicator head,
    fixable by `headOutput_fixable` — fails against `maj` for every
    aggregator (`2·1 < 3`). -/
theorem maj3_one_head_fails :
    ∀ agg : (Fin 1 → Bool) → Bool,
      (fun x : Fin 3 → Bool =>
        agg (fun _ => headOutput (indicatorHead (fun _ => true)) x)) ≠ maj :=
  fun agg => maj_needs_half_fixable_witnesses (by norm_num)
    (fun _ => headOutput (indicatorHead (fun _ => true)))
    (fun _ => headOutput_fixable _) agg

end
