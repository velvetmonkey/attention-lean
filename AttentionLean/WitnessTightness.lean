/-
  AttentionLean.WitnessTightness

  Tightness for the witness ladder: exact witness numbers where they close,
  the honest bracket where they do not.

  FROZEN VERDICTS (Step 0, before proving):

  * maj₃ — **k(maj₃) = 2**: the certificate lower bound (`2·1 < 3` kills
    one witness) is TIGHT at n = 3. Construction:
      w₁ = x₀ ∨ (x₁ ∧ x₂),   w₂ = x₀ ∧ ¬x₁ ∧ ¬x₂,   maj₃ = w₁ ∧ ¬w₂.
    Fibres: (0,0) = {000,001,010} (maj 0), (1,1) = {100} (maj 0),
    (1,0) = {011,101,110,111} (maj 1). Both witnesses are decision lists,
    hence `Fixable`; at n = 3 `Fixable` is a finite statement, so the
    fixability proofs are kernel `decide`.

  * maj_n, general — bracket UNCHANGED: ⌈n/2⌉ ≤ k(maj_n) ≤ n. One-line
    blocker for closing it: the n = 3 carve-out does not compose — the
    median recursion med_n = med₃(x₁, x₂, med_{n−2}) is FALSE (witness
    (1,1,0,0,0)), and no fixable decomposition of maj₅ into 3 witnesses
    was found; maj₅ (k ∈ {3, 4}) is the smallest open case.

  * General tightness (STRETCH). The certificate rung's operational
    measure is the minimum number of pinned coordinates that make the
    target constant on a subcube (minimal certificate size): the rung
    gives k(T) ≥ minCert(T) (with k := minCert(T) − 1 pins, minimality
    makes every subcube non-constant). The matching-upper-bound question
    — k(T) = minCert(T) for every Boolean target — is left OPEN, but is
    here CONFIRMED EXACTLY on three families:
      parity_n : k = n        (lower: sensitivity rung; upper: dictators)
      ip2 (2m) : k = m        (lower: embedding rung; upper: AND-pairs +
                               parity aggregator — the upper end is `rfl`)
      maj₃     : k = 2        (lower: certificate rung; upper: this file)
    No gap example was found; every candidate tried (mux₃, exactly-one₃,
    xor-with-dummies) also closed at its certificate number during the
    assessment. The general upper-bound construction is the open half.

  * The trivial upper end, stated once and generally: EVERY target on n
    Boolean coordinates is computable by the n dictators
    (`every_target_computable_by_n_dictators`) — so all witness numbers
    live in [minCert(T), n].

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessMajority
import AttentionLean.WitnessEmbedding

open Classical

noncomputable section

/-! ## §1 The trivial upper end, once and for all -/

/-- Every target on `n` Boolean coordinates is computable by the `n`
    dictators (aggregate with the target itself). All witness numbers sit
    in `[·, n]`. -/
theorem every_target_computable_by_n_dictators {n : ℕ} {B : Type*}
    (T : (Fin n → Bool) → B) :
    ∃ w : Fin n → (Fin n → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin n → Bool) → B, (fun x => agg (fun i => w i x)) = T :=
  ⟨fun i x => x i, dictator_fixable, T, rfl⟩

/-! ## §2 maj₃: the certificate bound is tight -/

/-- `memCube` is a finite conjunction; make its decidability available to
    the kernel `decide` used for the small fixability proofs below. -/
instance {n : ℕ} (ρ : Fin n → Option Bool) (x : Fin n → Bool) :
    Decidable (memCube ρ x) := by
  unfold memCube
  infer_instance

/-- First witness: `x₀ ∨ (x₁ ∧ x₂)` — a decision list. -/
def majW1 : (Fin 3 → Bool) → Bool := fun x => x 0 || (x 1 && x 2)

/-- Second witness: `x₀ ∧ ¬x₁ ∧ ¬x₂` — carves the lone bad corner out of
    the first witness's true-set. -/
def majW2 : (Fin 3 → Bool) → Bool := fun x => x 0 && !(x 1) && !(x 2)

theorem majW1_fixable : Fixable majW1 := by
  unfold Fixable
  decide

theorem majW2_fixable : Fixable majW2 := by
  unfold Fixable
  decide

/-- The construction computes strict majority on 3 bits (kernel `decide`
    over the 8-point cube — build-gated non-vacuity). -/
theorem maj3_eq_two_witness_combination :
    (fun x => majW1 x && !(majW2 x)) = (maj : (Fin 3 → Bool) → Bool) := by
  decide

/-- **maj₃ upper bound: two fixable witnesses suffice.** -/
theorem maj3_computable_by_two_fixable :
    ∃ w : Fin 2 → (Fin 3 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 2 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj := by
  refine ⟨![majW1, majW2], ?_, fun v => v 0 && !(v 1), ?_⟩
  · intro i
    fin_cases i
    · exact majW1_fixable
    · exact majW2_fixable
  · exact maj3_eq_two_witness_combination

/-- **k(maj₃) = 2, both ends.** Two fixable witnesses compute strict
    majority on 3 bits; one cannot (certificate rung, `2·1 < 3`). The
    ⌈n/2⌉ certificate lower bound is TIGHT at n = 3. -/
theorem maj3_witness_number_exact :
    (∃ w : Fin 2 → (Fin 3 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 2 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj) ∧
    (∀ w : Fin 1 → (Fin 3 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 1 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ maj) :=
  ⟨maj3_computable_by_two_fixable,
   fun w hfix agg => maj_needs_half_fixable_witnesses (by norm_num) w hfix agg⟩

/-! ## §3 Tightness instances: parity and inner product -/

/-- **k(parity_n) = n, both ends.** Dictators aggregated by `parityN`
    compute it; fewer than `n` fixable witnesses cannot (sensitivity
    rung). -/
theorem parityN_witness_number_exact {n : ℕ} :
    (∃ w : Fin n → (Fin n → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin n → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = parityN) ∧
    (∀ k, k < n → ∀ w : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin k → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ parityN) :=
  ⟨⟨fun i x => x i, dictator_fixable, parityN, rfl⟩,
   fun _ hk w hfix agg => fixable_witnesses_lower_bound hk parityN
     (fun x j => parityN_update_ne x j) w hfix agg⟩

/-- The AND of two coordinates is fixable: kill the first coordinate if
    its pin allows, else it is pinned and the second coordinate decides. -/
theorem and_pair_fixable {n : ℕ} (a b : Fin n) :
    Fixable (fun x => x a && x b) := by
  intro ρ
  cases hρa : ρ a with
  | none =>
      exact ⟨a, false, by simp [hρa], false, fun x _ hx => by simp [hx]⟩
  | some va =>
      cases va with
      | false =>
          exact ⟨a, false, by simp [hρa], false, fun x _ hx => by simp [hx]⟩
      | true =>
          cases hρb : ρ b with
          | none =>
              exact ⟨b, false, by simp [hρb], false, fun x _ hx => by
                simp [hx]⟩
          | some vb =>
              refine ⟨b, vb, by simp [hρb], vb, fun x hcube hx => ?_⟩
              have hxa : x a = true := hcube a true hρa
              show (x a && x b) = vb
              rw [hxa, hx]
              simp

/-- **k(ip2) = m, both ends.** The `m` pair-ANDs are fixable and `ip2` is
    definitionally their parity (the upper end is `rfl`); fewer than `m`
    fixable witnesses cannot compute it (embedding rung). Tightness for a
    target that everywhere-sensitivity provably cannot reach. -/
theorem ip2_witness_number_exact {m : ℕ} :
    (∃ w : Fin m → (Fin (2 * m) → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin m → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = ip2) ∧
    (∀ k, k < m → ∀ w : Fin k → (Fin (2 * m) → Bool) → Bool,
      (∀ i, Fixable (w i)) →
      ∀ agg : (Fin k → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ ip2) :=
  ⟨⟨fun i x => x (evenIdx i) && x (oddIdx i),
    fun i => and_pair_fixable (evenIdx i) (oddIdx i), parityN, rfl⟩,
   fun _ hk w hfix agg => ip2_needs_m_fixable_witnesses hk w hfix agg⟩

end
