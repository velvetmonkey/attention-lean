/-
  AttentionLean.WitnessTheory

  From the refutation kernel to a small standalone theory: the exact
  characterization of witness-computability, a quantitative counting lower
  bound, and the general fixable-witness lower bound that the parity proof
  is an instance of.

  FROZEN CONCLUSIONS (before proving):

  1. CHARACTERIZATION — `witness_computable_iff_refines`:
       (∃ agg, (fun s => agg (fun i => w i s)) = T)
         ↔ (∀ s s', (∀ i, w i s = w i s') → T s = T s')
     Some aggregator computes T iff the witness map `W s := fun i => w i s`
     refines T (T constant on W's fibres). Forward direction is the
     kernel's generalization; reverse is constructive on the image of W
     (`Classical.choice` off it). `[Nonempty S]` is required: with S empty
     but `Fin k → V` inhabited and B empty, the right side is vacuously
     true while no aggregator exists. The refutation kernel
     `witness_separation_fails` is re-derived as the one-pair
     contrapositive (`witness_separation_fails_of_char`).

  2. COUNTING BOUND — `witness_counting_bound`: with witness values in a
     finite V, if some aggregator computes T and T is injective on a
     finite A ⊆ S, then |A| ≤ |V|^k — i.e. k ≥ log_|V| |A|.
     HONEST SCOPE: this bites only for high-IMAGE targets. Parity is
     2-valued (any singleton A works, |A| = 1), so this does NOT recover
     k(n) ≥ n for parity; it is the information-capacity bound, not the
     sensitivity bound. Instance (tight, build-gated): the identity on
     `Fin 4` cannot be computed by one Bool-valued witness
     (`id_fin4_one_bool_witness_fails`, 4 ≤ 2 fails) and IS computed by
     two (`id_fin4_two_bool_witnesses_suffice`, by kernel `decide`).

  3. FIXABLE-WITNESS LOWER BOUND — STEP-0 ASSESSMENT: does
     `parityN_requires_N_heads` factor through a clean (target measure,
     witness capacity) pair? YES. Inspecting `ParityN.lean`: the witness
     class enters ONLY through `headOutput_fixable` (every head output is
     `Fixable` — on any subcube one pinned literal makes it constant: the
     capacity measure, "1-fixability"); the target enters ONLY through
     `parityN_update_ne` (parity flips under every single-coordinate
     update: the richness measure, everywhere-1-sensitivity on all n
     coordinates). The collision induction (`collision_of_fixable`) pins
     at most one coordinate per witness and flips a leftover free
     coordinate; its parity-specific conclusion ("opposite parity") is
     just the sensitivity of the target applied to that single flip.
     General theorem — `fixable_witnesses_lower_bound`: an everywhere-
     sensitive target on n Boolean coordinates is computed by NO
     aggregator over k < n fixable witnesses. So: measure m = n sensitive
     coordinates forces ≥ n fixable witnesses, for ANY aggregator —
     strictly more general than the landed theorem, which fixes the
     aggregator to a thresholded affine readout. Parity is recovered as
     the corollary `parityN_requires_N_heads_of_witness_theory`, verbatim
     the landed statement (which stays untouched). Non-vacuity: the
     concrete instance `parity3_two_fixable_witnesses_fail` — two real
     indicator heads against parity3, every aggregator refuted.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessSeparation
import AttentionLean.ParityN

open Classical

noncomputable section

/-! ## §1 The characterization -/

/-- **Witness computability, characterized.** Some aggregator computes the
    target iff the witness map refines it: the target is constant on the
    fibres of `s ↦ (fun i => w i s)`. -/
theorem witness_computable_iff_refines {S V B : Type*} [Nonempty S] {k : ℕ}
    (T : S → B) (w : Fin k → S → V) :
    (∃ agg : (Fin k → V) → B, (fun s => agg (fun i => w i s)) = T) ↔
    (∀ s s', (∀ i, w i s = w i s') → T s = T s') := by
  constructor
  · rintro ⟨agg, hagg⟩ s s' hw
    calc T s = agg (fun i => w i s) := (congrFun hagg s).symm
      _ = agg (fun i => w i s') := by rw [funext hw]
      _ = T s' := congrFun hagg s'
  · intro href
    refine ⟨fun v => if h : ∃ s, (fun i => w i s) = v then T h.choose
      else T (Classical.arbitrary S), ?_⟩
    funext s
    have hex : ∃ t, (fun i => w i t) = (fun i => w i s) := ⟨s, rfl⟩
    simp only [dif_pos hex]
    exact href _ _ (fun i => congrFun hex.choose_spec i)

/-- The refutation kernel, re-derived as the one-pair contrapositive of the
    characterization (the colliding pair inhabits `S`). -/
theorem witness_separation_fails_of_char {S V B : Type*} {k : ℕ}
    (T : S → B) (w : Fin k → S → V) (agg : (Fin k → V) → B)
    (s s' : S) (hw : ∀ i, w i s = w i s') (hT : T s ≠ T s') :
    (fun t => agg (fun i => w i t)) ≠ T := by
  intro heq
  have : Nonempty S := ⟨s⟩
  exact hT ((witness_computable_iff_refines T w).mp ⟨agg, heq⟩ s s' hw)

/-! ## §2 The counting lower bound (information capacity)

For high-image targets only — see the docstring scope note. -/

/-- **Counting bound.** Finite witness values: computing a target injective
    on a finite `A` forces `|A| ≤ |V|^k`, i.e. `k ≥ log_|V| |A|`. -/
theorem witness_counting_bound {S V B : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (T : S → B) (w : Fin k → S → V) (agg : (Fin k → V) → B)
    (hcomp : (fun s => agg (fun i => w i s)) = T)
    (A : Finset S) (hinj : Set.InjOn T A) :
    A.card ≤ Fintype.card V ^ k := by
  classical
  have hle : A.card ≤ (Finset.univ : Finset (Fin k → V)).card := by
    apply Finset.card_le_card_of_injOn (fun s => (fun i => w i s))
      (fun a _ => Finset.mem_univ _)
    intro a ha a' ha' hW
    apply hinj ha ha'
    have hW' : (fun i => w i a) = (fun i => w i a') := hW
    calc T a = agg (fun i => w i a) := (congrFun hcomp a).symm
      _ = agg (fun i => w i a') := by rw [hW']
      _ = T a' := congrFun hcomp a'
  calc A.card ≤ (Finset.univ : Finset (Fin k → V)).card := hle
    _ = Fintype.card V ^ k := by
      simp [Finset.card_univ]

/-- The two bits of a `Fin 4` index. -/
def bitsOf : Fin 2 → Fin 4 → Bool
  | 0 => fun s => decide (s.val % 2 = 1)
  | 1 => fun s => decide (2 ≤ s.val)

/-- Decode two bits back into a `Fin 4` index. -/
def decode2 (v : Fin 2 → Bool) : Fin 4 :=
  ⟨(if v 0 then 1 else 0) + (if v 1 then 2 else 0), by split <;> split <;> omega⟩

/-- **Tightness, upper half (build-gated by kernel `decide`)**: two
    Bool-valued witnesses compute the identity on `Fin 4`. -/
theorem id_fin4_two_bool_witnesses_suffice :
    (fun s => decode2 (fun i => bitsOf i s)) = (id : Fin 4 → Fin 4) := by
  decide

/-- **Counting-bound instance, lower half**: the identity on `Fin 4` (image
    size 4) is computed by NO single Bool-valued witness — `4 ≤ 2¹` fails. -/
theorem id_fin4_one_bool_witness_fails
    (w : Fin 1 → Fin 4 → Bool) (agg : (Fin 1 → Bool) → Fin 4) :
    (fun s => agg (fun i => w i s)) ≠ (id : Fin 4 → Fin 4) := by
  intro heq
  have h := witness_counting_bound id w agg heq Finset.univ
    Function.injective_id.injOn
  simp at h

/-! ## §3 The fixable-witness lower bound (sensitivity)

The general theorem behind `parityN_requires_N_heads`: witness capacity =
`Fixable` (one pinned literal per subcube makes the witness constant),
target richness = everywhere-1-sensitivity. -/

/-- The pinned coordinates of a partial assignment. -/
def pins {n : ℕ} (ρ : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ρ j ≠ none)

/-- **Pinning induction.** A list of fixable functions can be made
    simultaneously constant on a common subcube refining `ρ`, pinning at
    most one coordinate per function. -/
theorem fixable_pin_list {n : ℕ} :
    ∀ (L : List ((Fin n → Bool) → Bool)), (∀ f ∈ L, Fixable f) →
    ∀ ρ : Fin n → Option Bool,
    ∃ ρ' : Fin n → Option Bool,
      (pins ρ').card ≤ (pins ρ).card + L.length ∧
      (∀ x, memCube ρ' x → memCube ρ x) ∧
      (∀ f ∈ L, ∃ c, ∀ x, memCube ρ' x → f x = c)
  | [], _, ρ =>
      ⟨ρ, by simp, fun _ h => h, fun _ hf => nomatch hf⟩
  | f :: L, hfix, ρ => by
      obtain ⟨i, b, hexcl, c, hconst⟩ := hfix f List.mem_cons_self ρ
      have hsub₁ : ∀ x, memCube (fun j => if j = i then some b else ρ j) x →
          memCube ρ x := by
        intro x hx j bj hj
        by_cases hji : j = i
        · subst hji
          have hbj : bj = b := by
            by_contra hne
            apply hexcl
            rw [hj]
            have : bj = !b := by cases bj <;> cases b <;> simp_all
            rw [this]
          subst hbj
          exact hx j bj (by simp)
        · exact hx j bj (by simp [hji, hj])
      have hx_i : ∀ x, memCube (fun j => if j = i then some b else ρ j) x →
          x i = b := fun x hx => hx i b (by simp)
      have hcard₁ : (pins (fun j => if j = i then some b else ρ j)).card
          ≤ (pins ρ).card + 1 := by
        have hsubset : pins (fun j => if j = i then some b else ρ j)
            ⊆ insert i (pins ρ) := by
          intro j hj
          rcases eq_or_ne j i with rfl | hne
          · exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            simp only [pins, Finset.mem_filter, Finset.mem_univ, true_and,
              if_neg hne] at hj ⊢
            exact hj
        calc (pins (fun j => if j = i then some b else ρ j)).card
            ≤ (insert i (pins ρ)).card := Finset.card_le_card hsubset
          _ ≤ (pins ρ).card + 1 := Finset.card_insert_le _ _
      obtain ⟨ρ', hcard', hsub', hconst'⟩ :=
        fixable_pin_list L (fun g hg => hfix g (List.mem_cons_of_mem _ hg))
          (fun j => if j = i then some b else ρ j)
      refine ⟨ρ', ?_, fun x hx => hsub₁ x (hsub' x hx), ?_⟩
      · calc (pins ρ').card
            ≤ (pins (fun j => if j = i then some b else ρ j)).card + L.length :=
              hcard'
          _ ≤ (pins ρ).card + 1 + L.length := by omega
          _ = (pins ρ).card + (f :: L).length := by
              simp [List.length_cons]
              omega
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hgL
        · exact ⟨c, fun x hx =>
            hconst x (hsub₁ x (hsub' x hx)) (hx_i x (hsub' x hx))⟩
        · exact hconst' g hgL

/-- **The generic collision.** Fewer fixable witnesses than coordinates
    admit a point and a coordinate on which flipping changes NO witness. -/
theorem exists_flip_collision {n k : ℕ} (hk : k < n)
    (w : Fin k → (Fin n → Bool) → Bool) (hfix : ∀ i, Fixable (w i)) :
    ∃ (x : Fin n → Bool) (j : Fin n),
      ∀ i, w i x = w i (Function.update x j (!x j)) := by
  obtain ⟨ρ', hcard, -, hconst⟩ := fixable_pin_list (List.ofFn w)
    (by
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact hfix i)
    (fun _ => none)
  have hcard' : (pins ρ').card ≤ k := by
    have h0 : (pins (fun _ : Fin n => none)).card = 0 := by
      simp [pins]
    rw [h0, List.length_ofFn] at hcard
    omega
  have hfree : ∃ j, ρ' j = none := by
    by_contra hall
    push_neg at hall
    have huniv : pins ρ' = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      simp [pins, hall j]
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard'
    omega
  obtain ⟨j, hj⟩ := hfree
  refine ⟨fun m => (ρ' m).getD false, j, fun i => ?_⟩
  have hmem : memCube ρ' (fun m => (ρ' m).getD false) := by
    intro m bm hm
    simp [hm]
  have hmem' : memCube ρ'
      (Function.update (fun m => (ρ' m).getD false) j
        (!(fun m => (ρ' m).getD false) j)) := by
    intro m bm hm
    rcases eq_or_ne m j with rfl | hne
    · rw [hj] at hm
      cases hm
    · rw [Function.update_of_ne hne]
      simp [hm]
  obtain ⟨c, hc⟩ := hconst (w i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  rw [hc _ hmem, hc _ hmem']

/-- **STRETCH (b) — the general lower bound.** An everywhere-sensitive
    target on `n` Boolean coordinates (every single-coordinate flip changes
    it, anywhere) is computed by NO aggregator over `k < n` fixable
    witnesses. The abstract form of `parityN_requires_N_heads`: capacity =
    `Fixable`, richness = everywhere-1-sensitivity; strictly more general
    in the aggregator (any decision rule, not just a threshold). -/
theorem fixable_witnesses_lower_bound {n k : ℕ} {B : Type*} (hk : k < n)
    (T : (Fin n → Bool) → B)
    (hsens : ∀ x j, T (Function.update x j (!x j)) ≠ T x)
    (w : Fin k → (Fin n → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin k → Bool) → B) :
    (fun x => agg (fun i => w i x)) ≠ T := by
  obtain ⟨x, j, hcol⟩ := exists_flip_collision hk w hfix
  exact witness_separation_fails T w agg x (Function.update x j (!x j))
    hcol (Ne.symm (hsens x j))

/-- **Parity recovered as a corollary** — verbatim the landed
    `parityN_requires_N_heads` statement, now an instance of the general
    bound: `parityN` is everywhere-sensitive (`parityN_update_ne`), heads
    are fixable (`headOutput_fixable`), the threshold is one aggregator. -/
theorem parityN_requires_N_heads_of_witness_theory {n k d : ℕ} [NeZero n]
    (hk : k < n) (h : Fin k → HardAttentionHead n d) (w : Fin k → ℝ)
    (bias : ℝ) :
    ¬ (∀ x : Fin n → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = parityN x) := by
  intro hyp
  exact fixable_witnesses_lower_bound hk parityN
    (fun x j => parityN_update_ne x j)
    (fun i => headOutput (h i)) (fun i => headOutput_fixable (h i))
    (fun v => if (∑ i, w i * (if v i then (1 : ℝ) else 0)) + bias > 0
      then true else false)
    (funext fun x => hyp x)

/-- Non-vacuity for the general bound: two REAL fixable witnesses — indicator
    heads at two basis points — cannot compute parity3, for ANY aggregator. -/
theorem parity3_two_fixable_witnesses_fail :
    ∀ agg : (Fin 2 → Bool) → Bool,
      (fun x : Fin 3 → Bool =>
        agg (fun i => headOutput (indicatorHead (offPoint i.succ)) x))
      ≠ parityN :=
  fun agg => fixable_witnesses_lower_bound (by norm_num) parityN
    (fun x j => parityN_update_ne x j)
    (fun i => headOutput (indicatorHead (offPoint i.succ)))
    (fun _ => headOutput_fixable _) agg

end
