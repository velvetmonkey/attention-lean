/-
  AttentionLean.WitnessMaj5Lower

  Toward k(maj₅) ≥ 4 in Lean: the structural reduction, formalized.

  STEP-0 SCOPE (frozen before proving — rung discipline). The full lower
  bound k(maj₅) ≥ 4 rests on the three-case analysis validated by
  scripts/maj5_witness_search.py. Porting ALL of it needs a structural
  classification of the 24-pair threshold catalogs over Fixable(4) — a
  Parity3Clean-scale cascade that does NOT fit this window. What THIS
  module lands, each rung clean and final:

  R1 — TOOLS.
    * `fixable_const_halfcube` : every fixable witness is constant on some
      half-cube (the forcing literal at the empty restriction).
    * `fixable_update_restrict` : pinning one coordinate of a fixable
      witness (same-dimension restriction `fun y => f (update y i v)`)
      yields a fixable witness — the recursion tool the future catalog
      cascade needs.
    * `maj_nonconst_of_pin_bounds` : majority is non-constant on any
      subcube with at most `n/2` TRUE-pins and fewer than `n/2`
      FALSE-pins — the refined certificate lemma (the shipped
      `maj_nonconstant_on_small_subcubes` bounds total pins; this one
      bounds each sign separately, which is what mixed-sign kills need).

  R2 — CASE 1, CLOSED (`maj5_shared_face_kill`): if two of the three
    fixable witnesses are constant on a COMMON half-cube, no aggregator
    computes maj₅. Pure fiber language, no catalogs: the third witness's
    forcing literal at the shared face yields a ≤ 2-pin subcube on which
    all three witnesses are constant, and majority is non-constant on
    every ≤ 2-pin subcube of the 5-cube (2·2 < 5) — the collision kernel
    fires. Non-vacuity: the shipped construction's own first two
    witnesses share the face {x₀ = false}, so
    `maj5_W1W2_not_completable`: {maj5W1, maj5W2} extends to NO
    3-witness family, whatever the third fixable witness and aggregator.

  R3 — PARTIAL: the reduction theorem (`maj5_reduction`). Any 3 fixable
    witnesses computing maj₅ carry constancy half-cubes with
    (a) pairwise-DISTINCT signed directions (case 1 dead), and
    (b) if the three directions are pairwise distinct, the three signs
        are UNANIMOUS (`maj5_mixed_signs_kill`: mixed signs leave the
        triple-overlap subcube with ≤ 2 true-pins and ≤ 2 false-pins,
        where majority is non-constant while all witnesses collide).
    So every surviving configuration is exactly one of the two shapes the
    search killed by catalog: shared-direction-opposite-signs (case 2) or
    all-distinct-unanimous-signs (case 3).

  NOT LANDED HERE (stated plainly, future work): the case-2 and
  uniform-sign case-3 kills — they need the classification of fixable
  pairs refining T₂⁴/T₃⁴ (the 24-pair catalogs; kernel `decide` cannot
  sweep 2^16-function spaces, so this requires a decision-list normal
  form for Fixable(4) — for which `fixable_update_restrict` is the
  recursion step — and a Parity3Clean-style parametrized cascade).
  Consequently `maj5_witness_number_exact` is NOT claimed;
  `maj5_witness_bracket` (3 ≤ k(maj₅) ≤ 4, kernel-checked) stands, and
  k(maj₅) = 4 exactly remains pinned by the exhaustive search evidence.

  LADDER STATUS after this module: kernel-proved exact witness numbers —
  parity_n = n, ip2 = m, maj₃ = 2; kernel-proved bracket 3 ≤ k(maj₅) ≤ 4
  plus the reduction above; k(maj₅) = 4 search-pinned. Next frontier:
  finish the catalog cascade, then maj₇ (certificate rung gives ≥ 4;
  bracket [4, 7] open).

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessMaj5

open Classical

noncomputable section

/-! ## §1 R1 — tools -/

/-- Every fixable witness is constant on some half-cube: the forcing
    literal at the empty restriction. -/
theorem fixable_const_halfcube {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Fixable f) :
    ∃ i b c, ∀ x : Fin n → Bool, x i = b → f x = c := by
  obtain ⟨i, b, -, c, hc⟩ := hf (fun _ => none)
  exact ⟨i, b, c, fun x hx => hc x (fun _ _ hmem => nomatch hmem) hx⟩

/-- Pinning one coordinate of a fixable witness yields a fixable witness
    (same-dimension restriction). The recursion tool for the future
    catalog cascade. -/
theorem fixable_update_restrict {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : Fixable f) (i : Fin n) (v : Bool) :
    Fixable (fun y => f (Function.update y i v)) := by
  intro ρ
  obtain ⟨j, b, hexcl, c, hconst⟩ :=
    hf (fun m => if m = i then some v else ρ m)
  have hmem : ∀ y : Fin n → Bool, memCube ρ y →
      memCube (fun m => if m = i then some v else ρ m)
        (Function.update y i v) := by
    intro y hy m bm hm
    have hm' : (if m = i then some v else ρ m) = some bm := hm
    by_cases hmi : m = i
    · subst hmi
      rw [if_pos rfl] at hm'
      cases hm'
      simp
    · rw [if_neg hmi] at hm'
      rw [Function.update_of_ne hmi]
      exact hy m bm hm'
  by_cases hji : j = i
  · -- the literal is the pinned coordinate, forced to `v`: the
    -- restriction is constant on the whole subcube
    subst hji
    have hbv : b = v := by
      by_contra hne
      apply hexcl
      rw [if_pos rfl]
      have hv : v = !b := by cases v <;> cases b <;> simp_all
      rw [hv]
    obtain ⟨b₁, hleg⟩ : ∃ b₁ : Bool, ρ 0 ≠ some (!b₁) := by
      cases hρ0 : ρ 0 with
      | none => exact ⟨true, by simp⟩
      | some u => exact ⟨u, by simp⟩
    refine ⟨0, b₁, hleg, c, fun y hy _ => ?_⟩
    exact hconst _ (hmem y hy) (by rw [Function.update_self, hbv])
  · -- the literal transfers
    refine ⟨j, b, ?_, c, fun y hy hyj => ?_⟩
    · intro hτ
      apply hexcl
      rw [if_neg hji]
      exact hτ
    · exact hconst _ (hmem y hy)
        (by rw [Function.update_of_ne hji]; exact hyj)

/-- **Refined certificate lemma.** Majority is non-constant on any subcube
    with at most `n/2` TRUE-pins and fewer than `n/2` FALSE-pins — each
    sign bounded separately. -/
theorem maj_nonconst_of_pin_bounds {n : ℕ} (ρ : Fin n → Option Bool)
    (htp : 2 * (Finset.univ.filter fun j => ρ j = some true).card ≤ n)
    (hfp : 2 * (Finset.univ.filter fun j => ρ j = some false).card < n) :
    ∃ x y, memCube ρ x ∧ memCube ρ y ∧ maj x ≠ maj y := by
  refine ⟨fun j => (ρ j).getD false, fun j => (ρ j).getD true, ?_, ?_, ?_⟩
  · intro j bj hj
    simp [hj]
  · intro j bj hj
    simp [hj]
  · have he0 : (Finset.univ.filter fun j => (ρ j).getD false = true)
        = (Finset.univ.filter fun j => ρ j = some true) := by
      apply Finset.filter_congr
      intro j _
      cases hρj : ρ j with
      | none => simp
      | some b => cases b <;> simp
    have he1 : (Finset.univ.filter fun j => ¬ ((ρ j).getD true = true))
        = (Finset.univ.filter fun j => ρ j = some false) := by
      apply Finset.filter_congr
      intro j _
      cases hρj : ρ j with
      | none => simp
      | some b => cases b <;> simp
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => (ρ j).getD true = true)
    rw [Finset.card_univ, Fintype.card_fin, he1] at hsplit
    have h0 : maj (fun j => (ρ j).getD false) = false := by
      simp only [maj, decide_eq_false_iff_not]
      rw [he0]
      omega
    have h1 : maj (fun j => (ρ j).getD true) = true := by
      simp only [maj, decide_eq_true_eq]
      omega
    rw [h0, h1]
    simp

/-- Fin-3 bookkeeping: a third index besides two distinct ones, with
    completeness. -/
theorem fin3_third_index : ∀ a b : Fin 3, a ≠ b →
    ∃ c, c ≠ a ∧ c ≠ b ∧ ∀ j : Fin 3, j = a ∨ j = b ∨ j = c := by decide

/-- Fin-3 bookkeeping: the two indices besides a given one. -/
theorem fin3_other_two : ∀ i₀ : Fin 3,
    ∃ i₁ i₂ : Fin 3, i₁ ≠ i₀ ∧ i₂ ≠ i₀ ∧ i₁ ≠ i₂ ∧
      ∀ i : Fin 3, i = i₀ ∨ i = i₁ ∨ i = i₂ := by decide

/-! ## §2 R2 — case 1, closed -/

/-- **CASE 1 KILL.** If two of the three fixable witnesses are constant on
    a common half-cube, no aggregator computes maj₅: the third witness's
    forcing literal at that face leaves a ≤ 2-pin subcube where all three
    witnesses collide while majority is non-constant. -/
theorem maj5_shared_face_kill
    (w : Fin 3 → (Fin 5 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (a b : Fin 3) (hab : a ≠ b) (d : Fin 5) (β : Bool) (ca cb : Bool)
    (ha : ∀ x, x d = β → w a x = ca) (hb : ∀ x, x d = β → w b x = cb)
    (agg : (Fin 3 → Bool) → Bool) :
    (fun x => agg (fun i => w i x)) ≠ maj := by
  obtain ⟨e, hea, heb, hcompl⟩ := fin3_third_index a b hab
  intro heq
  obtain ⟨i, bb, hexcl, cc, hconst⟩ :=
    hfix e (fun j => if j = d then some β else none)
  have hbb : i = d → bb = β := by
    intro hid
    subst hid
    by_contra hne
    apply hexcl
    rw [if_pos rfl]
    have hβ : β = !bb := by cases β <;> cases bb <;> simp_all
    rw [hβ]
  set ρ₂ : Fin 5 → Option Bool :=
    fun j => if j = d then some β else if j = i then some bb else none
    with hρ₂
  have hcard : (pins ρ₂).card ≤ 2 := by
    have hsub : pins ρ₂ ⊆ insert d ({i} : Finset (Fin 5)) := by
      intro j hj
      simp only [pins, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_cases hjd : j = d
      · exact Finset.mem_insert.mpr (Or.inl hjd)
      · by_cases hji : j = i
        · exact Finset.mem_insert.mpr (Or.inr (by simp [hji]))
        · exact absurd (by simp [hρ₂, hjd, hji]) hj
    calc (pins ρ₂).card ≤ (insert d ({i} : Finset (Fin 5))).card :=
          Finset.card_le_card hsub
      _ ≤ ({i} : Finset (Fin 5)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  obtain ⟨x, y, hx, hy, hmaj⟩ :=
    maj_nonconstant_on_small_subcubes (by norm_num : 2 * 2 < 5) ρ₂ hcard
  have hxd : x d = β := hx d β (by simp [hρ₂])
  have hyd : y d = β := hy d β (by simp [hρ₂])
  have hxi : x i = bb := by
    by_cases hid : i = d
    · rw [hid, hxd, hbb hid]
    · exact hx i bb (by simp [hρ₂, hid])
  have hyi : y i = bb := by
    by_cases hid : i = d
    · rw [hid, hyd, hbb hid]
    · exact hy i bb (by simp [hρ₂, hid])
  have hfacemem : ∀ z : Fin 5 → Bool, z d = β →
      memCube (fun j => if j = d then some β else none) z := by
    intro z hz j bj hj
    have hj' : (if j = d then some β else none) = some bj := hj
    by_cases hjd : j = d
    · subst hjd
      rw [if_pos rfl] at hj'
      cases hj'
      exact hz
    · rw [if_neg hjd] at hj'
      cases hj'
  refine (witness_separation_fails maj w agg x y ?_ hmaj) heq
  intro j
  rcases hcompl j with rfl | rfl | rfl
  · rw [ha x hxd, ha y hyd]
  · rw [hb x hxd, hb y hyd]
  · rw [hconst x (hfacemem x hxd) hxi, hconst y (hfacemem y hyd) hyi]

/-- **Non-vacuity for case 1** — the shipped construction's own first two
    witnesses share the face `{x₀ = false}`: they extend to NO 3-witness
    family, whatever the third fixable witness and the aggregator. -/
theorem maj5_W1W2_not_completable
    (w₃ : (Fin 5 → Bool) → Bool) (h₃ : Fixable w₃)
    (agg : (Fin 3 → Bool) → Bool) :
    (fun x => agg (fun i => ![maj5W1, maj5W2, w₃] i x)) ≠ maj := by
  refine maj5_shared_face_kill ![maj5W1, maj5W2, w₃] ?_ 0 1 (by decide)
    0 false false false ?_ ?_ agg
  · intro i
    fin_cases i
    · exact maj5W1_fixable
    · exact maj5W2_fixable
    · exact h₃
  · intro x hx
    simp [maj5W1, hx]
  · intro x hx
    simp [maj5W2, hx]

/-! ## §3 R3 — mixed signs die; the reduction -/

/-- A non-unanimous Boolean triple contains both values. -/
theorem bool3_mixed : ∀ b₁ b₂ b₃ : Bool, ¬(b₁ = b₂ ∧ b₂ = b₃) →
    (b₁ = false ∨ b₂ = false ∨ b₃ = false) ∧
    (b₁ = true ∨ b₂ = true ∨ b₃ = true) := by decide

/-- **MIXED-SIGN KILL (case-3 sign reduction).** Three fixable witnesses
    constant on half-cubes in pairwise-distinct directions with
    non-unanimous signs cannot compute maj₅: on the triple-overlap
    subcube all witnesses collide, its true- and false-pins each number
    at most two, and majority is non-constant there. -/
theorem maj5_mixed_signs_kill
    (w : Fin 3 → (Fin 5 → Bool) → Bool)
    (d : Fin 3 → Fin 5) (β cv : Fin 3 → Bool)
    (hconst : ∀ i x, x (d i) = β i → w i x = cv i)
    (hd01 : d 0 ≠ d 1) (hd02 : d 0 ≠ d 2) (hd12 : d 1 ≠ d 2)
    (hmix : ¬(β 0 = β 1 ∧ β 1 = β 2))
    (agg : (Fin 3 → Bool) → Bool) :
    (fun x => agg (fun i => w i x)) ≠ maj := by
  intro heq
  set ρ₃ : Fin 5 → Option Bool :=
    fun j => if j = d 0 then some (β 0) else if j = d 1 then some (β 1)
      else if j = d 2 then some (β 2) else none
    with hρ₃
  have hval : ∀ z : Fin 5 → Bool, memCube ρ₃ z →
      ∀ i : Fin 3, z (d i) = β i := by
    intro z hz i
    fin_cases i
    · exact hz (d 0) (β 0) (by simp [hρ₃])
    · exact hz (d 1) (β 1) (by simp [hρ₃, Ne.symm hd01])
    · exact hz (d 2) (β 2) (by simp [hρ₃, Ne.symm hd02, Ne.symm hd12])
  have hpinval : ∀ j, ρ₃ j = none ∨
      ∃ i : Fin 3, j = d i ∧ ρ₃ j = some (β i) := by
    intro j
    by_cases h0 : j = d 0
    · exact Or.inr ⟨0, h0, by simp [hρ₃, h0]⟩
    · by_cases h1 : j = d 1
      · exact Or.inr ⟨1, h1, by simp [hρ₃, h1, Ne.symm hd01]⟩
      · by_cases h2 : j = d 2
        · exact Or.inr ⟨2, h2,
            by simp [hρ₃, h2, Ne.symm hd02, Ne.symm hd12]⟩
        · exact Or.inl (by simp [hρ₃, h0, h1, h2])
  have hcard_of : ∀ v : Bool, (∃ i₀ : Fin 3, β i₀ = !v) →
      (Finset.univ.filter fun j => ρ₃ j = some v).card ≤ 2 := by
    rintro v ⟨i₀, hi₀⟩
    obtain ⟨i₁, i₂, h₁₀, h₂₀, h₁₂, hcompl3⟩ := fin3_other_two i₀
    have hsub : (Finset.univ.filter fun j => ρ₃ j = some v)
        ⊆ ({d i₁, d i₂} : Finset (Fin 5)) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rcases hpinval j with hnone | ⟨i, rfl, hval'⟩
      · rw [hnone] at hj
        cases hj
      · have hbi : β i = v := by
          rw [hval'] at hj
          exact Option.some.inj hj
        have hii : i ≠ i₀ := by
          intro h
          rw [h, hi₀] at hbi
          cases v <;> simp_all
        rcases hcompl3 i with h | h | h
        · exact absurd h hii
        · subst h
          exact Finset.mem_insert_self _ _
        · subst h
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    calc (Finset.univ.filter fun j => ρ₃ j = some v).card
        ≤ ({d i₁, d i₂} : Finset (Fin 5)).card := Finset.card_le_card hsub
      _ ≤ ({d i₂} : Finset (Fin 5)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  obtain ⟨hfalse, htrue⟩ := bool3_mixed (β 0) (β 1) (β 2) hmix
  have htp : (Finset.univ.filter fun j => ρ₃ j = some true).card ≤ 2 := by
    apply hcard_of
    rcases hfalse with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  have hfp : (Finset.univ.filter fun j => ρ₃ j = some false).card ≤ 2 := by
    apply hcard_of
    rcases htrue with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
  obtain ⟨x, y, hx, hy, hmaj⟩ :=
    maj_nonconst_of_pin_bounds ρ₃ (by omega) (by omega)
  refine (witness_separation_fails maj w agg x y ?_ hmaj) heq
  intro i
  rw [hconst i x (hval x hx i), hconst i y (hval y hy i)]

/-- **THE REDUCTION.** Any three fixable witnesses computing maj₅ carry
    constancy half-cubes whose signed directions are pairwise distinct,
    and whose signs are unanimous whenever the directions are pairwise
    distinct: every surviving configuration is one of the two catalog
    shapes of the search (shared-direction-opposite-signs, or
    all-distinct-unanimous). -/
theorem maj5_reduction
    (w : Fin 3 → (Fin 5 → Bool) → Bool) (hfix : ∀ i, Fixable (w i))
    (agg : (Fin 3 → Bool) → Bool)
    (heq : (fun x => agg (fun i => w i x)) = maj) :
    ∃ (d : Fin 3 → Fin 5) (β cv : Fin 3 → Bool),
      (∀ i x, x (d i) = β i → w i x = cv i) ∧
      (∀ i j, i ≠ j → ¬(d i = d j ∧ β i = β j)) ∧
      ((d 0 ≠ d 1 ∧ d 0 ≠ d 2 ∧ d 1 ≠ d 2) → β 0 = β 1 ∧ β 1 = β 2) := by
  obtain ⟨d0, b0, c0, h0⟩ := fixable_const_halfcube (hfix 0)
  obtain ⟨d1, b1, c1, h1⟩ := fixable_const_halfcube (hfix 1)
  obtain ⟨d2, b2, c2, h2⟩ := fixable_const_halfcube (hfix 2)
  have hall : ∀ k : Fin 3, ∀ x : Fin 5 → Bool,
      x (![d0, d1, d2] k) = ![b0, b1, b2] k → w k x = ![c0, c1, c2] k := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
  refine ⟨![d0, d1, d2], ![b0, b1, b2], ![c0, c1, c2], hall, ?_, ?_⟩
  · rintro i j hij ⟨hd, hβ⟩
    exact (maj5_shared_face_kill w hfix i j hij (![d0, d1, d2] i)
      (![b0, b1, b2] i) (![c0, c1, c2] i) (![c0, c1, c2] j) (hall i)
      (fun x hx => hall j x (by rw [← hd, ← hβ]; exact hx)) agg) heq
  · rintro ⟨hd01, hd02, hd12⟩
    by_contra hmix
    exact (maj5_mixed_signs_kill w ![d0, d1, d2] ![b0, b1, b2] ![c0, c1, c2]
      hall hd01 hd02 hd12 hmix agg) heq

end
