/-
  AttentionLean.ThresholdCatalog

  L1 of the k(maj₅) ≥ 4 program: the CLASSIFICATION of ordered fixable
  pairs refining the 4-bit thresholds — the object the two remaining
  case kills (L2, L3) consume.

  STEP-0 SPEC (frozen before proving; matched VERBATIM to the search).
  "(P, Q) refines T" is exactly `refine` in
  scripts/maj5_witness_search.py: whenever two points carry the same
  joint label (P x, Q x), T agrees —
      ∀ x y, P x = P y → Q x = Q y → T x = T y.
  CLAIM (search-enumerated, |R2| = 24): the ordered fixable pairs
  refining `T2of4` (≥2-of-4) are EXACTLY
      { (catP A cP, catQ A cQ) : A a two-element subset of Fin 4,
        cP cQ ∈ Bool }
  where catP is the polarity-wrapped
      F_A(y) = (⋁_{i∈A} y i) ∨ (⋀_{j∉A} y j)
  and catQ the same on the complement subset — 6 × 2 × 2 = 24 pairs.
  Dually (|R3| = 24): the fixable pairs refining `T3of4` are the image
  of that catalog under dualization  dz f = fun y => !(f (¬y)).

  RUNGS (each final when it compiles):
    R-A  carriers + `catalog_sound` (all 24 pairs genuinely fixable and
         refining — non-vacuity) + `catalog_card` (in-kernel |R2| = 24).
    R-B  the cascade steps: heads positive (`refining_head_positive`),
         heads distinct, face equations — small kill decides
         (T2 ∘ pin unfixable / non-constant) + `refines_single_pm`.
    R-C  the three-region shape `shape4`, the canonical rest-pair, and
         the glue: any refining fixable pair IS a pair of shapes.
    R-D  per-direction finite classification (12 kernel decides over
         the 1024-point shape-parameter space, fixability-first
         nesting): shape pairs that are fixable and refining are
         catalog pairs.
    R-E  `T2_refining_pair_classified` — the L1 object for T₂.
    R-F  duality: `fixable_dualz`, `T3_refining_pair_classified`,
         `catalog3_sound`, `catalog3_card`.

  HONEST STATUS: this module classifies the threshold catalogs (L1).
  The case-2 and case-3 kills (L2, L3) and the assembly (L4) remain
  open, so k(maj₅) = 4 REMAINS SEARCH-PINNED after this module; the
  kernel-checked maj₅ statements are still the bracket 3 ≤ k ≤ 4 and
  `maj5_reduction`. Nothing existing is touched.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`; all finite checks kernel `decide`.
-/
import AttentionLean.FixableNormalForm

open Classical

noncomputable section

/-! ## §1 R-A: the catalog carriers -/

/-- `F_A` for `A = {a,b}`: OR of the two named coordinates, or AND of
    the other two. Symmetric in `a, b`. -/
def catBase (a b : Fin 4) (y : Fin 4 → Bool) : Bool :=
  y a || y b || decide (∀ j, j ≠ a → j ≠ b → y j = true)

/-- `F_Ā` for `A = {a,b}`: OR of the other two coordinates, or AND of
    the two named ones. -/
def catCoBase (a b : Fin 4) (y : Fin 4 → Bool) : Bool :=
  decide (∃ j, j ≠ a ∧ j ≠ b ∧ y j = true) || (y a && y b)

/-- Polarity-wrapped catalog function on the subset `{a,b}`. -/
def catP (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond c (catBase a b y) (!(catBase a b y))

/-- Polarity-wrapped catalog partner on the complement of `{a,b}`. -/
def catQ (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond c (catCoBase a b y) (!(catCoBase a b y))

set_option maxRecDepth 16384 in
/-- **Catalog soundness (non-vacuity).** Every one of the 24 catalog
    pairs is a genuine member of R2: both functions fixable, and the
    pair refines `T2of4`. -/
theorem catalog_sound : ∀ a b : Fin 4, a ≠ b → ∀ cP cQ : Bool,
    Fixable (catP a b cP) ∧ Fixable (catQ a b cQ) ∧
    (∀ x y, catP a b cP x = catP a b cP y →
      catQ a b cQ x = catQ a b cQ y → T2of4 x = T2of4 y) := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- **In-kernel |R2| = 24 oracle** (matches the search count): the 48
    admissible parameter tuples produce exactly 24 distinct function
    pairs. -/
theorem catalog_card :
    (((Finset.univ : Finset ((Fin 4 × Fin 4) × Bool × Bool)).filter
        fun t => t.1.1 ≠ t.1.2).image
      fun t => (fun y => catP t.1.1 t.1.2 t.2.1 y,
                fun y => catQ t.1.1 t.1.2 t.2.2 y)).card = 24 := by
  decide +kernel

/-! ## §2 R-B: cascade steps -/

/-- Fixability transports along pointwise equality. -/
theorem fixable_congr {n : ℕ} {f g : (Fin n → Bool) → Bool}
    (h : ∀ y, f y = g y) (hf : Fixable f) : Fixable g := by
  have hfg : f = g := funext h
  rw [← hfg]
  exact hf

/-- Pinning any coordinate of `T2of4` to `false` leaves an unfixable
    function (it is `maj₃` on the rest), and so does its complement —
    the kill behind "top literals are positive". -/
theorem T2_update_false_not_pm_fixable : ∀ i : Fin 4,
    ¬ Fixable (fun y => T2of4 (Function.update y i false)) ∧
    ¬ Fixable (fun y => !(T2of4 (Function.update y i false))) := by
  decide +kernel

/-- `T2of4` is non-constant on every half-cube. -/
theorem T2_update_nonconst : ∀ (i : Fin 4) (b : Bool),
    ∃ u v : Fin 4 → Bool,
      T2of4 (Function.update u i b) ≠ T2of4 (Function.update v i b) := by
  decide +kernel

/-- Polarity-pinning point: the weight-2 point `{i, j}` satisfies the
    threshold. -/
theorem T2_point_pin : ∀ i j : Fin 4, i ≠ j →
    T2of4 (Function.update (fun m => decide (m = i)) j true) = true := by
  decide

/-- **S1 — heads are positive.** In a fixable pair refining `T2of4`,
    the first component is constant on some POSITIVE half-cube: a
    negative constancy face would force the partner's restriction to be
    `±maj₃`, which is unfixable. -/
theorem refining_head_positive
    {P Q : (Fin 4 → Bool) → Bool} (hQ : Fixable Q)
    (hface : ∃ i b c, ∀ y : Fin 4 → Bool, y i = b → P y = c)
    (href : ∀ x y, P x = P y → Q x = Q y → T2of4 x = T2of4 y) :
    ∃ i cP, ∀ y : Fin 4 → Bool, y i = true → P y = cP := by
  obtain ⟨i, b, c, hc⟩ := hface
  cases b with
  | true => exact ⟨i, c, hc⟩
  | false =>
      exfalso
      have hQ' : Fixable (fun u => Q (Function.update u i false)) :=
        fixable_update_restrict hQ i false
      have hrefQ' : ∀ u v : Fin 4 → Bool,
          Q (Function.update u i false) = Q (Function.update v i false) →
          T2of4 (Function.update u i false)
            = T2of4 (Function.update v i false) := by
        intro u v hq
        exact href _ _
          (by rw [hc _ (Function.update_self i false u),
                  hc _ (Function.update_self i false v)]) hq
      obtain ⟨u₀, v₀, hne⟩ := T2_update_nonconst i false
      rcases refines_single_pm
          (fun u => T2of4 (Function.update u i false))
          (fun u => Q (Function.update u i false)) hrefQ' u₀ v₀ hne with
        hpos | hneg
      · exact (T2_update_false_not_pm_fixable i).1 (fixable_congr hpos hQ')
      · exact (T2_update_false_not_pm_fixable i).2 (fixable_congr hneg hQ')

/-- **S2 — heads are distinct.** The two positive constancy directions
    of a refining pair differ: a shared face would make `T2of4`
    constant across a single fiber. -/
theorem refining_heads_distinct
    {P Q : (Fin 4 → Bool) → Bool}
    (href : ∀ x y, P x = P y → Q x = Q y → T2of4 x = T2of4 y)
    {i j : Fin 4} {cP cQ : Bool}
    (hPf : ∀ y : Fin 4 → Bool, y i = true → P y = cP)
    (hQf : ∀ y : Fin 4 → Bool, y j = true → Q y = cQ) :
    i ≠ j := by
  rintro rfl
  obtain ⟨u, v, hne⟩ := T2_update_nonconst i true
  exact hne (href _ _
    (by rw [hPf _ (Function.update_self i true u),
            hPf _ (Function.update_self i true v)])
    (by rw [hQf _ (Function.update_self i true u),
            hQf _ (Function.update_self i true v)]))

/-- **S3 — the face equation.** On the partner's constancy face, the
    first component equals `T2of4` up to the complement of its own
    polarity. -/
theorem refining_face_eq
    {P Q : (Fin 4 → Bool) → Bool}
    (href : ∀ x y, P x = P y → Q x = Q y → T2of4 x = T2of4 y)
    {i j : Fin 4} {cP cQ : Bool} (hij : i ≠ j)
    (hPf : ∀ y : Fin 4 → Bool, y i = true → P y = cP)
    (hQf : ∀ y : Fin 4 → Bool, y j = true → Q y = cQ) :
    ∀ u, P (Function.update u j true)
      = xor (!cP) (T2of4 (Function.update u j true)) := by
  have hrefP' : ∀ u v : Fin 4 → Bool,
      P (Function.update u j true) = P (Function.update v j true) →
      T2of4 (Function.update u j true)
        = T2of4 (Function.update v j true) := by
    intro u v hp
    exact href _ _ hp
      (by rw [hQf _ (Function.update_self j true u),
              hQf _ (Function.update_self j true v)])
  obtain ⟨u₀, v₀, hne⟩ := T2_update_nonconst j true
  have hpti : (Function.update (fun m => decide (m = i)) j true) i = true := by
    rw [Function.update_of_ne hij]
    simp
  have hP1 : P (Function.update (fun m => decide (m = i)) j true) = cP :=
    hPf _ hpti
  rcases refines_single_pm
      (fun u => T2of4 (Function.update u j true))
      (fun u => P (Function.update u j true)) hrefP' u₀ v₀ hne with
    hpos | hneg
  · have hcp : cP = true := by
      have := hpos (fun m => decide (m = i))
      rw [hP1, T2_point_pin i j hij] at this
      exact this
    intro u
    rw [hpos u, hcp]
    cases T2of4 (Function.update u j true) <;> rfl
  · have hcp : cP = false := by
      have := hneg (fun m => decide (m = i))
      rw [hP1, T2_point_pin i j hij] at this
      exact this
    intro u
    rw [hneg u, hcp]
    cases T2of4 (Function.update u j true) <;> rfl

/-! ## §3 R-C: the three-region shape and the glue -/

/-- The three-region shape a refining pair member must take: constant on
    its own face, `±OR` of the free coordinates on the partner's face,
    arbitrary residual on the remaining 2-face. -/
def shape4 (i j k l : Fin 4) (c : Bool) (p : Bool → Bool → Bool)
    (y : Fin 4 → Bool) : Bool :=
  if y i then c else if y j then xor (!c) (y k || y l) else p (y k) (y l)

/-- The two coordinates outside `{i, j}`, in increasing order. -/
def restPair (i j : Fin 4) : Fin 4 × Fin 4 :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (2, 3)
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then (1, 3)
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then (1, 2)
  else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then (0, 3)
  else if (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) then (0, 2)
  else (0, 1)

theorem restPair_spec : ∀ i j : Fin 4, i ≠ j →
    (restPair i j).1 ≠ i ∧ (restPair i j).1 ≠ j ∧
    (restPair i j).2 ≠ i ∧ (restPair i j).2 ≠ j ∧
    (restPair i j).1 ≠ (restPair i j).2 ∧
    (∀ m : Fin 4,
      m = i ∨ m = j ∨ m = (restPair i j).1 ∨ m = (restPair i j).2) := by
  decide

theorem restPair_symm : ∀ i j : Fin 4, restPair i j = restPair j i := by
  decide

/-- Point-builder: coordinates `i, j, k` get `a, b, c`; everything else
    (the fourth coordinate, when the four are distinct) gets `d`. -/
def pt4 (i j k _l : Fin 4) (a b c d : Bool) : Fin 4 → Bool :=
  fun m => if m = i then a else if m = j then b else if m = k then c else d

/-- On the partner's face with the own coordinate off, the threshold is
    the OR of the two free coordinates. -/
theorem T2_face_or : ∀ i j : Fin 4, i ≠ j → ∀ y : Fin 4 → Bool,
    y i = false →
    T2of4 (Function.update y j true)
      = (y (restPair i j).1 || y (restPair i j).2) := by
  decide +kernel

/-- **The glue.** A function constant on the positive face `{y i = 1}`
    and matching the face equation on `{y j = 1}` IS a `shape4`, with
    residual read off its own values on the remaining 2-face. -/
theorem glue_shape
    {P : (Fin 4 → Bool) → Bool} {i j : Fin 4} {cP : Bool} (hij : i ≠ j)
    (hPf : ∀ y : Fin 4 → Bool, y i = true → P y = cP)
    (hface : ∀ u, P (Function.update u j true)
      = xor (!cP) (T2of4 (Function.update u j true))) :
    ∀ y, P y = shape4 i j (restPair i j).1 (restPair i j).2 cP
      (fun u v =>
        P (pt4 i j (restPair i j).1 (restPair i j).2 false false u v)) y := by
  obtain ⟨hki, hkj, hli, hlj, hkl, hcompl⟩ := restPair_spec i j hij
  intro y
  unfold shape4
  by_cases hyi : y i = true
  · rw [if_pos hyi, hPf y hyi]
  · have hyi' : y i = false := by cases h : y i <;> simp_all
    rw [if_neg hyi]
    by_cases hyj : y j = true
    · rw [if_pos hyj]
      have hupd : Function.update y j true = y := by
        funext m
        by_cases hm : m = j
        · subst hm
          rw [Function.update_self]
          exact hyj.symm
        · rw [Function.update_of_ne hm]
      have hf := hface y
      rw [T2_face_or i j hij y hyi'] at hf
      rw [hupd] at hf
      exact hf
    · rw [if_neg hyj]
      have hyj' : y j = false := by cases h : y j <;> simp_all
      have hy : P y
          = P (pt4 i j (restPair i j).1 (restPair i j).2 false false
              (y (restPair i j).1) (y (restPair i j).2)) := by
        congr 1
        funext m
        unfold pt4
        rcases hcompl m with rfl | rfl | rfl | rfl
        · rw [if_pos rfl]
          exact hyi'
        · rw [if_neg (Ne.symm hij), if_pos rfl]
          exact hyj'
        · rw [if_neg hki, if_neg hkj, if_pos rfl]
        · by_cases hlk : (restPair i j).2 = (restPair i j).1
          · rw [if_neg hli, if_neg hlj, if_pos hlk, hlk]
          · rw [if_neg hli, if_neg hlj, if_neg hlk]
      exact hy

/-! ## §4 R-D: the per-direction finite classification

The full quantified statement defeats `Decidable` instance synthesis, so
it is layered through two `def`s, each with its own registered instance;
kernel evaluation unfolds them and keeps the fixability-first
short-circuit order (fixability refutes cheaply, killing most parameter
branches before the partner space is enumerated). -/

/-- Innermost layer: the refining hypothesis forces catalog membership. -/
def layerBCore (i j k l : Fin 4) (cP : Bool) (p : Bool → Bool → Bool)
    (cQ : Bool) (q : Bool → Bool → Bool) : Prop :=
  (∀ x y, shape4 i j k l cP p x = shape4 i j k l cP p y →
    shape4 j i k l cQ q x = shape4 j i k l cQ q y → T2of4 x = T2of4 y) →
  ∃ a b : Fin 4, a ≠ b ∧ ∃ cP' cQ' : Bool,
    (∀ y, shape4 i j k l cP p y = catP a b cP' y) ∧
    (∀ y, shape4 j i k l cQ q y = catQ a b cQ' y)

instance (i j k l : Fin 4) (cP : Bool) (p : Bool → Bool → Bool)
    (cQ : Bool) (q : Bool → Bool → Bool) :
    Decidable (layerBCore i j k l cP p cQ q) := by
  unfold layerBCore
  infer_instance

/-- Middle layer: quantify the partner's parameters, fixability first. -/
def layerBInner (i j k l : Fin 4) (cP : Bool) (p : Bool → Bool → Bool) :
    Prop :=
  ∀ (cQ : Bool) (q : Bool → Bool → Bool),
    Fixable (shape4 j i k l cQ q) → layerBCore i j k l cP p cQ q

instance (i j k l : Fin 4) (cP : Bool) (p : Bool → Bool → Bool) :
    Decidable (layerBInner i j k l cP p) := by
  unfold layerBInner
  infer_instance

set_option maxRecDepth 16384 in
theorem layerB_01 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 0 1 2 3 cP p) → layerBInner 0 1 2 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_02 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 0 2 1 3 cP p) → layerBInner 0 2 1 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_03 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 0 3 1 2 cP p) → layerBInner 0 3 1 2 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_10 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 1 0 2 3 cP p) → layerBInner 1 0 2 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_12 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 1 2 0 3 cP p) → layerBInner 1 2 0 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_13 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 1 3 0 2 cP p) → layerBInner 1 3 0 2 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_20 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 2 0 1 3 cP p) → layerBInner 2 0 1 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_21 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 2 1 0 3 cP p) → layerBInner 2 1 0 3 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_23 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 2 3 0 1 cP p) → layerBInner 2 3 0 1 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_30 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 3 0 1 2 cP p) → layerBInner 3 0 1 2 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_31 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 3 1 0 2 cP p) → layerBInner 3 1 0 2 cP p := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem layerB_32 : ∀ (cP : Bool) (p : Bool → Bool → Bool),
    Fixable (shape4 3 2 0 1 cP p) → layerBInner 3 2 0 1 cP p := by
  decide +kernel

/-- Dispatch: the twelve concrete directions, keyed by `restPair`. -/
theorem layerB_dispatch : ∀ i j : Fin 4, i ≠ j →
    ∀ (cP : Bool) (p : Bool → Bool → Bool),
      Fixable (shape4 i j (restPair i j).1 (restPair i j).2 cP p) →
      layerBInner i j (restPair i j).1 (restPair i j).2 cP p := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact layerB_01
      | exact layerB_02
      | exact layerB_03
      | exact layerB_10
      | exact layerB_12
      | exact layerB_13
      | exact layerB_20
      | exact layerB_21
      | exact layerB_23
      | exact layerB_30
      | exact layerB_31
      | exact layerB_32

/-! ## §5 R-E: the classification -/

/-- **L1 FOR T₂ — THE CLASSIFICATION.** Every ordered fixable pair
    refining `T2of4` is one of the 24 catalog pairs: a polarity-wrapped
    two-subset function paired with its complement-subset partner.
    Together with `catalog_sound`/`catalog_card`, this is R2 = the
    24-element catalog, in the kernel. -/
theorem T2_refining_pair_classified
    {P Q : (Fin 4 → Bool) → Bool} (hP : Fixable P) (hQ : Fixable Q)
    (href : ∀ x y, P x = P y → Q x = Q y → T2of4 x = T2of4 y) :
    ∃ a b : Fin 4, a ≠ b ∧ ∃ cP cQ : Bool,
      (∀ y, P y = catP a b cP y) ∧ (∀ y, Q y = catQ a b cQ y) := by
  obtain ⟨i, cP, hPf⟩ :=
    refining_head_positive hQ (fixable_const_halfcube hP) href
  have href' : ∀ x y, Q x = Q y → P x = P y → T2of4 x = T2of4 y :=
    fun x y h1 h2 => href x y h2 h1
  obtain ⟨j, cQ, hQf⟩ :=
    refining_head_positive hP (fixable_const_halfcube hQ) href'
  have hij : i ≠ j := refining_heads_distinct href hPf hQf
  have hPface := refining_face_eq href hij hPf hQf
  have hQface := refining_face_eq href' hij.symm hQf hPf
  have hPglue := glue_shape hij hPf hPface
  have hQglue := glue_shape hij.symm hQf hQface
  rw [← restPair_symm i j] at hQglue
  have hfixP := fixable_congr hPglue hP
  have hfixQ := fixable_congr hQglue hQ
  have hrefS : ∀ x y,
      shape4 i j (restPair i j).1 (restPair i j).2 cP
        (fun u v => P (pt4 i j (restPair i j).1 (restPair i j).2
          false false u v)) x
      = shape4 i j (restPair i j).1 (restPair i j).2 cP
        (fun u v => P (pt4 i j (restPair i j).1 (restPair i j).2
          false false u v)) y →
      shape4 j i (restPair i j).1 (restPair i j).2 cQ
        (fun u v => Q (pt4 j i (restPair i j).1 (restPair i j).2
          false false u v)) x
      = shape4 j i (restPair i j).1 (restPair i j).2 cQ
        (fun u v => Q (pt4 j i (restPair i j).1 (restPair i j).2
          false false u v)) y →
      T2of4 x = T2of4 y := by
    intro x y h1 h2
    rw [← hPglue x, ← hPglue y] at h1
    rw [← hQglue x, ← hQglue y] at h2
    exact href x y h1 h2
  obtain ⟨a, b, hab, cP', cQ', hcatP, hcatQ⟩ :=
    layerB_dispatch i j hij cP _ hfixP cQ _ hfixQ hrefS
  refine ⟨a, b, hab, cP', cQ', fun y => ?_, fun y => ?_⟩
  · rw [hPglue y, hcatP y]
  · rw [hQglue y, hcatQ y]

/-! ## §6 R-F: duality — the T₃ catalog -/

/-- Boolean dualization: negate inputs and output. -/
def dualz {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun y => !(f (fun m => !(y m)))

/-- Fixability is closed under dualization: the forcing literal negates
    its value, the forced constant negates. -/
theorem fixable_dualz {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : Fixable f) : Fixable (dualz f) := by
  intro ρ
  obtain ⟨i, b, hexcl, c, hconst⟩ := hf (fun m => (ρ m).map (!·))
  refine ⟨i, !b, ?_, !c, ?_⟩
  · intro hτ
    apply hexcl
    rw [hτ]
    simp
  · intro x hx hxi
    have hmem : memCube (fun m => (ρ m).map (!·)) (fun m => !(x m)) := by
      intro m bm hm
      have hm' : Option.map (!·) (ρ m) = some bm := hm
      show (!(x m)) = bm
      cases hρm : ρ m with
      | none =>
          rw [hρm] at hm'
          cases hm'
      | some u =>
          rw [hρm] at hm'
          have hu : (!u) = bm := Option.some.inj hm'
          rw [hx m u hρm]
          exact hu
    have hxi' : (fun m => !(x m)) i = b := by
      show (!(x i)) = b
      rw [hxi]
      simp
    show (!(f fun m => !(x m))) = !c
    rw [hconst _ hmem hxi']

theorem dualz_dualz {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∀ y, dualz (dualz f) y = f y := by
  intro y
  show (!(!(f fun m => !(!(y m))))) = f y
  rw [Bool.not_not]
  congr 1
  funext m
  exact Bool.not_not _

/-- The two thresholds are each other's duals. -/
theorem T3_eq_dualz_T2 : ∀ y, T3of4 y = dualz T2of4 y := by
  decide

theorem T2_eq_not_T3_neg :
    ∀ y : Fin 4 → Bool, T2of4 y = !(T3of4 fun m => !(y m)) := by
  decide

/-- Dual catalog carriers: the `T3of4` catalog functions (constant on
    NEGATIVE faces; AND-forms). -/
def catBase3 (a b : Fin 4) (y : Fin 4 → Bool) : Bool :=
  y a && y b && decide (∃ j, j ≠ a ∧ j ≠ b ∧ y j = true)

def catCoBase3 (a b : Fin 4) (y : Fin 4 → Bool) : Bool :=
  decide (∀ j, j ≠ a → j ≠ b → y j = true) && (y a || y b)

def catP3 (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond c (catBase3 a b y) (!(catBase3 a b y))

def catQ3 (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond c (catCoBase3 a b y) (!(catCoBase3 a b y))

/-- The dual carriers ARE the dualized primal carriers. -/
theorem catP3_dual : ∀ (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool),
    catP3 a b c y = !(catP a b c fun m => !(y m)) := by
  decide

theorem catQ3_dual : ∀ (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool),
    catQ3 a b c y = !(catQ a b c fun m => !(y m)) := by
  decide

set_option maxRecDepth 16384 in
/-- **Catalog soundness for T₃** — all 24 dual pairs are fixable and
    refine `T3of4`. -/
theorem catalog3_sound : ∀ a b : Fin 4, a ≠ b → ∀ cP cQ : Bool,
    Fixable (catP3 a b cP) ∧ Fixable (catQ3 a b cQ) ∧
    (∀ x y, catP3 a b cP x = catP3 a b cP y →
      catQ3 a b cQ x = catQ3 a b cQ y → T3of4 x = T3of4 y) := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- **In-kernel |R3| = 24 oracle.** -/
theorem catalog3_card :
    (((Finset.univ : Finset ((Fin 4 × Fin 4) × Bool × Bool)).filter
        fun t => t.1.1 ≠ t.1.2).image
      fun t => (fun y => catP3 t.1.1 t.1.2 t.2.1 y,
                fun y => catQ3 t.1.1 t.1.2 t.2.2 y)).card = 24 := by
  decide +kernel

/-- **L1 FOR T₃ — THE DUAL CLASSIFICATION.** Every ordered fixable pair
    refining `T3of4` is one of the 24 dual catalog pairs. Proved by
    transporting through dualization and applying the T₂ result. -/
theorem T3_refining_pair_classified
    {P Q : (Fin 4 → Bool) → Bool} (hP : Fixable P) (hQ : Fixable Q)
    (href : ∀ x y, P x = P y → Q x = Q y → T3of4 x = T3of4 y) :
    ∃ a b : Fin 4, a ≠ b ∧ ∃ cP cQ : Bool,
      (∀ y, P y = catP3 a b cP y) ∧ (∀ y, Q y = catQ3 a b cQ y) := by
  have href' : ∀ x y, dualz P x = dualz P y → dualz Q x = dualz Q y →
      T2of4 x = T2of4 y := by
    intro x y h1 h2
    have h1' : P (fun m => !(x m)) = P (fun m => !(y m)) :=
      Bool.not_inj h1
    have h2' : Q (fun m => !(x m)) = Q (fun m => !(y m)) :=
      Bool.not_inj h2
    rw [T2_eq_not_T3_neg x, T2_eq_not_T3_neg y, href _ _ h1' h2']
  obtain ⟨a, b, hab, cP', cQ', hcP, hcQ⟩ :=
    T2_refining_pair_classified (fixable_dualz hP) (fixable_dualz hQ) href'
  have hyy : ∀ y : Fin 4 → Bool, (fun m => !(!(y m))) = y :=
    fun y => funext fun m => Bool.not_not _
  refine ⟨a, b, hab, cP', cQ', fun y => ?_, fun y => ?_⟩
  · have h := hcP (fun m => !(y m))
    show P y = _
    have h' : (!(P fun m => !(!(y m)))) = catP a b cP' (fun m => !(y m)) := h
    rw [hyy y] at h'
    rw [catP3_dual, ← h', Bool.not_not]
  · have h := hcQ (fun m => !(y m))
    show Q y = _
    have h' : (!(Q fun m => !(!(y m)))) = catQ a b cQ' (fun m => !(y m)) := h
    rw [hyy y] at h'
    rw [catQ3_dual, ← h', Bool.not_not]

end
