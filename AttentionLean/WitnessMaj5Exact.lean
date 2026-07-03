/-
  AttentionLean.WitnessMaj5Exact

  THE LOAD-BEARING THEOREM: k(maj₅) ≥ 4, kernel-clean —
  `maj5_no_three_fixable_witnesses`, and with the shipped upper bound
  `maj5_witness_number_exact`. This retires the exhaustive-search
  dependency: the first gap (witness complexity 4 > certificate
  complexity 3) becomes a kernel theorem.

  STATEMENT (frozen):
    ∀ w : Fin 3 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 3 → Bool) → Bool, (fun x => agg (fun i => w i x)) ≠ maj.

  ROUTE. `maj5_reduction` (main) leaves exactly two configurations:
  CASE 2 (two witnesses share a direction e with opposite signs) and
  CASE 3 (three distinct directions, unanimous sign σ). Both faces of a
  shared/each direction force catalog pairs via the L1 classification
  (`T2_refining_pair_classified` / `T3_refining_pair_classified`), so
  the third/each witness is a PIECEWISE-CATALOG function of finitely
  many parameters. The kills (oracle-designed and validated against
  scripts/maj5_witness_search.py, then re-verified in kernel here):

  * CASE 2: the doubly-classified witness (`case2C`: catQ-form on
    {x e = 1}, catQ3-form on {x e = 0}) is UNFIXABLE for ALL 2,880
    parameter choices — no refinement analysis needed. Five per-`e`
    kernel decides, each exhibiting a failing subcube from an 8-element
    hitting list of 2-pin subcubes.

  * CASE 3 (after a coordinate permutation sending the directions to
    0,1,2): each witness is piecewise-catalog on two faces + constant
    on its own face + free on the 4-point region {x₀=x₁=x₂=¬σ}.
    Per witness, a kernel decide (`case3_killA/B/C`) shows: under the
    derivable slice-constancy and cross-face-consistency facts, either
    the witness is unfixable (9-element hitting list) or its parameters
    lie in an EXPLICIT 16-element bad list (per σ). The final decide
    (`case3_compat`): no three bad-list members agree on the shared
    face subsets — so all three witnesses fixable is impossible.
    (Oracle counts: 40 filtered parts × 16 regions per witness per σ;
    16 fixable exceptions each; matched bad triples: 0.)

  All checks kernel `decide` (+kernel); no native_decide; no sorry.
  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. Purely additive: bracket, reduction, catalogs untouched.
-/
import AttentionLean.ThresholdCatalog

open Classical

noncomputable section

/-! ## §1 Face plumbing: computable embed / delete / insert -/

/-- Index of `j ≠ e` inside the 4 coordinates that remain after
    deleting `e` (garbage at `j = e`, never used there). -/
def unembed5 (e j : Fin 5) : Fin 4 :=
  if _h : j.val < e.val then ⟨j.val, by have := e.isLt; omega⟩
  else ⟨j.val - 1, by have := j.isLt; omega⟩

/-- The `i`-th coordinate of the 5-cube after skipping `e`. -/
def embed5 (e : Fin 5) (i : Fin 4) : Fin 5 :=
  if _h : i.val < e.val then ⟨i.val, by have := i.isLt; omega⟩
  else ⟨i.val + 1, by have := i.isLt; omega⟩

/-- Insert value `a` at coordinate `e` (generic in the value type). -/
def insertAt5 {α : Type*} (e : Fin 5) (a : α) (v : Fin 4 → α) :
    Fin 5 → α :=
  fun j => if j = e then a else v (unembed5 e j)

/-- Delete coordinate `e`. -/
def delAt (e : Fin 5) (x : Fin 5 → Bool) : Fin 4 → Bool :=
  fun i => x (embed5 e i)

theorem embed5_ne : ∀ (e : Fin 5) (i : Fin 4), embed5 e i ≠ e := by decide

theorem unembed5_embed5 : ∀ (e : Fin 5) (i : Fin 4),
    unembed5 e (embed5 e i) = i := by decide

theorem embed5_unembed5 : ∀ (e j : Fin 5), j ≠ e →
    embed5 e (unembed5 e j) = j := by decide

theorem insertAt5_self {α : Type*} (e : Fin 5) (a : α) (v : Fin 4 → α) :
    insertAt5 e a v e = a := by
  show (if e = e then a else v (unembed5 e e)) = a
  rw [if_pos rfl]

theorem insertAt5_embed5 {α : Type*} (e : Fin 5) (a : α) (v : Fin 4 → α)
    (i : Fin 4) : insertAt5 e a v (embed5 e i) = v i := by
  rw [insertAt5, if_neg (embed5_ne e i), unembed5_embed5]

theorem delAt_insertAt5 (e : Fin 5) (β : Bool) (y : Fin 4 → Bool) :
    delAt e (insertAt5 e β y) = y := by
  funext i
  exact insertAt5_embed5 e β y i

theorem insertAt5_delAt (e : Fin 5) (β : Bool) (x : Fin 5 → Bool)
    (hx : x e = β) : insertAt5 e β (delAt e x) = x := by
  funext j
  by_cases hj : j = e
  · subst hj
    rw [insertAt5_self, hx]
  · rw [insertAt5, if_neg hj, delAt, embed5_unembed5 e j hj]

/-- Restriction of a fixable 5-cube witness to a face is fixable on the
    4-cube: the forcing literal transfers or the restriction is
    constant. -/
theorem fixable_restrictAt {W : (Fin 5 → Bool) → Bool} (hW : Fixable W)
    (e : Fin 5) (β : Bool) :
    Fixable (fun y => W (insertAt5 e β y)) := by
  intro ρ
  obtain ⟨i5, b, hexcl, c, hconst⟩ := hW (insertAt5 e (some β) ρ)
  have hmem : ∀ y : Fin 4 → Bool, memCube ρ y →
      memCube (insertAt5 e (some β) ρ) (insertAt5 e β y) := by
    intro y hy m bm hm
    by_cases hme : m = e
    · subst hme
      rw [insertAt5_self] at hm
      cases hm
      rw [insertAt5_self]
    · rw [insertAt5, if_neg hme] at hm ⊢
      exact hy _ bm hm
  by_cases hie : i5 = e
  · subst hie
    have hbβ : b = β := by
      by_contra hne
      apply hexcl
      rw [insertAt5_self]
      cases b <;> cases β <;> simp_all
    obtain ⟨b₁, hleg⟩ := exists_legal_literal ρ
    refine ⟨0, b₁, hleg, c, fun y hy _ => ?_⟩
    exact hconst _ (hmem y hy) (by rw [insertAt5_self, hbβ])
  · refine ⟨unembed5 e i5, b, ?_, c, fun y hy hyi => ?_⟩
    · intro hτ
      apply hexcl
      rw [insertAt5, if_neg hie]
      exact hτ
    · exact hconst _ (hmem y hy)
        (by rw [insertAt5, if_neg hie]; exact hyi)

/-! ## §2 Face transport: refinement and classification on faces -/

/-- σ-uniform catalog carriers: T₂-catalog for `σ = true`, T₃-catalog
    for `σ = false`. -/
def catPσ (σ : Bool) (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond σ (catP a b c y) (catP3 a b c y)

def catQσ (σ : Bool) (a b : Fin 4) (c : Bool) (y : Fin 4 → Bool) : Bool :=
  cond σ (catQ a b c y) (catQ3 a b c y)

/-- Majority on a face is the matching 4-bit threshold. -/
theorem maj_insert_face : ∀ (e : Fin 5) (σ : Bool) (y : Fin 4 → Bool),
    maj (insertAt5 e σ y) = cond σ (T2of4 y) (T3of4 y) := by
  decide

/-- The triple-refinement of any computing family. -/
theorem triple_refines {w : Fin 3 → (Fin 5 → Bool) → Bool}
    {agg : (Fin 3 → Bool) → Bool}
    (heq : (fun x => agg (fun i => w i x)) = maj) :
    ∀ x x', (∀ i, w i x = w i x') → maj x = maj x' := by
  intro x x' h
  have hx := congrFun heq x
  have hx' := congrFun heq x'
  rw [← hx, ← hx']
  show agg (fun i => w i x) = agg (fun i => w i x')
  congr 1
  funext i
  exact h i

/-- **Face classification.** On the face `{x e = σ}` where `A` is
    constant, the pair of restrictions of `B, C` is a fixable pair
    refining the matching threshold, hence a catalog pair; transported
    back to face equations on the 5-cube. -/
theorem face_classified {A B C : (Fin 5 → Bool) → Bool}
    (href : ∀ x x', A x = A x' → B x = B x' → C x = C x' →
      maj x = maj x')
    (hB : Fixable B) (hC : Fixable C) (e : Fin 5) (σ : Bool) {cv : Bool}
    (hA : ∀ x, x e = σ → A x = cv) :
    ∃ a b, a ≠ b ∧ ∃ cP cQ,
      (∀ x, x e = σ → B x = catPσ σ a b cP (delAt e x)) ∧
      (∀ x, x e = σ → C x = catQσ σ a b cQ (delAt e x)) := by
  have hfixB' : Fixable (fun y => B (insertAt5 e σ y)) :=
    fixable_restrictAt hB e σ
  have hfixC' : Fixable (fun y => C (insertAt5 e σ y)) :=
    fixable_restrictAt hC e σ
  have hpair : ∀ y y' : Fin 4 → Bool,
      B (insertAt5 e σ y) = B (insertAt5 e σ y') →
      C (insertAt5 e σ y) = C (insertAt5 e σ y') →
      maj (insertAt5 e σ y) = maj (insertAt5 e σ y') := by
    intro y y' hb hc
    exact href _ _
      (by rw [hA _ (insertAt5_self e σ y), hA _ (insertAt5_self e σ y')])
      hb hc
  cases σ with
  | true =>
      have hpair2 : ∀ y y' : Fin 4 → Bool,
          B (insertAt5 e true y) = B (insertAt5 e true y') →
          C (insertAt5 e true y) = C (insertAt5 e true y') →
          T2of4 y = T2of4 y' := by
        intro y y' hb hc
        have h := hpair y y' hb hc
        rw [maj_insert_face, maj_insert_face] at h
        exact h
      obtain ⟨a, b, hab, cP, cQ, hcatB, hcatC⟩ :=
        T2_refining_pair_classified hfixB' hfixC' hpair2
      refine ⟨a, b, hab, cP, cQ, fun x hx => ?_, fun x hx => ?_⟩
      · have h := hcatB (delAt e x)
        rw [insertAt5_delAt e true x hx] at h
        exact h
      · have h := hcatC (delAt e x)
        rw [insertAt5_delAt e true x hx] at h
        exact h
  | false =>
      have hpair2 : ∀ y y' : Fin 4 → Bool,
          B (insertAt5 e false y) = B (insertAt5 e false y') →
          C (insertAt5 e false y) = C (insertAt5 e false y') →
          T3of4 y = T3of4 y' := by
        intro y y' hb hc
        have h := hpair y y' hb hc
        rw [maj_insert_face, maj_insert_face] at h
        exact h
      obtain ⟨a, b, hab, cP, cQ, hcatB, hcatC⟩ :=
        T3_refining_pair_classified hfixB' hfixC' hpair2
      refine ⟨a, b, hab, cP, cQ, fun x hx => ?_, fun x hx => ?_⟩
      · have h := hcatB (delAt e x)
        rw [insertAt5_delAt e false x hx] at h
        exact h
      · have h := hcatC (delAt e x)
        rw [insertAt5_delAt e false x hx] at h
        exact h

/-! ## §3 Case 2: shared direction, opposite signs -/

/-- The doubly-classified third witness of case 2. -/
def case2C (e : Fin 5) (a b : Fin 4) (cQ : Bool) (a2 b2 : Fin 4)
    (cQ2 : Bool) (x : Fin 5 → Bool) : Bool :=
  if x e then catQ a b cQ (delAt e x) else catQ3 a2 b2 cQ2 (delAt e x)

/-- A 2-pin subcube. -/
def pin2 (i j : Fin 5) (bi bj : Bool) : Fin 5 → Option Bool :=
  fun m => if m = i then some bi else if m = j then some bj else none

/-- All 32 points of the 5-cube, as an explicit list — kernel evaluation
    over this list avoids the (prohibitively slow) `Fintype` enumeration
    of the function space inside `decide`. -/
def allPts5 : List (Fin 5 → Bool) :=
  [![false, false, false, false, false],
   ![true, false, false, false, false],
   ![false, true, false, false, false],
   ![true, true, false, false, false],
   ![false, false, true, false, false],
   ![true, false, true, false, false],
   ![false, true, true, false, false],
   ![true, true, true, false, false],
   ![false, false, false, true, false],
   ![true, false, false, true, false],
   ![false, true, false, true, false],
   ![true, true, false, true, false],
   ![false, false, true, true, false],
   ![true, false, true, true, false],
   ![false, true, true, true, false],
   ![true, true, true, true, false],
   ![false, false, false, false, true],
   ![true, false, false, false, true],
   ![false, true, false, false, true],
   ![true, true, false, false, true],
   ![false, false, true, false, true],
   ![true, false, true, false, true],
   ![false, true, true, false, true],
   ![true, true, true, false, true],
   ![false, false, false, true, true],
   ![true, false, false, true, true],
   ![false, true, false, true, true],
   ![true, true, false, true, true],
   ![false, false, true, true, true],
   ![true, false, true, true, true],
   ![false, true, true, true, true],
   ![true, true, true, true, true]]

/-- The ten literals of the 5-cube. -/
def allLits5 : List (Fin 5 × Bool) :=
  [(0, false), (0, true), (1, false), (1, true), (2, false), (2, true),
   (3, false), (3, true), (4, false), (4, true)]

/-- Every point is in the list. -/
theorem allPts5_complete :
    ∀ b0 b1 b2 b3 b4 : Bool, ![b0, b1, b2, b3, b4] ∈ allPts5 := by
  decide

theorem allLits5_complete : ∀ (i : Fin 5) (b : Bool),
    (i, b) ∈ allLits5 := by
  decide

/-- Bool-valued "some non-excluded literal forces `F` constant on
    `cube(ρ) ∩ {x i = b}`" — computed over explicit lists. -/
def hasLitB (F : (Fin 5 → Bool) → Bool) (ρ : Fin 5 → Option Bool) :
    Bool :=
  allLits5.any fun p =>
    decide (ρ p.1 ≠ some (!p.2)) &&
    (match allPts5.filter
        (fun x => decide (memCube ρ x) && (x p.1 == p.2)) with
     | [] => true
     | h :: t => t.all fun x => F x == F h)

/-- **The bridge.** A fixable function has a forcing literal at every
    subcube, in the Bool-computed sense. -/
theorem hasLitB_of_fixable {F : (Fin 5 → Bool) → Bool}
    (hF : Fixable F) (ρ : Fin 5 → Option Bool) : hasLitB F ρ = true := by
  obtain ⟨i, bb, hexcl, c, hconst⟩ := hF ρ
  apply List.any_eq_true.mpr
  refine ⟨(i, bb), allLits5_complete i bb, ?_⟩
  simp only [Bool.and_eq_true]
  refine ⟨decide_eq_true hexcl, ?_⟩
  have hmemval : ∀ x ∈ allPts5.filter
      (fun x => decide (memCube ρ x) && (x i == bb)), F x = c := by
    intro x hx
    obtain ⟨-, hcond⟩ := List.mem_filter.mp hx
    simp only [Bool.and_eq_true] at hcond
    obtain ⟨hm, hi⟩ := hcond
    exact hconst x (of_decide_eq_true hm) (by simpa using hi)
  cases hfil : allPts5.filter
      (fun x => decide (memCube ρ x) && (x i == bb)) with
  | nil => rfl
  | cons h t =>
      apply List.all_eq_true.mpr
      intro x hx
      have hxF : F x = c :=
        hmemval x (by rw [hfil]; exact List.mem_cons_of_mem _ hx)
      have hhF : F h = c :=
        hmemval h (by rw [hfil]; exact List.mem_cons_self ..)
      rw [hxF, hhF]
      exact beq_self_eq_true c

/-- Oracle-mined hitting lists of failing subcubes, one per shared
    direction `e`. -/
def case2L (e : Fin 5) : List (Fin 5 → Option Bool) :=
  if e = 0 then
    [pin2 1 2 false true, pin2 1 2 true false, pin2 3 4 false true,
     pin2 3 4 true false, pin2 1 3 false true, pin2 1 4 true false,
     pin2 2 3 false true, pin2 2 4 false true]
  else if e = 1 then
    [pin2 0 2 false true, pin2 0 2 true false, pin2 3 4 false true,
     pin2 3 4 true false, pin2 0 3 false true, pin2 0 4 true false,
     pin2 2 3 false true, pin2 2 4 false true]
  else if e = 2 then
    [pin2 0 1 false true, pin2 0 1 true false, pin2 3 4 false true,
     pin2 3 4 true false, pin2 0 3 false true, pin2 0 4 true false,
     pin2 1 3 false true, pin2 1 4 false true]
  else if e = 3 then
    [pin2 0 1 false true, pin2 0 1 true false, pin2 2 4 false true,
     pin2 2 4 true false, pin2 0 2 false true, pin2 0 4 true false,
     pin2 1 2 false true, pin2 1 4 false true]
  else
    [pin2 0 1 false true, pin2 0 1 true false, pin2 2 3 false true,
     pin2 2 3 true false, pin2 0 2 false true, pin2 0 3 true false,
     pin2 1 2 false true, pin2 1 3 false true]

set_option maxRecDepth 16384 in
theorem case2_kill_0 : ∀ a b : Fin 4, a ≠ b → ∀ cQ : Bool,
    ∀ a2 b2 : Fin 4, a2 ≠ b2 → ∀ cQ2 : Bool,
    ((case2L 0).any fun ρ =>
      !(hasLitB (case2C 0 a b cQ a2 b2 cQ2) ρ)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem case2_kill_1 : ∀ a b : Fin 4, a ≠ b → ∀ cQ : Bool,
    ∀ a2 b2 : Fin 4, a2 ≠ b2 → ∀ cQ2 : Bool,
    ((case2L 1).any fun ρ =>
      !(hasLitB (case2C 1 a b cQ a2 b2 cQ2) ρ)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem case2_kill_2 : ∀ a b : Fin 4, a ≠ b → ∀ cQ : Bool,
    ∀ a2 b2 : Fin 4, a2 ≠ b2 → ∀ cQ2 : Bool,
    ((case2L 2).any fun ρ =>
      !(hasLitB (case2C 2 a b cQ a2 b2 cQ2) ρ)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem case2_kill_3 : ∀ a b : Fin 4, a ≠ b → ∀ cQ : Bool,
    ∀ a2 b2 : Fin 4, a2 ≠ b2 → ∀ cQ2 : Bool,
    ((case2L 3).any fun ρ =>
      !(hasLitB (case2C 3 a b cQ a2 b2 cQ2) ρ)) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem case2_kill_4 : ∀ a b : Fin 4, a ≠ b → ∀ cQ : Bool,
    ∀ a2 b2 : Fin 4, a2 ≠ b2 → ∀ cQ2 : Bool,
    ((case2L 4).any fun ρ =>
      !(hasLitB (case2C 4 a b cQ a2 b2 cQ2) ρ)) = true := by
  decide +kernel

/-- **CASE 2 IS DEAD.** Two witnesses constant on opposite sides of a
    shared direction: the third witness is doubly catalog-classified
    and unfixable — for every parameter choice. -/
theorem case2_dead {w : Fin 3 → (Fin 5 → Bool) → Bool}
    (hfix : ∀ i, Fixable (w i)) {agg : (Fin 3 → Bool) → Bool}
    (heq : (fun x => agg (fun i => w i x)) = maj)
    {i j : Fin 3} (hij : i ≠ j) {e : Fin 5} {cvi cvj : Bool}
    (hci : ∀ x : Fin 5 → Bool, x e = true → w i x = cvi)
    (hcj : ∀ x : Fin 5 → Bool, x e = false → w j x = cvj) : False := by
  obtain ⟨k, hki, hkj, hcompl⟩ := fin3_third_index i j hij
  have href := triple_refines heq
  have href1 : ∀ x x', w i x = w i x' → w j x = w j x' →
      w k x = w k x' → maj x = maj x' := by
    intro x x' h1 h2 h3
    apply href
    intro m
    rcases hcompl m with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  obtain ⟨a, b, hab, cP, cQ, hBf, hCf⟩ :=
    face_classified href1 (hfix j) (hfix k) e true hci
  have href2 : ∀ x x', w j x = w j x' → w i x = w i x' →
      w k x = w k x' → maj x = maj x' :=
    fun x x' h1 h2 h3 => href1 x x' h2 h1 h3
  obtain ⟨a2, b2, hab2, cP2, cQ2, hBf2, hCf2⟩ :=
    face_classified href2 (hfix i) (hfix k) e false hcj
  have hglue : ∀ x, w k x = case2C e a b cQ a2 b2 cQ2 x := by
    intro x
    show w k x = if x e then _ else _
    by_cases hx : x e = true
    · rw [if_pos hx]
      exact hCf x hx
    · have hx' : x e = false := by cases h : x e <;> simp_all
      rw [if_neg hx]
      exact hCf2 x hx'
  have hfixC : Fixable (case2C e a b cQ a2 b2 cQ2) :=
    fixable_congr hglue (hfix k)
  have hkill : ((case2L e).any fun ρ =>
      !(hasLitB (case2C e a b cQ a2 b2 cQ2) ρ)) = true := by
    fin_cases e
    · exact case2_kill_0 a b hab cQ a2 b2 hab2 cQ2
    · exact case2_kill_1 a b hab cQ a2 b2 hab2 cQ2
    · exact case2_kill_2 a b hab cQ a2 b2 hab2 cQ2
    · exact case2_kill_3 a b hab cQ a2 b2 hab2 cQ2
    · exact case2_kill_4 a b hab cQ a2 b2 hab2 cQ2
  obtain ⟨ρ, -, hno⟩ := List.any_eq_true.mp hkill
  rw [Bool.not_eq_true'] at hno
  rw [hasLitB_of_fixable hfixC ρ] at hno
  cases hno

/-! ## §4 Coordinate permutations (for case 3) -/

/-- Reindexing along any map preserves fixability: the forcing literal
    pulls back. -/
theorem fixable_reindex {f : (Fin 5 → Bool) → Bool} (hf : Fixable f)
    (q : Fin 5 → Fin 5) :
    Fixable (fun x => f (fun j => x (q j))) := by
  intro ρ
  obtain ⟨i, b, hexcl, c, hconst⟩ := hf (fun j => ρ (q j))
  refine ⟨q i, b, hexcl, c, fun x hx hxi => ?_⟩
  exact hconst (fun j => x (q j)) (fun j bj hj => hx (q j) bj hj) hxi

/-- Majority is invariant under coordinate permutation. -/
theorem maj_reindex (p q : Fin 5 → Fin 5) (hpq : ∀ j, p (q j) = j)
    (hqp : ∀ j, q (p j) = j) (x : Fin 5 → Bool) :
    maj (fun j => x (q j)) = maj x := by
  have hcard : (Finset.univ.filter fun i => x (q i) = true).card
      = (Finset.univ.filter fun i => x i = true).card := by
    refine Finset.card_bij' (fun a _ => q a) (fun a _ => p a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [hqp a]
      exact ha
    · intro a _
      exact hpq a
    · intro a _
      exact hqp a
  show decide (5 < 2 * (Finset.univ.filter
    fun i => x (q i) = true).card) = maj x
  rw [hcard]
  rfl

/-- Smallest coordinate outside `{d0, d1, d2}`. -/
def rest0 (d0 d1 d2 : Fin 5) : Fin 5 :=
  if d0 ≠ 0 ∧ d1 ≠ 0 ∧ d2 ≠ 0 then 0
  else if d0 ≠ 1 ∧ d1 ≠ 1 ∧ d2 ≠ 1 then 1
  else if d0 ≠ 2 ∧ d1 ≠ 2 ∧ d2 ≠ 2 then 2
  else if d0 ≠ 3 ∧ d1 ≠ 3 ∧ d2 ≠ 3 then 3 else 4

/-- Largest coordinate outside `{d0, d1, d2}`. -/
def rest1 (d0 d1 d2 : Fin 5) : Fin 5 :=
  if d0 ≠ 4 ∧ d1 ≠ 4 ∧ d2 ≠ 4 then 4
  else if d0 ≠ 3 ∧ d1 ≠ 3 ∧ d2 ≠ 3 then 3
  else if d0 ≠ 2 ∧ d1 ≠ 2 ∧ d2 ≠ 2 then 2
  else if d0 ≠ 1 ∧ d1 ≠ 1 ∧ d2 ≠ 1 then 1 else 0

/-- Permutation sending `0,1,2` to the three directions. -/
def perm3p (d0 d1 d2 : Fin 5) : Fin 5 → Fin 5 :=
  fun m => if m = 0 then d0 else if m = 1 then d1 else if m = 2 then d2
    else if m = 3 then rest0 d0 d1 d2 else rest1 d0 d1 d2

/-- Its inverse. -/
def perm3q (d0 d1 d2 : Fin 5) : Fin 5 → Fin 5 :=
  fun j => if j = d0 then 0 else if j = d1 then 1 else if j = d2 then 2
    else if j = rest0 d0 d1 d2 then 3 else 4

theorem perm3_spec : ∀ d0 d1 d2 : Fin 5, d0 ≠ d1 → d0 ≠ d2 → d1 ≠ d2 →
    (∀ j, perm3p d0 d1 d2 (perm3q d0 d1 d2 j) = j) ∧
    (∀ j, perm3q d0 d1 d2 (perm3p d0 d1 d2 j) = j) ∧
    perm3q d0 d1 d2 d0 = 0 ∧ perm3q d0 d1 d2 d1 = 1 ∧
    perm3q d0 d1 d2 d2 = 2 := by
  decide

/-! ## §5 Case 3: infrastructure and oracle data -/

def allPts4 : List (Fin 4 → Bool) :=
  [![false, false, false, false],
   ![true, false, false, false],
   ![false, true, false, false],
   ![true, true, false, false],
   ![false, false, true, false],
   ![true, false, true, false],
   ![false, true, true, false],
   ![true, true, true, false],
   ![false, false, false, true],
   ![true, false, false, true],
   ![false, true, false, true],
   ![true, true, false, true],
   ![false, false, true, true],
   ![true, false, true, true],
   ![false, true, true, true],
   ![true, true, true, true]]

def pin1 (i : Fin 5) (bi : Bool) : Fin 5 → Option Bool :=
  fun m => if m = i then some bi else none

def pin3 (i j k : Fin 5) (bi bj bk : Bool) : Fin 5 → Option Bool :=
  fun m => if m = i then some bi else if m = j then some bj
    else if m = k then some bk else none

/-- Slice-constancy filters (Bool-computed): the catalog form is
    constant with value `cv` on the slice `{y k = σ}`. -/
def F1P (σ : Bool) (k : Fin 4) (a b : Fin 4) (c cv : Bool) : Bool :=
  allPts4.all fun y => !(y k == σ) || (catPσ σ a b c y == cv)

def F1Q (σ : Bool) (k : Fin 4) (a b : Fin 4) (c cv : Bool) : Bool :=
  allPts4.all fun y => !(y k == σ) || (catQσ σ a b c y == cv)

/-- Cross-face consistency filters (Bool-computed). -/
def F2A (σ : Bool) (a1 b1 : Fin 4) (c1 : Bool) (a2 b2 : Fin 4)
    (c2 : Bool) : Bool :=
  allPts5.all fun x => !((x 1 == σ) && (x 2 == σ)) ||
    (catPσ σ a1 b1 c1 (delAt 1 x) == catPσ σ a2 b2 c2 (delAt 2 x))

def F2B (σ : Bool) (a0 b0 : Fin 4) (c0 : Bool) (a2 b2 : Fin 4)
    (c2 : Bool) : Bool :=
  allPts5.all fun x => !((x 0 == σ) && (x 2 == σ)) ||
    (catPσ σ a0 b0 c0 (delAt 0 x) == catQσ σ a2 b2 c2 (delAt 2 x))

def F2C (σ : Bool) (a0 b0 : Fin 4) (c0 : Bool) (a1 b1 : Fin 4)
    (c1 : Bool) : Bool :=
  allPts5.all fun x => !((x 0 == σ) && (x 1 == σ)) ||
    (catQσ σ a0 b0 c0 (delAt 0 x) == catQσ σ a1 b1 c1 (delAt 1 x))

theorem F1P_of {σ : Bool} {k a b : Fin 4} {c cv : Bool}
    (h : ∀ y : Fin 4 → Bool, y k = σ → catPσ σ a b c y = cv) :
    F1P σ k a b c cv = true := by
  apply List.all_eq_true.mpr
  intro y _
  by_cases hy : y k = σ
  · rw [beq_iff_eq.mpr (h y hy), Bool.or_true]
  · rw [beq_eq_false_iff_ne.mpr hy]
    rfl

theorem F1Q_of {σ : Bool} {k a b : Fin 4} {c cv : Bool}
    (h : ∀ y : Fin 4 → Bool, y k = σ → catQσ σ a b c y = cv) :
    F1Q σ k a b c cv = true := by
  apply List.all_eq_true.mpr
  intro y _
  by_cases hy : y k = σ
  · rw [beq_iff_eq.mpr (h y hy), Bool.or_true]
  · rw [beq_eq_false_iff_ne.mpr hy]
    rfl

theorem F2A_of {σ : Bool} {a1 b1 : Fin 4} {c1 : Bool} {a2 b2 : Fin 4}
    {c2 : Bool}
    (h : ∀ x : Fin 5 → Bool, x 1 = σ → x 2 = σ →
      catPσ σ a1 b1 c1 (delAt 1 x) = catPσ σ a2 b2 c2 (delAt 2 x)) :
    F2A σ a1 b1 c1 a2 b2 c2 = true := by
  apply List.all_eq_true.mpr
  intro x _
  by_cases h1 : x 1 = σ
  · by_cases h2 : x 2 = σ
    · rw [beq_iff_eq.mpr (h x h1 h2), Bool.or_true]
    · rw [beq_eq_false_iff_ne.mpr h2, Bool.and_false]
      rfl
  · rw [beq_eq_false_iff_ne.mpr h1, Bool.false_and]
    rfl

theorem F2B_of {σ : Bool} {a0 b0 : Fin 4} {c0 : Bool} {a2 b2 : Fin 4}
    {c2 : Bool}
    (h : ∀ x : Fin 5 → Bool, x 0 = σ → x 2 = σ →
      catPσ σ a0 b0 c0 (delAt 0 x) = catQσ σ a2 b2 c2 (delAt 2 x)) :
    F2B σ a0 b0 c0 a2 b2 c2 = true := by
  apply List.all_eq_true.mpr
  intro x _
  by_cases h0 : x 0 = σ
  · by_cases h2 : x 2 = σ
    · rw [beq_iff_eq.mpr (h x h0 h2), Bool.or_true]
    · rw [beq_eq_false_iff_ne.mpr h2, Bool.and_false]
      rfl
  · rw [beq_eq_false_iff_ne.mpr h0, Bool.false_and]
    rfl

theorem F2C_of {σ : Bool} {a0 b0 : Fin 4} {c0 : Bool} {a1 b1 : Fin 4}
    {c1 : Bool}
    (h : ∀ x : Fin 5 → Bool, x 0 = σ → x 1 = σ →
      catQσ σ a0 b0 c0 (delAt 0 x) = catQσ σ a1 b1 c1 (delAt 1 x)) :
    F2C σ a0 b0 c0 a1 b1 c1 = true := by
  apply List.all_eq_true.mpr
  intro x _
  by_cases h0 : x 0 = σ
  · by_cases h1 : x 1 = σ
    · rw [beq_iff_eq.mpr (h x h0 h1), Bool.or_true]
    · rw [beq_eq_false_iff_ne.mpr h1, Bool.and_false]
      rfl
  · rw [beq_eq_false_iff_ne.mpr h0, Bool.false_and]
    rfl

/-- The 4-point free region: all three directions at `!σ`. -/
def regPt (σ : Bool) (u v : Bool) : Fin 5 → Bool :=
  fun j => if j = 3 then u else if j = 4 then v else !σ

/-- Assembled case-3 witnesses (canonical directions `0, 1, 2`). -/
def case3A (σ : Bool) (a1 b1 : Fin 4) (c1 : Bool) (a2 b2 : Fin 4)
    (c2 cv : Bool) (r : Bool → Bool → Bool) (x : Fin 5 → Bool) : Bool :=
  if x 0 = σ then cv
  else if x 1 = σ then catPσ σ a1 b1 c1 (delAt 1 x)
  else if x 2 = σ then catPσ σ a2 b2 c2 (delAt 2 x)
  else r (x 3) (x 4)

def case3B (σ : Bool) (a0 b0 : Fin 4) (c0 : Bool) (a2 b2 : Fin 4)
    (c2 cv : Bool) (r : Bool → Bool → Bool) (x : Fin 5 → Bool) : Bool :=
  if x 0 = σ then catPσ σ a0 b0 c0 (delAt 0 x)
  else if x 1 = σ then cv
  else if x 2 = σ then catQσ σ a2 b2 c2 (delAt 2 x)
  else r (x 3) (x 4)

def case3C (σ : Bool) (a0 b0 : Fin 4) (c0 : Bool) (a1 b1 : Fin 4)
    (c1 cv : Bool) (r : Bool → Bool → Bool) (x : Fin 5 → Bool) : Bool :=
  if x 0 = σ then catQσ σ a0 b0 c0 (delAt 0 x)
  else if x 1 = σ then catQσ σ a1 b1 c1 (delAt 1 x)
  else if x 2 = σ then cv
  else r (x 3) (x 4)

/-- Parameter/region tuple of a case-3 witness whose assembled function
    happens to be fixable — the oracle-mined exceptional list entries. -/
structure W3Bad where
  sig : Bool
  fa : Fin 4
  fb : Fin 4
  pc : Bool
  ga : Fin 4
  gb : Fin 4
  qc : Bool
  cv : Bool
  r00 : Bool
  r10 : Bool
  r01 : Bool
  r11 : Bool
deriving DecidableEq

/-- Oracle-mined hitting lists of failing subcubes (case 3). -/
def case3LA (σ : Bool) : List (Fin 5 → Option Bool) :=
  if σ then
    [pin2 0 1 false false, pin2 0 4 false false, pin1 0 false,
     pin2 0 3 false false, pin2 0 2 false false, pin2 0 4 false true,
     pin2 0 3 false true, pin3 0 3 4 false false true,
     pin3 0 3 4 false true false]
  else
    [pin2 0 1 true true, pin2 0 4 true true, pin1 0 true,
     pin2 0 3 true false, pin2 0 2 true true, pin2 0 3 true true,
     pin2 0 4 true false, pin3 0 3 4 true false true,
     pin3 0 3 4 true true false]

def case3LB (σ : Bool) : List (Fin 5 → Option Bool) :=
  if σ then
    [pin2 0 1 false false, pin2 1 4 false false, pin1 1 false,
     pin3 1 3 4 false false true, pin2 1 2 false false,
     pin2 1 3 false true, pin2 1 4 false true,
     pin3 1 3 4 false true false, pin2 1 3 false false]
  else
    [pin2 0 1 true true, pin2 1 3 true true, pin1 1 true,
     pin2 1 4 true false, pin2 1 2 true true, pin2 1 4 true true,
     pin2 1 3 true false, pin3 1 3 4 true false true,
     pin3 1 3 4 true true false]

def case3LC (σ : Bool) : List (Fin 5 → Option Bool) :=
  if σ then
    [pin2 0 2 false false, pin2 2 4 false false, pin1 2 false,
     pin2 2 3 false true, pin2 1 2 false false, pin2 2 3 false false,
     pin2 2 4 false true, pin3 2 3 4 false true false,
     pin3 2 3 4 false false true]
  else
    [pin2 1 2 true true, pin2 2 4 true true, pin1 2 true,
     pin2 2 3 true false, pin2 0 2 true true, pin2 2 3 true true,
     pin2 2 4 true false, pin3 2 3 4 true false true,
     pin3 2 3 4 true true false]

/-- Oracle-mined bad lists: the ONLY parameter/region combinations whose
    assembled witness is fixable (16 per sign, per witness). -/
def badA : List W3Bad :=
  [⟨true, 0, 2, false, 0, 2, false, false, true, false, true, false⟩,
   ⟨true, 0, 2, false, 2, 0, false, false, true, false, true, false⟩,
   ⟨true, 0, 2, true, 0, 2, true, true, false, true, false, true⟩,
   ⟨true, 0, 2, true, 2, 0, true, true, false, true, false, true⟩,
   ⟨true, 0, 3, false, 0, 3, false, false, true, true, false, false⟩,
   ⟨true, 0, 3, false, 3, 0, false, false, true, true, false, false⟩,
   ⟨true, 0, 3, true, 0, 3, true, true, false, false, true, true⟩,
   ⟨true, 0, 3, true, 3, 0, true, true, false, false, true, true⟩,
   ⟨true, 2, 0, false, 0, 2, false, false, true, false, true, false⟩,
   ⟨true, 2, 0, false, 2, 0, false, false, true, false, true, false⟩,
   ⟨true, 2, 0, true, 0, 2, true, true, false, true, false, true⟩,
   ⟨true, 2, 0, true, 2, 0, true, true, false, true, false, true⟩,
   ⟨true, 3, 0, false, 0, 3, false, false, true, true, false, false⟩,
   ⟨true, 3, 0, false, 3, 0, false, false, true, true, false, false⟩,
   ⟨true, 3, 0, true, 0, 3, true, true, false, false, true, true⟩,
   ⟨true, 3, 0, true, 3, 0, true, true, false, false, true, true⟩,
   ⟨false, 0, 2, false, 0, 2, false, true, true, false, true, false⟩,
   ⟨false, 0, 2, false, 2, 0, false, true, true, false, true, false⟩,
   ⟨false, 0, 2, true, 0, 2, true, false, false, true, false, true⟩,
   ⟨false, 0, 2, true, 2, 0, true, false, false, true, false, true⟩,
   ⟨false, 0, 3, false, 0, 3, false, true, true, true, false, false⟩,
   ⟨false, 0, 3, false, 3, 0, false, true, true, true, false, false⟩,
   ⟨false, 0, 3, true, 0, 3, true, false, false, false, true, true⟩,
   ⟨false, 0, 3, true, 3, 0, true, false, false, false, true, true⟩,
   ⟨false, 2, 0, false, 0, 2, false, true, true, false, true, false⟩,
   ⟨false, 2, 0, false, 2, 0, false, true, true, false, true, false⟩,
   ⟨false, 2, 0, true, 0, 2, true, false, false, true, false, true⟩,
   ⟨false, 2, 0, true, 2, 0, true, false, false, true, false, true⟩,
   ⟨false, 3, 0, false, 0, 3, false, true, true, true, false, false⟩,
   ⟨false, 3, 0, false, 3, 0, false, true, true, true, false, false⟩,
   ⟨false, 3, 0, true, 0, 3, true, false, false, false, true, true⟩,
   ⟨false, 3, 0, true, 3, 0, true, false, false, false, true, true⟩]

def badB : List W3Bad :=
  [⟨true, 0, 2, false, 0, 3, false, false, true, false, true, false⟩,
   ⟨true, 0, 2, false, 3, 0, false, false, true, false, true, false⟩,
   ⟨true, 0, 2, true, 0, 3, true, true, false, true, false, true⟩,
   ⟨true, 0, 2, true, 3, 0, true, true, false, true, false, true⟩,
   ⟨true, 0, 3, false, 0, 2, false, false, true, true, false, false⟩,
   ⟨true, 0, 3, false, 2, 0, false, false, true, true, false, false⟩,
   ⟨true, 0, 3, true, 0, 2, true, true, false, false, true, true⟩,
   ⟨true, 0, 3, true, 2, 0, true, true, false, false, true, true⟩,
   ⟨true, 2, 0, false, 0, 3, false, false, true, false, true, false⟩,
   ⟨true, 2, 0, false, 3, 0, false, false, true, false, true, false⟩,
   ⟨true, 2, 0, true, 0, 3, true, true, false, true, false, true⟩,
   ⟨true, 2, 0, true, 3, 0, true, true, false, true, false, true⟩,
   ⟨true, 3, 0, false, 0, 2, false, false, true, true, false, false⟩,
   ⟨true, 3, 0, false, 2, 0, false, false, true, true, false, false⟩,
   ⟨true, 3, 0, true, 0, 2, true, true, false, false, true, true⟩,
   ⟨true, 3, 0, true, 2, 0, true, true, false, false, true, true⟩,
   ⟨false, 0, 2, false, 0, 3, false, true, true, false, true, false⟩,
   ⟨false, 0, 2, false, 3, 0, false, true, true, false, true, false⟩,
   ⟨false, 0, 2, true, 0, 3, true, false, false, true, false, true⟩,
   ⟨false, 0, 2, true, 3, 0, true, false, false, true, false, true⟩,
   ⟨false, 0, 3, false, 0, 2, false, true, true, true, false, false⟩,
   ⟨false, 0, 3, false, 2, 0, false, true, true, true, false, false⟩,
   ⟨false, 0, 3, true, 0, 2, true, false, false, false, true, true⟩,
   ⟨false, 0, 3, true, 2, 0, true, false, false, false, true, true⟩,
   ⟨false, 2, 0, false, 0, 3, false, true, true, false, true, false⟩,
   ⟨false, 2, 0, false, 3, 0, false, true, true, false, true, false⟩,
   ⟨false, 2, 0, true, 0, 3, true, false, false, true, false, true⟩,
   ⟨false, 2, 0, true, 3, 0, true, false, false, true, false, true⟩,
   ⟨false, 3, 0, false, 0, 2, false, true, true, true, false, false⟩,
   ⟨false, 3, 0, false, 2, 0, false, true, true, true, false, false⟩,
   ⟨false, 3, 0, true, 0, 2, true, false, false, false, true, true⟩,
   ⟨false, 3, 0, true, 2, 0, true, false, false, false, true, true⟩]

def badC : List W3Bad :=
  [⟨true, 0, 2, false, 0, 2, false, false, true, true, false, false⟩,
   ⟨true, 0, 2, false, 2, 0, false, false, true, true, false, false⟩,
   ⟨true, 0, 2, true, 0, 2, true, true, false, false, true, true⟩,
   ⟨true, 0, 2, true, 2, 0, true, true, false, false, true, true⟩,
   ⟨true, 0, 3, false, 0, 3, false, false, true, false, true, false⟩,
   ⟨true, 0, 3, false, 3, 0, false, false, true, false, true, false⟩,
   ⟨true, 0, 3, true, 0, 3, true, true, false, true, false, true⟩,
   ⟨true, 0, 3, true, 3, 0, true, true, false, true, false, true⟩,
   ⟨true, 2, 0, false, 0, 2, false, false, true, true, false, false⟩,
   ⟨true, 2, 0, false, 2, 0, false, false, true, true, false, false⟩,
   ⟨true, 2, 0, true, 0, 2, true, true, false, false, true, true⟩,
   ⟨true, 2, 0, true, 2, 0, true, true, false, false, true, true⟩,
   ⟨true, 3, 0, false, 0, 3, false, false, true, false, true, false⟩,
   ⟨true, 3, 0, false, 3, 0, false, false, true, false, true, false⟩,
   ⟨true, 3, 0, true, 0, 3, true, true, false, true, false, true⟩,
   ⟨true, 3, 0, true, 3, 0, true, true, false, true, false, true⟩,
   ⟨false, 0, 2, false, 0, 2, false, true, true, true, false, false⟩,
   ⟨false, 0, 2, false, 2, 0, false, true, true, true, false, false⟩,
   ⟨false, 0, 2, true, 0, 2, true, false, false, false, true, true⟩,
   ⟨false, 0, 2, true, 2, 0, true, false, false, false, true, true⟩,
   ⟨false, 0, 3, false, 0, 3, false, true, true, false, true, false⟩,
   ⟨false, 0, 3, false, 3, 0, false, true, true, false, true, false⟩,
   ⟨false, 0, 3, true, 0, 3, true, false, false, true, false, true⟩,
   ⟨false, 0, 3, true, 3, 0, true, false, false, true, false, true⟩,
   ⟨false, 2, 0, false, 0, 2, false, true, true, true, false, false⟩,
   ⟨false, 2, 0, false, 2, 0, false, true, true, true, false, false⟩,
   ⟨false, 2, 0, true, 0, 2, true, false, false, false, true, true⟩,
   ⟨false, 2, 0, true, 2, 0, true, false, false, false, true, true⟩,
   ⟨false, 3, 0, false, 0, 3, false, true, true, false, true, false⟩,
   ⟨false, 3, 0, false, 3, 0, false, true, true, false, true, false⟩,
   ⟨false, 3, 0, true, 0, 3, true, false, false, true, false, true⟩,
   ⟨false, 3, 0, true, 3, 0, true, false, false, true, false, true⟩]

/-! ## §6 Case 3: the kills -/

set_option maxRecDepth 16384 in
/-- **Witness-A kill.** Under the derivable filters, the assembled first
    witness is unfixable (hitting list) or its parameters are on the
    explicit bad list. -/
theorem case3_killA : ∀ (σ : Bool) (a1 b1 : Fin 4), a1 ≠ b1 →
    ∀ (c1 : Bool) (a2 b2 : Fin 4), a2 ≠ b2 → ∀ (c2 cv : Bool),
    F1P σ 0 a1 b1 c1 cv = true → F1P σ 0 a2 b2 c2 cv = true →
    F2A σ a1 b1 c1 a2 b2 c2 = true →
    ∀ r : Bool → Bool → Bool,
    ((case3LA σ).all fun ρ =>
      hasLitB (case3A σ a1 b1 c1 a2 b2 c2 cv r) ρ) = true →
    (⟨σ, a1, b1, c1, a2, b2, c2, cv, r false false, r true false,
      r false true, r true true⟩ : W3Bad) ∈ badA := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- **Witness-B kill.** -/
theorem case3_killB : ∀ (σ : Bool) (a0 b0 : Fin 4), a0 ≠ b0 →
    ∀ (c0 : Bool) (a2 b2 : Fin 4), a2 ≠ b2 → ∀ (c2 cv : Bool),
    F1P σ 0 a0 b0 c0 cv = true → F1Q σ 1 a2 b2 c2 cv = true →
    F2B σ a0 b0 c0 a2 b2 c2 = true →
    ∀ r : Bool → Bool → Bool,
    ((case3LB σ).all fun ρ =>
      hasLitB (case3B σ a0 b0 c0 a2 b2 c2 cv r) ρ) = true →
    (⟨σ, a0, b0, c0, a2, b2, c2, cv, r false false, r true false,
      r false true, r true true⟩ : W3Bad) ∈ badB := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- **Witness-C kill.** -/
theorem case3_killC : ∀ (σ : Bool) (a0 b0 : Fin 4), a0 ≠ b0 →
    ∀ (c0 : Bool) (a1 b1 : Fin 4), a1 ≠ b1 → ∀ (c1 cv : Bool),
    F1Q σ 1 a0 b0 c0 cv = true → F1Q σ 1 a1 b1 c1 cv = true →
    F2C σ a0 b0 c0 a1 b1 c1 = true →
    ∀ r : Bool → Bool → Bool,
    ((case3LC σ).all fun ρ =>
      hasLitB (case3C σ a0 b0 c0 a1 b1 c1 cv r) ρ) = true →
    (⟨σ, a0, b0, c0, a1, b1, c1, cv, r false false, r true false,
      r false true, r true true⟩ : W3Bad) ∈ badC := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- **The compatibility kill.** No three bad-list members share the
    face subsets a genuine triple must share: three simultaneously
    fixable case-3 witnesses are impossible. -/
theorem case3_compat : ∀ tA ∈ badA, ∀ tB ∈ badB, ∀ tC ∈ badC,
    ¬(tA.sig = tB.sig ∧ tB.sig = tC.sig ∧
      tC.ga = tA.fa ∧ tC.gb = tA.fb ∧ tA.ga = tB.ga ∧ tA.gb = tB.gb ∧
      tB.fa = tC.fa ∧ tB.fb = tC.fb) := by
  decide +kernel

/-! ## §7 Case 3 is dead -/

theorem ins5_0_1 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (0 : Fin 5) σ y 1 = y 0 := by decide

theorem ins5_0_2 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (0 : Fin 5) σ y 2 = y 1 := by decide

theorem ins5_1_0 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (1 : Fin 5) σ y 0 = y 0 := by decide

theorem ins5_1_2 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (1 : Fin 5) σ y 2 = y 1 := by decide

theorem ins5_2_0 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (2 : Fin 5) σ y 0 = y 0 := by decide

theorem ins5_2_1 : ∀ (σ : Bool) (y : Fin 4 → Bool),
    insertAt5 (2 : Fin 5) σ y 1 = y 1 := by decide

theorem regPt_coords : ∀ σ u v : Bool,
    regPt σ u v 0 = !σ ∧ regPt σ u v 1 = !σ ∧ regPt σ u v 2 = !σ ∧
    regPt σ u v 3 = u ∧ regPt σ u v 4 = v := by decide

/-- **CASE 3 IS DEAD.** Three distinct directions with unanimous signs:
    each witness is piecewise-catalog, hence unfixable or on its bad
    list; the bad lists are mutually incompatible. -/
theorem case3_dead {w : Fin 3 → (Fin 5 → Bool) → Bool}
    (hfix : ∀ i, Fixable (w i)) {agg : (Fin 3 → Bool) → Bool}
    (heq : (fun x => agg (fun i => w i x)) = maj)
    {d : Fin 3 → Fin 5} {β cv : Fin 3 → Bool}
    (hconst : ∀ i x, x (d i) = β i → w i x = cv i)
    (h01 : d 0 ≠ d 1) (h02 : d 0 ≠ d 2) (h12 : d 1 ≠ d 2)
    (hσ1 : β 0 = β 1) (hσ2 : β 1 = β 2) : False := by
  obtain ⟨hpq, hqp, hq0, hq1, hq2⟩ :=
    perm3_spec (d 0) (d 1) (d 2) h01 h02 h12
  set σ : Bool := β 0 with hσdef
  set q : Fin 5 → Fin 5 := perm3q (d 0) (d 1) (d 2) with hqdef
  set p : Fin 5 → Fin 5 := perm3p (d 0) (d 1) (d 2) with hpdef
  set W0 : (Fin 5 → Bool) → Bool := fun x => w 0 (fun j => x (q j))
    with hW0
  set W1 : (Fin 5 → Bool) → Bool := fun x => w 1 (fun j => x (q j))
    with hW1
  set W2 : (Fin 5 → Bool) → Bool := fun x => w 2 (fun j => x (q j))
    with hW2
  have hfx0 : Fixable W0 := fixable_reindex (hfix 0) q
  have hfx1 : Fixable W1 := fixable_reindex (hfix 1) q
  have hfx2 : Fixable W2 := fixable_reindex (hfix 2) q
  have heq' : (fun x => agg (fun i => (![W0, W1, W2] : Fin 3 → _) i x))
      = maj := by
    funext x
    have hfns : (fun i => (![W0, W1, W2] : Fin 3 → _) i x)
        = fun i => w i (fun j => x (q j)) := by
      funext i
      fin_cases i <;> rfl
    rw [hfns]
    calc agg (fun i => w i (fun j => x (q j)))
        = maj (fun j => x (q j)) := congrFun heq _
      _ = maj x := maj_reindex p q hpq hqp x
  have htr := triple_refines heq'
  have hrefF0 : ∀ x x', W0 x = W0 x' → W1 x = W1 x' → W2 x = W2 x' →
      maj x = maj x' := by
    intro x x' h0 h1 h2
    apply htr
    intro m
    fin_cases m
    · exact h0
    · exact h1
    · exact h2
  have hrefF1 : ∀ x x', W1 x = W1 x' → W0 x = W0 x' → W2 x = W2 x' →
      maj x = maj x' := fun x x' h1 h0 h2 => hrefF0 x x' h0 h1 h2
  have hrefF2 : ∀ x x', W2 x = W2 x' → W0 x = W0 x' → W1 x = W1 x' →
      maj x = maj x' := fun x x' h2 h0 h1 => hrefF0 x x' h0 h1 h2
  have hc0 : ∀ x : Fin 5 → Bool, x 0 = σ → W0 x = cv 0 := by
    intro x hx
    show w 0 (fun j => x (q j)) = cv 0
    apply hconst 0
    show x (q (d 0)) = β 0
    rw [hq0, ← hσdef]
    exact hx
  have hc1 : ∀ x : Fin 5 → Bool, x 1 = σ → W1 x = cv 1 := by
    intro x hx
    show w 1 (fun j => x (q j)) = cv 1
    apply hconst 1
    show x (q (d 1)) = β 1
    rw [hq1, ← hσ1]
    exact hx
  have hc2 : ∀ x : Fin 5 → Bool, x 2 = σ → W2 x = cv 2 := by
    intro x hx
    show w 2 (fun j => x (q j)) = cv 2
    apply hconst 2
    show x (q (d 2)) = β 2
    rw [hq2, ← hσ2, ← hσ1]
    exact hx
  obtain ⟨a0, b0, hab0, cP0, cQ0, hB0, hC0⟩ :=
    face_classified hrefF0 hfx1 hfx2 0 σ hc0
  obtain ⟨a1, b1, hab1, cP1, cQ1, hA1, hC1⟩ :=
    face_classified hrefF1 hfx0 hfx2 1 σ hc1
  obtain ⟨a2, b2, hab2, cP2, cQ2, hA2, hB2⟩ :=
    face_classified hrefF2 hfx0 hfx1 2 σ hc2
  set rA : Bool → Bool → Bool := fun u v => W0 (regPt σ u v) with hrA
  set rB : Bool → Bool → Bool := fun u v => W1 (regPt σ u v) with hrB
  set rC : Bool → Bool → Bool := fun u v => W2 (regPt σ u v) with hrC
  -- glue each witness to its assembled form
  have hb : ∀ (x : Fin 5 → Bool) (m : Fin 5), ¬ x m = σ → x m = !σ := by
    intro x m hm
    cases hσv : σ <;> cases hxv : x m <;> simp_all
  have hregeq : ∀ x : Fin 5 → Bool, ¬ x 0 = σ → ¬ x 1 = σ → ¬ x 2 = σ →
      x = regPt σ (x 3) (x 4) := by
    intro x h0 h1 h2
    obtain ⟨hr0, hr1, hr2, hr3, hr4⟩ := regPt_coords σ (x 3) (x 4)
    funext j
    fin_cases j
    · show x 0 = regPt σ (x 3) (x 4) 0
      rw [hr0]; exact hb x 0 h0
    · show x 1 = regPt σ (x 3) (x 4) 1
      rw [hr1]; exact hb x 1 h1
    · show x 2 = regPt σ (x 3) (x 4) 2
      rw [hr2]; exact hb x 2 h2
    · show x 3 = regPt σ (x 3) (x 4) 3
      rw [hr3]
    · show x 4 = regPt σ (x 3) (x 4) 4
      rw [hr4]
  have hglueA : ∀ x, W0 x = case3A σ a1 b1 cP1 a2 b2 cP2 (cv 0) rA x := by
    intro x
    show W0 x = if x 0 = σ then _ else _
    by_cases h0 : x 0 = σ
    · rw [if_pos h0]; exact hc0 x h0
    · rw [if_neg h0]
      by_cases h1 : x 1 = σ
      · rw [if_pos h1]; exact hA1 x h1
      · rw [if_neg h1]
        by_cases h2 : x 2 = σ
        · rw [if_pos h2]; exact hA2 x h2
        · rw [if_neg h2]
          calc W0 x = W0 (regPt σ (x 3) (x 4)) := by
                rw [← hregeq x h0 h1 h2]
            _ = rA (x 3) (x 4) := rfl
  have hglueB : ∀ x, W1 x = case3B σ a0 b0 cP0 a2 b2 cQ2 (cv 1) rB x := by
    intro x
    show W1 x = if x 0 = σ then _ else _
    by_cases h0 : x 0 = σ
    · rw [if_pos h0]; exact hB0 x h0
    · rw [if_neg h0]
      by_cases h1 : x 1 = σ
      · rw [if_pos h1]; exact hc1 x h1
      · rw [if_neg h1]
        by_cases h2 : x 2 = σ
        · rw [if_pos h2]; exact hB2 x h2
        · rw [if_neg h2]
          calc W1 x = W1 (regPt σ (x 3) (x 4)) := by
                rw [← hregeq x h0 h1 h2]
            _ = rB (x 3) (x 4) := rfl
  have hglueC : ∀ x, W2 x = case3C σ a0 b0 cQ0 a1 b1 cQ1 (cv 2) rC x := by
    intro x
    show W2 x = if x 0 = σ then _ else _
    by_cases h0 : x 0 = σ
    · rw [if_pos h0]; exact hC0 x h0
    · rw [if_neg h0]
      by_cases h1 : x 1 = σ
      · rw [if_pos h1]; exact hC1 x h1
      · rw [if_neg h1]
        by_cases h2 : x 2 = σ
        · rw [if_pos h2]; exact hc2 x h2
        · rw [if_neg h2]
          calc W2 x = W2 (regPt σ (x 3) (x 4)) := by
                rw [← hregeq x h0 h1 h2]
            _ = rC (x 3) (x 4) := rfl
  -- slice-constancy facts
  have hslA1 : ∀ y : Fin 4 → Bool, y 0 = σ → catPσ σ a1 b1 cP1 y = cv 0 := by
    intro y hy
    have h := hA1 (insertAt5 1 σ y) (insertAt5_self 1 σ y)
    rw [delAt_insertAt5] at h
    rw [hc0 _ (by rw [ins5_1_0]; exact hy)] at h
    exact h.symm
  have hslA2 : ∀ y : Fin 4 → Bool, y 0 = σ → catPσ σ a2 b2 cP2 y = cv 0 := by
    intro y hy
    have h := hA2 (insertAt5 2 σ y) (insertAt5_self 2 σ y)
    rw [delAt_insertAt5] at h
    rw [hc0 _ (by rw [ins5_2_0]; exact hy)] at h
    exact h.symm
  have hslB0 : ∀ y : Fin 4 → Bool, y 0 = σ → catPσ σ a0 b0 cP0 y = cv 1 := by
    intro y hy
    have h := hB0 (insertAt5 0 σ y) (insertAt5_self 0 σ y)
    rw [delAt_insertAt5] at h
    rw [hc1 _ (by rw [ins5_0_1]; exact hy)] at h
    exact h.symm
  have hslB2 : ∀ y : Fin 4 → Bool, y 1 = σ → catQσ σ a2 b2 cQ2 y = cv 1 := by
    intro y hy
    have h := hB2 (insertAt5 2 σ y) (insertAt5_self 2 σ y)
    rw [delAt_insertAt5] at h
    rw [hc1 _ (by rw [ins5_2_1]; exact hy)] at h
    exact h.symm
  have hslC0 : ∀ y : Fin 4 → Bool, y 1 = σ → catQσ σ a0 b0 cQ0 y = cv 2 := by
    intro y hy
    have h := hC0 (insertAt5 0 σ y) (insertAt5_self 0 σ y)
    rw [delAt_insertAt5] at h
    rw [hc2 _ (by rw [ins5_0_2]; exact hy)] at h
    exact h.symm
  have hslC1 : ∀ y : Fin 4 → Bool, y 1 = σ → catQσ σ a1 b1 cQ1 y = cv 2 := by
    intro y hy
    have h := hC1 (insertAt5 1 σ y) (insertAt5_self 1 σ y)
    rw [delAt_insertAt5] at h
    rw [hc2 _ (by rw [ins5_1_2]; exact hy)] at h
    exact h.symm
  -- cross-face consistency facts
  have hF2A : ∀ x : Fin 5 → Bool, x 1 = σ → x 2 = σ →
      catPσ σ a1 b1 cP1 (delAt 1 x) = catPσ σ a2 b2 cP2 (delAt 2 x) :=
    fun x hx1 hx2 => (hA1 x hx1).symm.trans (hA2 x hx2)
  have hF2B : ∀ x : Fin 5 → Bool, x 0 = σ → x 2 = σ →
      catPσ σ a0 b0 cP0 (delAt 0 x) = catQσ σ a2 b2 cQ2 (delAt 2 x) :=
    fun x hx0 hx2 => (hB0 x hx0).symm.trans (hB2 x hx2)
  have hF2C : ∀ x : Fin 5 → Bool, x 0 = σ → x 1 = σ →
      catQσ σ a0 b0 cQ0 (delAt 0 x) = catQσ σ a1 b1 cQ1 (delAt 1 x) :=
    fun x hx0 hx1 => (hC0 x hx0).symm.trans (hC1 x hx1)
  -- memberships in the bad lists
  have hmemA := case3_killA σ a1 b1 hab1 cP1 a2 b2 hab2 cP2 (cv 0)
    (F1P_of hslA1) (F1P_of hslA2) (F2A_of hF2A) rA
    (List.all_eq_true.mpr fun ρ _ =>
      hasLitB_of_fixable (fixable_congr hglueA hfx0) ρ)
  have hmemB := case3_killB σ a0 b0 hab0 cP0 a2 b2 hab2 cQ2 (cv 1)
    (F1P_of hslB0) (F1Q_of hslB2) (F2B_of hF2B) rB
    (List.all_eq_true.mpr fun ρ _ =>
      hasLitB_of_fixable (fixable_congr hglueB hfx1) ρ)
  have hmemC := case3_killC σ a0 b0 hab0 cQ0 a1 b1 hab1 cQ1 (cv 2)
    (F1Q_of hslC0) (F1Q_of hslC1) (F2C_of hF2C) rC
    (List.all_eq_true.mpr fun ρ _ =>
      hasLitB_of_fixable (fixable_congr hglueC hfx2) ρ)
  exact case3_compat _ hmemA _ hmemB _ hmemC
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §8 The theorem -/

/-- **k(maj₅) ≥ 4, in the kernel.** No three fixable witnesses compute
    strict majority on five bits, whatever the aggregator. -/
theorem maj5_no_three_fixable_witnesses :
    ∀ w : Fin 3 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) →
    ∀ agg : (Fin 3 → Bool) → Bool,
      (fun x => agg (fun i => w i x)) ≠ (maj : (Fin 5 → Bool) → Bool) := by
  intro w hfix agg heq
  obtain ⟨d, β, cv, hconst, hdist, huni⟩ := maj5_reduction w hfix agg heq
  by_cases hsh : ∃ i j : Fin 3, i ≠ j ∧ d i = d j
  · obtain ⟨i, j, hij, hd⟩ := hsh
    have hβ : β i ≠ β j := fun h => hdist i j hij ⟨hd, h⟩
    cases hbi : β i with
    | true =>
        have hbj : β j = false := by
          cases hbjv : β j
          · rfl
          · exact absurd (hbi.trans hbjv.symm) hβ
        exact case2_dead hfix heq hij
          (fun x hx => hconst i x (by rw [hbi]; exact hx))
          (fun x hx => hconst j x (by rw [hbj, ← hd]; exact hx))
    | false =>
        have hbj : β j = true := by
          cases hbjv : β j
          · exact absurd (hbi.trans hbjv.symm) hβ
          · rfl
        exact case2_dead hfix heq hij.symm
          (fun x hx => hconst j x (by rw [hbj]; exact hx))
          (fun x hx => hconst i x (by rw [hbi, hd]; exact hx))
  · push_neg at hsh
    obtain ⟨hu1, hu2⟩ := huni
      ⟨hsh 0 1 (by decide), hsh 0 2 (by decide), hsh 1 2 (by decide)⟩
    exact case3_dead hfix heq hconst (hsh 0 1 (by decide))
      (hsh 0 2 (by decide)) (hsh 1 2 (by decide)) hu1 hu2

/-- **k(maj₅) = 4 — THE FIRST GAP, kernel-complete.** Four fixable
    witnesses compute maj₅ and three cannot: witness complexity strictly
    exceeds certificate complexity (minCert(maj₅) = 3). Subsumes
    `maj5_witness_bracket`. -/
theorem maj5_witness_number_exact :
    (∃ w : Fin 4 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 4 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj) ∧
    (∀ w : Fin 3 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 3 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ maj) :=
  ⟨maj5_computable_by_four_fixable, maj5_no_three_fixable_witnesses⟩

end
