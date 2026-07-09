/-
  AttentionLean.FixableNormalForm

  R4a of the k(maj₅) ≥ 4 program: the DECISION-LIST NORMAL FORM for
  fixable witnesses, plus the concrete kill decides the catalog cascade
  opens with.

  STEP-0 SCOPE (frozen before proving — rung discipline). The remaining
  k(maj₅) ≥ 4 cases (shared-direction-opposite-signs; all-distinct-
  unanimous) need the classification of fixable pairs refining the 4-bit
  thresholds. Kernel `decide` cannot sweep the 2^16-function space, and
  even normal-form REP pairs number ~10^8 — so the catalogs must be
  derived by structural cascade lemmas built on a normal form. This
  module lands the rungs that close in this window, each final:

  R4a — CLOSED. The classification theorem `fixable_iff_dl`:
    a Boolean witness is `Fixable` iff it is computed by a DECISION LIST
    (`DL n`: a chain of literal tests with constant outputs and a
    constant default).
    * (⇐) `dl_fixable` : decision lists are fixable — pin the head
      literal if the subcube allows it, else the head is dead on the
      subcube and the tail's literal transfers.
    * (⇒) `fixable_exists_dl` : every fixable witness IS a decision
      list — the forcing literal at the empty restriction heads the
      list, and `fixable_update_restrict` (the base branch's recursion
      tool) supplies the fixable tail on one fewer relevant coordinate;
      termination by the relevant-coordinate list.
    Kernel-verified oracle control, matching the search:
    `card_fixable3` : |Fixable(3)| = 96 — the priority-function count,
    computed by `decide` over the full 256-function space of 3 bits.
    (|Fixable(4)| = 1050 is NOT reproduced in-kernel: 2^16 functions ×
    81-subcube checks is past kernel range; it remains script-verified.)

  R4b — OPENERS ONLY (the first cascade steps, each a concrete kernel
  fact the classification needs):
    * `maj3_not_fixable`, and for the 4-bit thresholds `T2of4`/`T3of4`
      (≥2-of-4, ≥3-of-4): neither `T2of4_not_pm_fixable` nor
      `T3of4_not_pm_fixable` — the threshold and its complement are both
      unfixable. These close the catalog cascade's step 1 (a refining
      pair's top literals must be positive: a negative literal would
      force the partner's restriction to be ±maj₃, and a shared face
      would force ±T alone).
    * `refines_single_pm` : a single Boolean witness refining a
      non-constant target equals the target or its complement — the
      lemma that turns "restriction refines OR₃/AND₂/…" into equations.

  OPEN LEAVES (frozen as future work, precise statements for a follow-up
  pass; NOT claimed here):
    L1 (R4b) — catalog classification: any fixable pair (P, Q) refining
        `T2of4` is one of the 24 search-catalog shapes (dually for
        `T3of4`). Route: `fixable_exists_dl` + cascade on the head
        literals (step 1 = the openers above), with per-level `decide`
        over the shrinking residual space.
    L2 (R4c) — case-2 kill: shared direction, opposite signs — both
        faces force catalog pairs, the third witness is determined, all
        24×24×4 assemblies fail (search-verified count).
    L3 (R4d) — case-3 kill: all-distinct unanimous — slice-constant and
        overlap-consistency cuts, then the region check (search count:
        262,144 assemblies, all fail).
    L4 (R4e) — `maj5_no_three_fixable_witnesses` via `maj5_reduction` +
        L2 + L3, then `maj5_witness_number_exact`.
  The open leaves above are the CATALOG route and stay future work. The
  exact result was since closed by a DIFFERENT route: k(maj₅) = 4 is now
  kernel-checked in `WitnessMaj5Exact.lean` (`maj5_witness_number_exact`)
  and `WitnessMaj5HeadsExact.lean` (`maj5_head_number_exact`), both by
  kernel `decide` with no native_decide and no sorry. So L1–L4 are an
  alternative classification path, not a blocker on the headline theorem.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`.
-/
import AttentionLean.WitnessMaj5Lower

open Classical

noncomputable section

/-! ## §1 Decision lists -/

/-- A decision list over `n` Boolean coordinates: test literals in order,
    output the matched node's constant, fall through to a default. -/
inductive DL (n : ℕ) : Type where
  | const : Bool → DL n
  | node : Fin n → Bool → Bool → DL n → DL n

/-- Evaluation: the first live literal fires. -/
def DL.eval {n : ℕ} : DL n → (Fin n → Bool) → Bool
  | .const b, _ => b
  | .node i b o r, x => if x i = b then o else DL.eval r x

/-- `Fixable` is decidable (finite subcubes, literals, and points). -/
instance {n : ℕ} (f : (Fin n → Bool) → Bool) : Decidable (Fixable f) := by
  unfold Fixable
  infer_instance

/-! ## §2 (⇐) Decision lists are fixable -/

/-- Every subcube admits a non-excluded literal (on a nonempty coordinate
    type). -/
theorem exists_legal_literal {n : ℕ} [NeZero n] (ρ : Fin n → Option Bool) :
    ∃ b : Bool, ρ 0 ≠ some (!b) := by
  cases hρ0 : ρ 0 with
  | none => exact ⟨true, by simp⟩
  | some u => exact ⟨u, by simp⟩

/-- **(⇐) Decision lists are fixable.** Pin the head literal when the
    subcube allows it; otherwise the head is dead on the subcube and the
    tail's forcing literal transfers. -/
theorem dl_fixable {n : ℕ} [NeZero n] : ∀ r : DL n, Fixable (DL.eval r) := by
  intro r
  induction r with
  | const b =>
      intro ρ
      obtain ⟨b₁, hleg⟩ := exists_legal_literal ρ
      exact ⟨0, b₁, hleg, b, fun _ _ _ => rfl⟩
  | node i b o r ih =>
      intro ρ
      by_cases hexcl : ρ i = some (!b)
      · -- the head literal is dead on this subcube: the tail decides
        obtain ⟨j, b', hexcl', c, hconst⟩ := ih ρ
        refine ⟨j, b', hexcl', c, fun x hx hxj => ?_⟩
        have hxi : x i = !b := hx i (!b) hexcl
        have hne : x i ≠ b := by
          rw [hxi]
          cases b <;> simp
        show (if x i = b then o else DL.eval r x) = c
        rw [if_neg hne]
        exact hconst x hx hxj
      · -- pin the head literal
        refine ⟨i, b, hexcl, o, fun x _ hxi => ?_⟩
        show (if x i = b then o else DL.eval r x) = o
        rw [if_pos hxi]

/-! ## §3 (⇒) Every fixable witness is a decision list -/

/-- The recursion, fueled by the list of still-relevant coordinates: a
    fixable witness depending only on `L` is a decision list. The forcing
    literal at the empty restriction heads the list; if its coordinate is
    relevant, `fixable_update_restrict` supplies the fixable tail on one
    fewer relevant coordinate; if not, the witness is constant. -/
theorem fixable_exists_dl_aux {n : ℕ} [NeZero n] :
    ∀ (k : ℕ) (L : List (Fin n)) (f : (Fin n → Bool) → Bool),
      L.length ≤ k → Fixable f →
      (∀ x y : Fin n → Bool, (∀ j ∈ L, x j = y j) → f x = f y) →
      ∃ r : DL n, ∀ x, DL.eval r x = f x := by
  intro k
  induction k with
  | zero =>
      intro L f hL hf hdep
      obtain ⟨i, b, c, hc⟩ := fixable_const_halfcube hf
      have hLnil : L = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hL)
      refine ⟨.const c, fun x => ?_⟩
      show c = f x
      have hagree : ∀ j ∈ L, (Function.update x i b) j = x j := by
        intro j hj
        rw [hLnil] at hj
        cases hj
      calc c = f (Function.update x i b) :=
            (hc _ (Function.update_self i b x)).symm
        _ = f x := hdep _ _ hagree
  | succ k ih =>
      intro L f hL hf hdep
      obtain ⟨i, b, c, hc⟩ := fixable_const_halfcube hf
      by_cases hi : i ∈ L
      · -- recurse on the tail with `i` pinned away
        have hf' : Fixable (fun y => f (Function.update y i (!b))) :=
          fixable_update_restrict hf i (!b)
        have hlen : (L.erase i).length ≤ k := by
          have := List.length_erase_of_mem hi
          omega
        have hdep' : ∀ x y : Fin n → Bool,
            (∀ j ∈ L.erase i, x j = y j) →
            f (Function.update x i (!b)) = f (Function.update y i (!b)) := by
          intro x y hagree
          apply hdep
          intro j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hji, Function.update_of_ne hji]
            exact hagree j (List.mem_erase_of_ne hji |>.mpr hj)
        obtain ⟨r', hr'⟩ := ih (L.erase i) _ hlen hf' hdep'
        refine ⟨.node i b c r', fun x => ?_⟩
        show (if x i = b then c else DL.eval r' x) = f x
        by_cases hxi : x i = b
        · rw [if_pos hxi]
          exact (hc x hxi).symm
        · rw [if_neg hxi]
          have hxi' : x i = !b := by
            cases hb : x i <;> cases b <;> simp_all
          calc DL.eval r' x = f (Function.update x i (!b)) := hr' x
            _ = f x := by rw [← hxi', Function.update_eq_self]
      · -- the forcing coordinate is irrelevant: the witness is constant
        refine ⟨.const c, fun x => ?_⟩
        show c = f x
        have hagree : ∀ j ∈ L, (Function.update x i b) j = x j := by
          intro j hj
          have hji : j ≠ i := fun h => hi (by rw [← h]; exact hj)
          rw [Function.update_of_ne hji]
        calc c = f (Function.update x i b) :=
              (hc _ (Function.update_self i b x)).symm
          _ = f x := hdep _ _ hagree

/-- **(⇒) Every fixable witness is a decision list.** -/
theorem fixable_exists_dl {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : Fixable f) :
    ∃ r : DL n, ∀ x, DL.eval r x = f x := by
  refine fixable_exists_dl_aux (List.finRange n).length (List.finRange n) f
    le_rfl hf ?_
  intro x y hagree
  have hxy : x = y := funext fun j => hagree j (List.mem_finRange j)
  rw [hxy]

/-- **R4a — THE NORMAL FORM.** A Boolean witness is fixable iff it is
    computed by a decision list. -/
theorem fixable_iff_dl {n : ℕ} [NeZero n] (f : (Fin n → Bool) → Bool) :
    Fixable f ↔ ∃ r : DL n, ∀ x, DL.eval r x = f x := by
  constructor
  · exact fixable_exists_dl
  · rintro ⟨r, hr⟩
    have hfr : f = DL.eval r := funext fun x => (hr x).symm
    rw [hfr]
    exact dl_fixable r

/-- Non-vacuity for (⇒) on a shipped witness: the maj₃ construction's
    first witness has a decision list. -/
theorem majW1_has_dl : ∃ r : DL 3, ∀ x, DL.eval r x = majW1 x :=
  fixable_exists_dl majW1_fixable

-- Non-vacuity for (⇐): a concrete decision list evaluates as expected.
#guard DL.eval (.node 0 true true (.const false)) (fun _ : Fin 3 => true) == true
#guard DL.eval (.node 0 true true (.const false)) (fun _ : Fin 3 => false) == false

/-! ## §4 Oracle control, in-kernel -/

set_option maxRecDepth 16384 in
/-- **|Fixable(3)| = 96** — the priority-function count, kernel-verified
    over the full 256-function space; matches the search's positive
    control. -/
theorem card_fixable3 :
    ((Finset.univ : Finset ((Fin 3 → Bool) → Bool)).filter
      fun f => Fixable f).card = 96 := by
  decide

/-! ## §5 R4b openers: the concrete cascade kills -/

/-- The ≥2-of-4 threshold. -/
def T2of4 (y : Fin 4 → Bool) : Bool :=
  decide (2 ≤ (Finset.univ.filter fun i => y i = true).card)

/-- The ≥3-of-4 threshold. -/
def T3of4 (y : Fin 4 → Bool) : Bool :=
  decide (3 ≤ (Finset.univ.filter fun i => y i = true).card)

/-- Majority on 3 bits is not fixable — with `maj3_not_fixable'` for its
    complement: catalog step 1 (a negative top literal is dead). -/
theorem maj3_not_fixable : ¬ Fixable (maj : (Fin 3 → Bool) → Bool) := by
  decide

theorem maj3_not_fixable' :
    ¬ Fixable (fun x => !(maj (n := 3) x)) := by
  decide

/-- Neither the ≥2-of-4 threshold nor its complement is fixable —
    the case-1-style shared-face kill for the 4-bit catalogs. -/
theorem T2of4_not_pm_fixable :
    ¬ Fixable T2of4 ∧ ¬ Fixable (fun y => !(T2of4 y)) := by
  constructor <;> decide

/-- Neither the ≥3-of-4 threshold nor its complement is fixable. -/
theorem T3of4_not_pm_fixable :
    ¬ Fixable T3of4 ∧ ¬ Fixable (fun y => !(T3of4 y)) := by
  constructor <;> decide

/-- **Single-witness refinement is equality up to complement.** If `g`'s
    fibres refine a non-constant `f`, then `g = f` or `g = ¬f`
    pointwise — the lemma that turns "the restriction refines OR₃" into
    an equation in the catalog cascade. -/
theorem refines_single_pm {α : Type*} (f g : α → Bool)
    (h : ∀ x y, g x = g y → f x = f y)
    (x₀ y₀ : α) (hne : f x₀ ≠ f y₀) :
    (∀ x, g x = f x) ∨ (∀ x, g x = !(f x)) := by
  have hgne : g x₀ ≠ g y₀ := fun he => hne (h _ _ he)
  by_cases hfg : g x₀ = f x₀
  · left
    intro z
    by_cases hz : g z = g x₀
    · rw [hz, hfg, h z x₀ hz]
    · have hzy : g z = g y₀ := by
        cases hb : g z <;> cases hb₀ : g x₀ <;> cases hb₁ : g y₀ <;> simp_all
      rw [hzy, h z y₀ hzy]
      cases hb₀ : f x₀ <;> cases hb₁ : f y₀ <;> cases hb₂ : g y₀ <;> simp_all
  · right
    intro z
    by_cases hz : g z = g x₀
    · rw [hz, h z x₀ hz]
      cases hb₀ : f x₀ <;> cases hb₂ : g x₀ <;> simp_all
    · have hzy : g z = g y₀ := by
        cases hb : g z <;> cases hb₀ : g x₀ <;> cases hb₁ : g y₀ <;> simp_all
      rw [hzy, h z y₀ hzy]
      cases hb₀ : f x₀ <;> cases hb₁ : f y₀ <;> cases hb₂ : g y₀ <;>
        cases hb₃ : g x₀ <;> simp_all

end
