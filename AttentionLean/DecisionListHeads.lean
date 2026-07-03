/-
  AttentionLean.DecisionListHeads

  THE BRIDGE THEOREM, closed: Fixable = decision lists = hard-attention
  head outputs.

  `head_output_iff_fixable` — a Boolean function is the output of some
  single hard-attention head iff it is `Fixable` (equivalently, by
  `fixable_iff_dl`, iff it is a decision list). The reverse direction is
  the long-standing `headOutput_fixable`; the forward construction is
  the general decision-list → head realization
  (`dl_realizable_by_head`), generalizing the concrete maj₅ heads of
  WitnessMaj5HeadsExact.

  ROUTE.
  1. `tableHeadN` — the score/read-table head at any arity (dimension 2),
     with the argmax lemmas.
  2. Priority form: a list of (coordinate, tested value, output) entries
     plus a default, evaluated first-live-literal-wins
     (`PriorityDL.eval`). Realized by giving the k-th entry score
     `length − k` (strictly decreasing, positive) with FALL-THROUGH
     tables: unlisted and complementary literals score 0 and read the
     default. The fall-through resolution makes well-formedness
     unnecessary — duplicated or dead literals resolve identically in
     the evaluator and in the argmax (both take the first occurrence),
     so `priorityDL_realizable` holds for ALL priority lists.
  3. A raw `DL` flattens structurally to its entry list
     (`DL.toEntries`), giving `dl_realizable_by_head`.
  4. With `fixable_exists_dl`: `fixable_realizable_by_head` (dimension 2
     always suffices: `fixable_realizable_by_head₂`), and the
     characterization `head_output_iff_fixable`.
  5. Consequence: `heads_computability_iff_fixable_witnesses` — for
     ARBITRARY aggregators, k-head computability coincides with
     k-Fixable-witness computability, so every witness upper bound
     transfers to heads and every head lower bound is provable in
     witness space. CAVEAT (do not overclaim): with a thresholded
     AFFINE readout on the head side, upper bounds transfer only when
     the witness-side aggregator is itself threshold-affine — arbitrary
     aggregators are strictly more general than affine readouts.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`, no `sorry`. Purely additive.
-/
import AttentionLean.WitnessMaj5HeadsExact

open Classical

noncomputable section

/-! ## §1 The table head at any arity -/

/-- A head with prescribed score and read tables (dimension 2), at any
    arity — `tableHead` generalized from `Fin 5`. -/
def tableHeadN {n : ℕ} [NeZero n] (s r : Fin n → Bool → ℝ) :
    HardAttentionHead n 2 where
  W_Q := 1
  W_K := 1
  query := ![1, 0]
  tok := fun i b => ![s i b, r i b]
  W_V := ![0, 1]
  readout_w := 1
  readout_b := 0

lemma tableHeadN_score {n : ℕ} [NeZero n] (s r : Fin n → Bool → ℝ)
    (i : Fin n) (b : Bool) : scoreVal (tableHeadN s r) i b = s i b := by
  simp [scoreVal, tableHeadN, Matrix.one_mulVec, dotProduct,
    Fin.sum_univ_two]

lemma tableHeadN_read {n : ℕ} [NeZero n] (s r : Fin n → Bool → ℝ)
    (i : Fin n) (b : Bool) : readVal (tableHeadN s r) i b = r i b := by
  simp [readVal, tableHeadN, dotProduct, Fin.sum_univ_two]

lemma tableHeadN_output_eq {n : ℕ} [NeZero n] (s r : Fin n → Bool → ℝ)
    (x : Fin n → Bool) (i : Fin n)
    (hmax : ∀ j, s j (x j) ≤ s i (x i))
    (hmin : ∀ j, s j (x j) = s i (x i) → i ≤ j) :
    headOutput (tableHeadN s r) x
      = (if r i (x i) > 0 then true else false) := by
  have hwin : argmaxScore (attentionScore (tableHeadN s r) x) = i :=
    argmaxScore_eq_of _ i
      (fun j => by
        simp only [attentionScore_eq_scoreVal, tableHeadN_score]
        exact hmax j)
      (fun j hj => by
        simp only [attentionScore_eq_scoreVal, tableHeadN_score] at hj
        exact hmin j hj)
  simp only [headOutput, hwin, tableHeadN_read]
  norm_num [tableHeadN]

lemma tableHeadN_output_strict {n : ℕ} [NeZero n]
    (s r : Fin n → Bool → ℝ) (x : Fin n → Bool) (i : Fin n)
    (hmax : ∀ j, j ≠ i → s j (x j) < s i (x i)) :
    headOutput (tableHeadN s r) x
      = (if r i (x i) > 0 then true else false) := by
  apply tableHeadN_output_eq
  · intro j
    by_cases hji : j = i
    · rw [hji]
    · exact (hmax j hji).le
  · intro j hj
    by_cases hji : j = i
    · rw [hji]
    · exact absurd hj (ne_of_lt (hmax j hji))

/-! ## §2 Priority lists and their realization -/

/-- Priority evaluation: the first live literal's output, else the
    default. -/
def pevalList {n : ℕ} : List (Fin n × Bool × Bool) → Bool →
    (Fin n → Bool) → Bool
  | [], d, _ => d
  | e :: t, d, x => if x e.1 = e.2.1 then e.2.2 else pevalList t d x

/-- A priority decision list: entries (coordinate, tested value,
    output) plus a default. -/
structure PriorityDL (n : ℕ) where
  entries : List (Fin n × Bool × Bool)
  dflt : Bool

def PriorityDL.eval {n : ℕ} (P : PriorityDL n) (x : Fin n → Bool) :
    Bool :=
  pevalList P.entries P.dflt x

/-- Fall-through score table: the k-th entry's literal scores
    `length − k`; everything else falls through to 0. -/
def pscore {n : ℕ} : List (Fin n × Bool × Bool) → Fin n → Bool → ℝ
  | [], _, _ => 0
  | e :: t, i, b =>
      if i = e.1 ∧ b = e.2.1 then (t.length + 1 : ℝ) else pscore t i b

/-- Fall-through read table: an entry's literal reads its output;
    everything else falls through to the default. -/
def pread {n : ℕ} : List (Fin n × Bool × Bool) → Bool → Fin n → Bool → ℝ
  | [], d, _, _ => if d then 1 else -1
  | e :: t, d, i, b =>
      if i = e.1 ∧ b = e.2.1 then (if e.2.2 then 1 else -1)
      else pread t d i b

lemma pscore_nonneg {n : ℕ} (l : List (Fin n × Bool × Bool)) (i : Fin n)
    (b : Bool) : 0 ≤ pscore l i b := by
  induction l with
  | nil => exact le_refl 0
  | cons e t ih =>
      show 0 ≤ if i = e.1 ∧ b = e.2.1 then (t.length + 1 : ℝ)
        else pscore t i b
      split
      · positivity
      · exact ih

lemma pscore_le_length {n : ℕ} (l : List (Fin n × Bool × Bool))
    (i : Fin n) (b : Bool) : pscore l i b ≤ (l.length : ℝ) := by
  induction l with
  | nil => norm_num [pscore]
  | cons e t ih =>
      show (if i = e.1 ∧ b = e.2.1 then (t.length + 1 : ℝ)
        else pscore t i b) ≤ ((e :: t).length : ℝ)
      have hlen : ((e :: t).length : ℝ) = (t.length + 1 : ℝ) := by
        push_cast [List.length_cons]
        ring
      rw [hlen]
      split
      · exact le_refl _
      · calc pscore t i b ≤ (t.length : ℝ) := ih
          _ ≤ (t.length + 1 : ℝ) := by linarith

/-- If the head entry is dead on `x`, all three tables fall through. -/
lemma pscore_cons_dead {n : ℕ} (e : Fin n × Bool × Bool)
    (t : List (Fin n × Bool × Bool)) (x : Fin n → Bool)
    (hdead : ¬ x e.1 = e.2.1) (j : Fin n) :
    pscore (e :: t) j (x j) = pscore t j (x j) := by
  show (if j = e.1 ∧ x j = e.2.1 then _ else pscore t j (x j)) = _
  rw [if_neg]
  rintro ⟨rfl, hval⟩
  exact hdead hval

lemma pread_cons_dead {n : ℕ} (e : Fin n × Bool × Bool)
    (t : List (Fin n × Bool × Bool)) (d : Bool) (x : Fin n → Bool)
    (hdead : ¬ x e.1 = e.2.1) (j : Fin n) :
    pread (e :: t) d j (x j) = pread t d j (x j) := by
  show (if j = e.1 ∧ x j = e.2.1 then _ else pread t d j (x j)) = _
  rw [if_neg]
  rintro ⟨rfl, hval⟩
  exact hdead hval

/-- With no live entry, every point's score falls through to 0. -/
lemma pscore_all_dead {n : ℕ} (l : List (Fin n × Bool × Bool))
    (x : Fin n → Bool) (hdead : ∀ e ∈ l, ¬ x e.1 = e.2.1) (j : Fin n) :
    pscore l j (x j) = 0 := by
  induction l with
  | nil => rfl
  | cons e t ih =>
      rw [pscore_cons_dead e t x (hdead e (List.mem_cons_self ..)) j]
      exact ih fun e' he' => hdead e' (List.mem_cons_of_mem _ he')

lemma pread_all_dead {n : ℕ} (l : List (Fin n × Bool × Bool)) (d : Bool)
    (x : Fin n → Bool) (hdead : ∀ e ∈ l, ¬ x e.1 = e.2.1) (j : Fin n) :
    pread l d j (x j) = (if d then 1 else -1) := by
  induction l with
  | nil => rfl
  | cons e t ih =>
      rw [pread_cons_dead e t d x (hdead e (List.mem_cons_self ..)) j]
      exact ih fun e' he' => hdead e' (List.mem_cons_of_mem _ he')

lemma pevalList_all_dead {n : ℕ} (l : List (Fin n × Bool × Bool))
    (d : Bool) (x : Fin n → Bool)
    (hdead : ∀ e ∈ l, ¬ x e.1 = e.2.1) : pevalList l d x = d := by
  induction l with
  | nil => rfl
  | cons e t ih =>
      show (if x e.1 = e.2.1 then _ else pevalList t d x) = d
      rw [if_neg (hdead e (List.mem_cons_self ..))]
      exact ih fun e' he' => hdead e' (List.mem_cons_of_mem _ he')

/-- **The live-case analysis.** If some entry is live, there is a
    winning coordinate: strictly maximal positive score, whose read
    value matches the priority evaluation. -/
lemma priority_live_winner {n : ℕ} (l : List (Fin n × Bool × Bool))
    (d : Bool) (x : Fin n → Bool)
    (hlive : ∃ e ∈ l, x e.1 = e.2.1) :
    ∃ i : Fin n,
      (∀ j, j ≠ i → pscore l j (x j) < pscore l i (x i)) ∧
      ((0 : ℝ) < pread l d i (x i) ↔ pevalList l d x = true) := by
  induction l with
  | nil =>
      obtain ⟨e, he, -⟩ := hlive
      cases he
  | cons e t ih =>
      by_cases hl : x e.1 = e.2.1
      · -- the head is live: its coordinate wins with score length
        refine ⟨e.1, fun j hj => ?_, ?_⟩
        · have hj1 : pscore (e :: t) e.1 (x e.1) = (t.length + 1 : ℝ) := by
            show (if e.1 = e.1 ∧ x e.1 = e.2.1 then _ else _) = _
            rw [if_pos ⟨rfl, hl⟩]
          have hj2 : pscore (e :: t) j (x j) ≤ (t.length : ℝ) := by
            show (if j = e.1 ∧ x j = e.2.1 then (t.length + 1 : ℝ)
              else pscore t j (x j)) ≤ _
            rw [if_neg]
            · exact pscore_le_length t j (x j)
            · rintro ⟨rfl, -⟩
              exact hj rfl
          rw [hj1]
          calc pscore (e :: t) j (x j) ≤ (t.length : ℝ) := hj2
            _ < (t.length + 1 : ℝ) := by linarith
        · have hr : pread (e :: t) d e.1 (x e.1)
              = (if e.2.2 then 1 else -1) := by
            show (if e.1 = e.1 ∧ x e.1 = e.2.1 then _ else _) = _
            rw [if_pos ⟨rfl, hl⟩]
          have hev : pevalList (e :: t) d x = e.2.2 := by
            show (if x e.1 = e.2.1 then _ else _) = _
            rw [if_pos hl]
          rw [hr, hev]
          cases e.2.2 <;> norm_num
      · -- the head is dead: everything falls through to the tail
        have hlive' : ∃ e' ∈ t, x e'.1 = e'.2.1 := by
          obtain ⟨e', he', hv⟩ := hlive
          rcases List.mem_cons.mp he' with rfl | hmem
          · exact absurd hv hl
          · exact ⟨e', hmem, hv⟩
        obtain ⟨i, hstrict, hiff⟩ := ih hlive'
        refine ⟨i, fun j hj => ?_, ?_⟩
        · rw [pscore_cons_dead e t x hl j, pscore_cons_dead e t x hl i]
          exact hstrict j hj
        · rw [pread_cons_dead e t d x hl i]
          have hev : pevalList (e :: t) d x = pevalList t d x := by
            show (if x e.1 = e.2.1 then _ else _) = _
            rw [if_neg hl]
          rw [hev]
          exact hiff

/-- **Every priority list is realized by a table head** (dimension 2),
    no well-formedness needed: fall-through tables resolve duplicated
    and dead literals exactly as the evaluator does. -/
theorem priorityDL_realizable {n : ℕ} [NeZero n] (P : PriorityDL n)
    (x : Fin n → Bool) :
    headOutput (tableHeadN (pscore P.entries) (pread P.entries P.dflt))
      x = P.eval x := by
  by_cases hlive : ∃ e ∈ P.entries, x e.1 = e.2.1
  · obtain ⟨i, hstrict, hiff⟩ :=
      priority_live_winner P.entries P.dflt x hlive
    rw [tableHeadN_output_strict _ _ x i hstrict]
    show (if pread P.entries P.dflt i (x i) > 0 then true else false)
      = pevalList P.entries P.dflt x
    by_cases hpos : (0 : ℝ) < pread P.entries P.dflt i (x i)
    · rw [if_pos hpos, (hiff.mp hpos).symm]
    · rw [if_neg hpos]
      cases hev : pevalList P.entries P.dflt x
      · rfl
      · exact absurd (hiff.mpr hev) hpos
  · push_neg at hlive
    have hdead : ∀ e ∈ P.entries, ¬ x e.1 = e.2.1 := hlive
    have hmax : ∀ j, pscore P.entries j (x j)
        ≤ pscore P.entries 0 (x 0) := by
      intro j
      rw [pscore_all_dead P.entries x hdead j,
        pscore_all_dead P.entries x hdead 0]
    rw [tableHeadN_output_eq _ _ x 0 hmax (fun j _ => Fin.zero_le j)]
    show (if pread P.entries P.dflt 0 (x 0) > 0 then true else false)
      = pevalList P.entries P.dflt x
    rw [pread_all_dead P.entries P.dflt x hdead 0,
      pevalList_all_dead P.entries P.dflt x hdead]
    cases P.dflt <;> norm_num

/-! ## §3 Raw decision lists flatten to priority lists -/

/-- Flatten a `DL` into its entry list and default. -/
def DL.toEntries {n : ℕ} : DL n → List (Fin n × Bool × Bool) × Bool
  | .const b => ([], b)
  | .node i b o r => ((i, b, o) :: r.toEntries.1, r.toEntries.2)

lemma DL.eval_toEntries {n : ℕ} (r : DL n) (x : Fin n → Bool) :
    pevalList r.toEntries.1 r.toEntries.2 x = DL.eval r x := by
  induction r with
  | const b => rfl
  | node i b o r ih =>
      show (if x i = b then o else pevalList r.toEntries.1
        r.toEntries.2 x) = (if x i = b then o else DL.eval r x)
      rw [ih]

/-- **Every decision list is a hard-attention head output** (dimension
    2 suffices). Discharges S1 of the AttentionBridge scaffold in
    general. -/
theorem dl_realizable_by_head {n : ℕ} [NeZero n] (r : DL n) :
    ∃ (d : ℕ) (h : HardAttentionHead n d),
      ∀ x, headOutput h x = DL.eval r x := by
  refine ⟨2, tableHeadN (pscore r.toEntries.1)
    (pread r.toEntries.1 r.toEntries.2), fun x => ?_⟩
  calc headOutput _ x
      = (PriorityDL.mk r.toEntries.1 r.toEntries.2).eval x :=
        priorityDL_realizable ⟨r.toEntries.1, r.toEntries.2⟩ x
    _ = DL.eval r x := DL.eval_toEntries r x

/-! ## §4 The characterization -/

/-- Every fixable witness is a head output, at dimension 2. -/
theorem fixable_realizable_by_head₂ {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : Fixable f) :
    ∃ h : HardAttentionHead n 2, ∀ x, headOutput h x = f x := by
  obtain ⟨r, hr⟩ := fixable_exists_dl hf
  refine ⟨tableHeadN (pscore r.toEntries.1)
    (pread r.toEntries.1 r.toEntries.2), fun x => ?_⟩
  calc headOutput _ x
      = (PriorityDL.mk r.toEntries.1 r.toEntries.2).eval x :=
        priorityDL_realizable ⟨r.toEntries.1, r.toEntries.2⟩ x
    _ = DL.eval r x := DL.eval_toEntries r x
    _ = f x := hr x

/-- Every fixable witness is a head output. -/
theorem fixable_realizable_by_head {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : Fixable f) :
    ∃ (d : ℕ) (h : HardAttentionHead n d),
      ∀ x, headOutput h x = f x := by
  obtain ⟨h, hh⟩ := fixable_realizable_by_head₂ hf
  exact ⟨2, h, hh⟩

/-- **THE BRIDGE THEOREM.** A Boolean function is the output of a
    hard-attention head iff it is `Fixable` — equivalently (by
    `fixable_iff_dl`), iff it is a decision list. Single-head
    expressivity is EXACTLY the decision-list class. -/
theorem head_output_iff_fixable {n : ℕ} [NeZero n]
    (f : (Fin n → Bool) → Bool) :
    (∃ (d : ℕ) (h : HardAttentionHead n d),
      ∀ x, headOutput h x = f x) ↔ Fixable f := by
  constructor
  · rintro ⟨d, h, hh⟩
    exact fixable_congr hh (headOutput_fixable h)
  · exact fixable_realizable_by_head

/-! ## §5 Consequence: head computability = witness computability -/

/-- **For arbitrary aggregators, k-head computability coincides with
    k-Fixable-witness computability**: every witness-number upper bound
    transfers to heads, and every head lower bound is provable in
    witness space. (For thresholded AFFINE readouts, upper bounds
    transfer only when the witness-side aggregator is itself
    threshold-affine.) -/
theorem heads_computability_iff_fixable_witnesses {n k : ℕ} [NeZero n]
    (T : (Fin n → Bool) → Bool) :
    (∃ (d : ℕ) (h : Fin k → HardAttentionHead n d)
      (agg : (Fin k → Bool) → Bool),
      (fun x => agg (fun i => headOutput (h i) x)) = T) ↔
    (∃ ws : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (ws i)) ∧
      ∃ agg : (Fin k → Bool) → Bool,
        (fun x => agg (fun i => ws i x)) = T) := by
  constructor
  · rintro ⟨d, h, agg, hT⟩
    exact ⟨fun i => headOutput (h i),
      fun i => headOutput_fixable (h i), agg, hT⟩
  · rintro ⟨ws, hfix, agg, hT⟩
    choose h hh using fun i => fixable_realizable_by_head₂ (hfix i)
    refine ⟨2, h, agg, ?_⟩
    rw [← hT]
    funext x
    show agg (fun i => headOutput (h i) x) = agg (fun i => ws i x)
    congr 1
    funext i
    exact hh i x

end
