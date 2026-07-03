/-
# t-coordinate fixing and the bounded-window parity lower bound

Generalizes the abstraction behind `parityN_requires_N_heads` from 1-coordinate
to t-coordinate fixing, and proves the genuinely new windowed lower bound:

* `FixableK f t` — over any subcube, some ≤ t not-excluded literals on distinct
  positions pin `f` to a constant. `Fixable` is the 1-literal case
  (`fixable_fixableK`), and the budget is monotone (`fixableK_mono`).
* `collision_of_fixableK` — k functions each t-fixable cost at most k·t pinned
  coordinates; k·t below the free-coordinate count leaves a parity-flipping
  free coordinate. The existing `collision_of_fixable` is the t = 1 instance.
* `parityN_requires_window_union` — **the windowed capstone**: heads whose
  argmax provably stays inside windows `W i` cannot compute parity when the
  windows jointly miss a coordinate (`|⋃ i, W i| < n`) — with NO bound on the
  number of heads. Incomparable to `parityN_requires_N_heads`: n heads all
  windowed on position 0 are covered here (|⋃| = 1 < n) but not there (k = n).
* `parityN_requires_window_bound` — readable corollary: k heads of window ≤ t
  need k·t ≥ n. (Honesty note: this numeric form also follows from the
  existing capstone, since t ≥ 1 forces k ≤ k·t < n; it is kept only as the
  "heads × window" headline of the union bound, from which it follows in one
  line via `Finset.card_biUnion_le`.)

The window hypothesis is SEMANTIC (`∀ x, argmaxScore … ∈ W i`) — the head
model is unchanged and every existing theorem is untouched.

Axiom footprint of everything here: `[propext, Classical.choice, Quot.sound]`.
No `native_decide`.
-/

import AttentionLean.ParityN

open Finset

/-! ## t-coordinate fixing -/

/-- t-coordinate fixing: over any subcube, some ≤ t not-excluded literals on
    distinct positions pin the function to a constant. `Fixable` is the
    1-literal case. -/
def FixableK {n : ℕ} (f : (Fin n → Bool) → Bool) (t : ℕ) : Prop :=
  ∀ ρ : Fin n → Option Bool, ∃ S : List (Fin n × Bool),
    S.length ≤ t ∧
    (S.map Prod.fst).Nodup ∧
    (∀ p ∈ S, ρ p.1 ≠ some (!p.2)) ∧
    ∃ c : Bool, ∀ x : Fin n → Bool,
      memCube ρ x → (∀ p ∈ S, x p.1 = p.2) → f x = c

/-- The 1-literal abstraction embeds. (One-directional: the converse fails at
    n = 0, where `S = []` works but no literal exists.) -/
theorem fixable_fixableK {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : Fixable f) :
    FixableK f 1 := by
  intro ρ
  obtain ⟨i, b, hnd, c, hc⟩ := hf ρ
  refine ⟨[(i, b)], by simp, by simp, by simpa using hnd, c, ?_⟩
  intro x hx hS
  exact hc x hx (hS (i, b) (List.mem_singleton_self _))

/-- The fixing budget is monotone. -/
theorem fixableK_mono {n : ℕ} (f : (Fin n → Bool) → Bool) {t t' : ℕ}
    (h : t ≤ t') (hf : FixableK f t) : FixableK f t' := by
  intro ρ
  obtain ⟨S, hlen, hnd, hdead, c, hc⟩ := hf ρ
  exact ⟨S, hlen.trans h, hnd, hdead, c, hc⟩

/-- Pin a list of not-excluded literals on distinct positions: the resulting
    subcube refines the original, realizes every listed literal, and spends at
    most `S.length` free coordinates (stated additively — no subtraction). -/
theorem pin_list {n : ℕ} (S : List (Fin n × Bool)) :
    ∀ ρ : Fin n → Option Bool,
      (S.map Prod.fst).Nodup →
      (∀ p ∈ S, ρ p.1 ≠ some (!p.2)) →
      ∃ ρ' : Fin n → Option Bool,
        (∀ z : Fin n → Bool, memCube ρ' z → memCube ρ z) ∧
        (∀ z : Fin n → Bool, memCube ρ' z → ∀ p ∈ S, z p.1 = p.2) ∧
        (univ.filter fun i => ρ i = none).card
          ≤ (univ.filter fun i => ρ' i = none).card + S.length := by
  induction S with
  | nil =>
    intro ρ _ _
    exact ⟨ρ, fun _ h => h, by simp, by simp⟩
  | cons p rest ih =>
    intro ρ hnd hdead
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hp_notin, hnd_rest⟩ := hnd
    have hdead_p := hdead p (List.mem_cons_self ..)
    cases hρp : ρ p.1 with
    | some b' =>
      -- the head literal is already pinned (necessarily to p.2): no cost
      have hb : b' = p.2 := by
        rw [hρp] at hdead_p
        cases hb2 : p.2 <;> cases hb' : b' <;> simp_all
      subst hb
      obtain ⟨ρ', h1, h2, h3⟩ :=
        ih ρ hnd_rest (fun q hq => hdead q (List.mem_cons_of_mem _ hq))
      refine ⟨ρ', h1, ?_, ?_⟩
      · intro z hz q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact (h1 z hz) q.1 q.2 hρp
        · exact h2 z hz q hq'
      · simp only [List.length_cons]
        omega
    | none =>
      -- pin the head literal: one free coordinate spent
      have hdead₁ : ∀ q ∈ rest, Function.update ρ p.1 (some p.2) q.1 ≠ some (!q.2) := by
        intro q hq
        have hqi : q.1 ≠ p.1 := by
          intro hcontra
          exact hp_notin (hcontra ▸ List.mem_map_of_mem hq)
        rw [Function.update_apply, if_neg hqi]
        exact hdead q (List.mem_cons_of_mem _ hq)
      obtain ⟨ρ', h1, h2, h3⟩ := ih (Function.update ρ p.1 (some p.2)) hnd_rest hdead₁
      have hsub : ∀ z : Fin n → Bool,
          memCube (Function.update ρ p.1 (some p.2)) z → memCube ρ z := by
        intro z hz j bj hjb
        have hji : j ≠ p.1 := fun hc => by rw [hc, hρp] at hjb; cases hjb
        exact hz j bj (by rw [Function.update_apply, if_neg hji]; exact hjb)
      have hfree : (univ.filter fun i => ρ i = none).card
          ≤ (univ.filter fun i => Function.update ρ p.1 (some p.2) i = none).card + 1 := by
        have hfilter : (univ.filter fun j => Function.update ρ p.1 (some p.2) j = none)
            = (univ.filter fun j => ρ j = none).erase p.1 := by
          ext j
          by_cases hj : j = p.1
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have hmem : p.1 ∈ (univ.filter fun j => ρ j = none) :=
          mem_filter.mpr ⟨mem_univ _, hρp⟩
        rw [hfilter, card_erase_of_mem hmem]
        omega
      refine ⟨ρ', fun z hz => hsub z (h1 z hz), ?_, ?_⟩
      · intro z hz q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact (h1 z hz) q.1 q.2 (by rw [Function.update_apply, if_pos rfl])
        · exact h2 z hz q hq'
      · simp only [List.length_cons]
        omega

/-- **Generalised collision (Lemma B-K).** k functions each t-fixable admit an
    opposite-parity agreeing pair inside any subcube with more than k·t free
    coordinates: each function costs at most t pinned coordinates, and a
    leftover free coordinate flips parity. `collision_of_fixable` is the
    t = 1 instance. -/
theorem collision_of_fixableK {n t : ℕ} (fs : List ((Fin n → Bool) → Bool)) :
    (∀ f ∈ fs, FixableK f t) →
    ∀ ρ : Fin n → Option Bool,
      fs.length * t < (univ.filter fun i => ρ i = none).card →
      ∃ x y : Fin n → Bool, memCube ρ x ∧ memCube ρ y ∧
        parityN x ≠ parityN y ∧ ∀ f ∈ fs, f x = f y := by
  induction fs with
  | nil =>
    intro _ ρ hcard
    simp only [List.length_nil, Nat.zero_mul] at hcard
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hcard
    have hρi₀ : ρ i₀ = none := (Finset.mem_filter.mp hi₀).2
    refine ⟨fun j => (ρ j).getD false,
      Function.update (fun j => (ρ j).getD false) i₀ (!(ρ i₀).getD false),
      ?_, ?_, ?_, by simp⟩
    · intro i b hib; simp [hib]
    · intro i b hib
      have hne : i ≠ i₀ := fun hc => by rw [hc, hρi₀] at hib; cases hib
      rw [Function.update_apply, if_neg hne]
      simp [hib]
    · exact (parityN_update_ne _ i₀).symm
  | cons f rest ih =>
    intro hfix ρ hcard
    obtain ⟨S, hlen, hnd, hdead, c, hconst⟩ := hfix f (List.mem_cons_self ..) ρ
    obtain ⟨ρ', hsub, hpins, hfree⟩ := pin_list S ρ hnd hdead
    have hcard' : rest.length * t < (univ.filter fun i => ρ' i = none).card := by
      simp only [List.length_cons, add_one_mul] at hcard
      omega
    obtain ⟨x, y, hx, hy, hpar, hagree⟩ :=
      ih (fun g hg => hfix g (List.mem_cons_of_mem _ hg)) ρ' hcard'
    refine ⟨x, y, hsub x hx, hsub y hy, hpar, ?_⟩
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg'
    · rw [hconst x (hsub x hx) (hpins x hx), hconst y (hsub y hy) (hpins y hy)]
    · exact hagree g hg'

/-! ## `argmaxScore` access lemmas

The existing `argmaxScore_eq_of` characterisation CONSUMES max/min-index facts;
the windowed argument needs to PRODUCE them from `argmaxScore` itself. -/

/-- The argmax achieves the supremum of the scores. -/
theorem argmaxScore_score_eq_sup {n : ℕ} [NeZero n] (scores : Fin n → ℝ) :
    scores (argmaxScore scores) = univ.sup' univ_nonempty scores := by
  unfold argmaxScore
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty
  obtain ⟨i, _, hv⟩ := Finset.exists_mem_eq_sup' hne scores
  have hifilt : i ∈ univ.filter (fun j => scores j = univ.sup' hne scores) := by
    simp [hv.symm]
  have hmem := Finset.min'_mem
    (univ.filter fun j => scores j = univ.sup' hne scores) ⟨i, hifilt⟩
  exact (Finset.mem_filter.mp hmem).2

/-- Among positions achieving the argmax's score, the argmax has minimal index. -/
theorem argmaxScore_le_of_score_eq {n : ℕ} [NeZero n] (scores : Fin n → ℝ)
    (j : Fin n) (hj : scores j = scores (argmaxScore scores)) :
    argmaxScore scores ≤ j := by
  have hsup := argmaxScore_score_eq_sup scores
  unfold argmaxScore
  exact Finset.min'_le _ _ (by simp [hj.trans hsup])

/-! ## The windowed capstone -/

/-- If two inputs agree on a window containing both argmaxes, the argmaxes
    coincide: scores agree on the window, each argmax achieves the (therefore
    common) supremum, and minimality of index on each side gives antisymmetry. -/
private theorem argmax_eq_of_agree_on_window {n d : ℕ} [NeZero n]
    (head : HardAttentionHead n d) (Wi : Finset (Fin n)) (x y : Fin n → Bool)
    (hWx : argmaxScore (attentionScore head x) ∈ Wi)
    (hWy : argmaxScore (attentionScore head y) ∈ Wi)
    (hagree : ∀ j ∈ Wi, x j = y j) :
    argmaxScore (attentionScore head x) = argmaxScore (attentionScore head y) := by
  have hsc : ∀ j ∈ Wi, attentionScore head x j = attentionScore head y j := by
    intro j hj
    rw [attentionScore_eq_scoreVal, attentionScore_eq_scoreVal, hagree j hj]
  have hax := argmaxScore_score_eq_sup (attentionScore head x)
  have hay := argmaxScore_score_eq_sup (attentionScore head y)
  -- the two suprema agree
  have h1 : univ.sup' univ_nonempty (attentionScore head x)
      ≤ univ.sup' univ_nonempty (attentionScore head y) := by
    rw [← hax, hsc _ hWx]
    exact Finset.le_sup' _ (mem_univ _)
  have h2 : univ.sup' univ_nonempty (attentionScore head y)
      ≤ univ.sup' univ_nonempty (attentionScore head x) := by
    rw [← hay, ← hsc _ hWy]
    exact Finset.le_sup' _ (mem_univ _)
  have hsup_eq := le_antisymm h1 h2
  -- each argmax achieves the other's score; minimality both ways
  have h3 : argmaxScore (attentionScore head x) ≤ argmaxScore (attentionScore head y) := by
    apply argmaxScore_le_of_score_eq
    rw [hsc _ hWy, hay, ← hsup_eq, hax]
  have h4 : argmaxScore (attentionScore head y) ≤ argmaxScore (attentionScore head x) := by
    apply argmaxScore_le_of_score_eq
    rw [← hsc _ hWx, hax, hsup_eq, hay]
  exact le_antisymm h3 h4

/-- **Windowed capstone (union bound).** Heads whose argmax provably stays in
    windows `W i` cannot compute parity when the windows jointly miss a
    coordinate — with NO bound on the number of heads. Incomparable to
    `parityN_requires_N_heads` (witness: n heads all windowed on {0}). -/
theorem parityN_requires_window_union {n k d : ℕ} [NeZero n]
    (h : Fin k → HardAttentionHead n d)
    (W : Fin k → Finset (Fin n))
    (hWin : ∀ i x, argmaxScore (attentionScore (h i) x) ∈ W i)
    (hU : (univ.biUnion W).card < n)
    (w : Fin k → ℝ) (bias : ℝ) :
    ¬ (∀ x : Fin n → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = parityN x) := by
  intro hcomp
  -- a coordinate every window misses
  have hne : (univ \ univ.biUnion W).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨i₀, hi₀⟩ := hne
  have hi₀U : i₀ ∉ univ.biUnion W := (Finset.mem_sdiff.mp hi₀).2
  -- flip the missed coordinate: parity flips, no head notices
  set x : Fin n → Bool := fun _ => false with hxdef
  set y : Fin n → Bool := Function.update x i₀ (!x i₀) with hydef
  have hagree : ∀ i : Fin k, ∀ j ∈ W i, x j = y j := by
    intro i j hj
    have hne : j ≠ i₀ := fun hc =>
      hi₀U (hc ▸ Finset.mem_biUnion.mpr ⟨i, mem_univ _, hj⟩)
    rw [hydef, Function.update_apply, if_neg hne]
  have hout : ∀ i : Fin k, headOutput (h i) x = headOutput (h i) y := by
    intro i
    have hwin_eq := argmax_eq_of_agree_on_window (h i) (W i) x y
      (hWin i x) (hWin i y) (hagree i)
    simp only [headOutput]
    rw [hwin_eq, hagree i _ (hWin i y)]
  have hpar : parityN y ≠ parityN x := parityN_update_ne x i₀
  have hx := hcomp x
  have hy := hcomp y
  have hsum : (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
      = ∑ i, w i * (if headOutput (h i) y then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun i _ => by rw [hout i]
  rw [hsum] at hx
  exact hpar (hy.symm.trans hx)

/-- Headline corollary: k heads of window ≤ t require k·t ≥ n for parity.
    One line from the union capstone via `Finset.card_biUnion_le`. (This
    numeric form is ALSO derivable from `parityN_requires_N_heads` — t ≥ 1
    forces k ≤ k·t < n — and is kept only as the readable "heads × window"
    reading of the union bound.) -/
theorem parityN_requires_window_bound {n k t d : ℕ} [NeZero n] (hkt : k * t < n)
    (h : Fin k → HardAttentionHead n d)
    (W : Fin k → Finset (Fin n)) (hWcard : ∀ i, (W i).card ≤ t)
    (hWin : ∀ i x, argmaxScore (attentionScore (h i) x) ∈ W i)
    (w : Fin k → ℝ) (bias : ℝ) :
    ¬ (∀ x : Fin n → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = parityN x) := by
  apply parityN_requires_window_union h W hWin _ w bias
  calc (univ.biUnion W).card
      ≤ ∑ i, (W i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin k, t := Finset.sum_le_sum fun i _ => hWcard i
    _ = k * t := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ < n := hkt
