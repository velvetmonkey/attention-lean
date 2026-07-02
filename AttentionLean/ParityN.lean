/-
# General parity lower bound: fewer than n heads cannot compute parity on n bits

`parityN_requires_N_heads`: for every n and every k < n, no k hard-attention
heads combined through a thresholded affine readout compute parity on n bits.
This generalizes the enumerated case results `parity3_requires_three_heads`
and `parity4_requires_four_heads` to all n, replacing `native_decide`
enumeration of achievable head behaviors with a structural argument.

The proof is NOT a counting/pigeonhole argument on head-output tuples — k
arbitrary Boolean functions with k = n-1 CAN compute parity through a
thresholded affine readout (unary-count encoding). The bound depends
essentially on hard-attention structure:

* **Fixing lemma** (`headOutput_fixable`): a head's attention score at
  position i depends only on (i, x i), so over any subcube (partial
  assignment) the key-minimal (max score, then min index) not-yet-excluded
  literal (i, b) pins the argmax: fixing x i = b makes the head CONSTANT on
  the restricted subcube. This is where argmax instability — the obstacle to
  naive "flip a non-winning position" arguments à la `headOutput_stable` —
  is controlled.
* **Collision lemma** (`collision_of_fixable`, then `collision_exists_n`):
  by induction, k such functions cost at most k fixed coordinates; k < n
  leaves a free coordinate whose flip toggles parity inside a subcube where
  every head is constant, producing two inputs of opposite parity that no
  head distinguishes.
* **Capstone**: an affine readout is constant on equal head outputs, so it
  cannot equal parity on both inputs of the collision pair.

Unlike the fixed-n case theorems, this chain uses no `native_decide`; its
axiom footprint is `[propext, Classical.choice, Quot.sound]`.
-/

import AttentionLean.Defs

open Finset

/-! ## General parity -/

/-- Parity of an n-bit vector: true iff an odd number of bits are set. -/
def parityN {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => x i).card % 2 = 1)

-- Compatibility with the hardcoded `parity3`/`parity4` lives in
-- `AttentionLean.ParityNCompat`: those definitions sit in `ParitySmall`,
-- whose import chain pulls the heavy `native_decide` enumeration modules.
-- This file deliberately depends on `Defs` alone.

/-- Flipping one bit flips parity. -/
theorem parityN_update_ne {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    parityN (Function.update x i (!x i)) ≠ parityN x := by
  cases hxi : x i with
  | false =>
    have hset : (univ.filter fun j => Function.update x i true j = true)
        = insert i (univ.filter fun j => x j = true) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [Function.update_apply]
      · simp [Function.update_apply, hj]
    have hnotmem : i ∉ (univ.filter fun j => x j = true) := by simp [hxi]
    simp only [parityN, ne_eq, decide_eq_decide, Bool.not_false, hset,
      Finset.card_insert_of_notMem hnotmem]
    omega
  | true =>
    have hset : (univ.filter fun j => Function.update x i false j = true)
        = (univ.filter fun j => x j = true).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [Function.update_apply]
      · simp [Function.update_apply, hj]
    have hmem : i ∈ (univ.filter fun j => x j = true) := by simp [hxi]
    have hpos : 0 < (univ.filter fun j => x j = true).card := card_pos.mpr ⟨i, hmem⟩
    simp only [parityN, ne_eq, decide_eq_decide, Bool.not_true, hset,
      card_erase_of_mem hmem]
    omega

/-! ## Subcubes and the fixing property -/

/-- Membership in the subcube described by a partial assignment: `x`
    matches every pinned coordinate. -/
def memCube {n : ℕ} (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin n, ∀ b : Bool, ρ i = some b → x i = b

/-- The fixing property: on any subcube, the function becomes constant after
    pinning at most one additional coordinate. The witness literal `(i, b)`
    is never excluded by the subcube (`ρ i ≠ some (!b)`), so pinning it
    keeps the subcube nonempty and spends at most one free coordinate. -/
def Fixable {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ ρ : Fin n → Option Bool, ∃ (i : Fin n) (b : Bool), ρ i ≠ some (!b) ∧
    ∃ c : Bool, ∀ x : Fin n → Bool, memCube ρ x → x i = b → f x = c

/-! ## Lemma A: hard-attention heads are fixable -/

/-- Characterization of `argmaxScore`: a position achieving the maximum
    score and minimal among positions achieving its score is the argmax. -/
theorem argmaxScore_eq_of {n : ℕ} [NeZero n] (scores : Fin n → ℝ) (i : Fin n)
    (hmax : ∀ j, scores j ≤ scores i)
    (hmin : ∀ j, scores j = scores i → i ≤ j) :
    argmaxScore scores = i := by
  unfold argmaxScore
  have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty
  have hM : univ.sup' hne scores = scores i :=
    le_antisymm (Finset.sup'_le _ _ fun j _ => hmax j) (Finset.le_sup' _ (mem_univ i))
  have hifilt : i ∈ univ.filter (fun j => scores j = univ.sup' hne scores) := by
    simp [hM]
  have hfne : (univ.filter (fun j => scores j = univ.sup' hne scores)).Nonempty := ⟨i, hifilt⟩
  apply le_antisymm
  · exact Finset.min'_le _ _ hifilt
  · have hmem := Finset.min'_mem _ hfne
    have hval : scores (Finset.min' _ hfne) = scores i := by
      have := (Finset.mem_filter.mp hmem).2
      rw [this, hM]
    exact hmin _ hval

/-- **Lemma A.** Every hard-attention head output is fixable: over any
    subcube, the not-excluded literal with (max score, then min index) pins
    the argmax, so fixing it makes the head constant. -/
theorem headOutput_fixable {n d : ℕ} [NeZero n] (head : HardAttentionHead n d) :
    Fixable (headOutput head) := by
  intro ρ
  -- the not-excluded ("not dead") literals
  set s : Finset (Fin n × Bool) := univ.filter (fun p => ρ p.1 ≠ some (!p.2)) with hs
  have hsne : s.Nonempty := by
    cases hρ : ρ (0 : Fin n) with
    | none => exact ⟨((0 : Fin n), true), by simp [hs, hρ]⟩
    | some c => exact ⟨((0 : Fin n), c), by simp [hs, hρ]⟩
  -- maximal score over not-dead literals
  set M : ℝ := s.sup' hsne (fun p => scoreVal head p.1 p.2) with hM
  -- achievers, minimal index among them
  set A : Finset (Fin n × Bool) := s.filter (fun p => scoreVal head p.1 p.2 = M) with hAdef
  have hAne : A.Nonempty := by
    obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_sup' hsne (fun p => scoreVal head p.1 p.2)
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpv.symm.trans hM.symm⟩⟩
  set I : Finset (Fin n) := A.image Prod.fst with hI
  have hIne : I.Nonempty := hAne.image _
  obtain ⟨p, hpA, hpfst⟩ := Finset.mem_image.mp (I.min'_mem hIne)
  -- p.1 is the minimal index among the maximal-score not-dead literals
  have hpair : (p.1, p.2) ∈ A := hpA
  refine ⟨p.1, p.2, ?_, ?_⟩
  · -- the chosen literal is not dead
    have hmem : (p.1, p.2) ∈ s := (Finset.filter_subset _ _) hpair
    simpa [hs] using hmem
  · refine ⟨if head.readout_w * readVal head p.1 p.2 + head.readout_b > 0 then true
      else false, ?_⟩
    intro x hxcube hxi
    -- live literals of x are not dead
    have hlive : ∀ j : Fin n, (j, x j) ∈ s := by
      intro j
      simp only [hs, mem_filter, mem_univ, true_and]
      intro hcontra
      have := hxcube j (!(x j)) hcontra
      simp at this
    have hstar_val : attentionScore head x p.1 = M := by
      rw [attentionScore_eq_scoreVal, hxi]
      exact (Finset.mem_filter.mp hpair).2
    -- the argmax is pinned at p.1
    have hwin : argmaxScore (attentionScore head x) = p.1 := by
      apply argmaxScore_eq_of
      · intro j
        rw [hstar_val, attentionScore_eq_scoreVal]
        exact Finset.le_sup' (fun p : Fin n × Bool => scoreVal head p.1 p.2) (hlive j)
      · intro j hj
        rw [hstar_val] at hj
        have hjA : (j, x j) ∈ A := by
          simp only [hAdef, mem_filter]
          refine ⟨hlive j, ?_⟩
          rw [← attentionScore_eq_scoreVal, hj]
        rw [hpfst]
        exact I.min'_le j (Finset.mem_image.mpr ⟨(j, x j), hjA, rfl⟩)
    simp only [headOutput]
    rw [hwin, hxi]

/-! ## Lemma B: collision by subcube induction -/

/-- **Lemma B.** Any list of fixable functions shorter than the number of
    free coordinates of a subcube admits an opposite-parity pair inside the
    subcube on which all the functions agree: each function costs at most
    one pinned coordinate, and a leftover free coordinate flips parity. -/
theorem collision_of_fixable {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) :
    (∀ f ∈ fs, Fixable f) →
    ∀ ρ : Fin n → Option Bool,
      fs.length < (univ.filter fun i => ρ i = none).card →
      ∃ x y : Fin n → Bool, memCube ρ x ∧ memCube ρ y ∧
        parityN x ≠ parityN y ∧ ∀ f ∈ fs, f x = f y := by
  induction fs with
  | nil =>
    intro _ ρ hcard
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hcard
    have hρi₀ : ρ i₀ = none := (Finset.mem_filter.mp hi₀).2
    refine ⟨fun j => (ρ j).getD false,
      Function.update (fun j => (ρ j).getD false) i₀ (!(ρ i₀).getD false),
      ?_, ?_, ?_, by simp⟩
    · intro i b hib; simp [hib]
    · intro i b hib
      have hne : i ≠ i₀ := fun h => by rw [h, hρi₀] at hib; cases hib
      rw [Function.update_apply, if_neg hne]
      simp [hib]
    · exact (parityN_update_ne _ i₀).symm
  | cons f rest ih =>
    intro hfix ρ hcard
    obtain ⟨i, b, hnd, c, hconst⟩ := hfix f (List.mem_cons_self ..) ρ
    have hfixrest : ∀ g ∈ rest, Fixable g := fun g hg =>
      hfix g (List.mem_cons_of_mem _ hg)
    cases hρi : ρ i with
    | some b' =>
      -- the literal is already pinned (necessarily to b): f is constant on ρ
      have hb : b' = b := by
        rw [hρi] at hnd
        cases b <;> cases b' <;> simp_all
      subst hb
      have hcard' : rest.length < (univ.filter fun j => ρ j = none).card := by
        simp only [List.length_cons] at hcard; omega
      obtain ⟨x, y, hxc, hyc, hpar, hagree⟩ := ih hfixrest ρ hcard'
      refine ⟨x, y, hxc, hyc, hpar, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with hgf | hgrest
      · subst hgf
        rw [hconst x hxc (hxc i b' hρi), hconst y hyc (hyc i b' hρi)]
      · exact hagree g hgrest
    | none =>
      -- pin the literal: f becomes constant, one free coordinate spent
      set ρ' : Fin n → Option Bool := Function.update ρ i (some b) with hρ'
      have hρ'i : ρ' i = some b := by simp [hρ']
      have hfilter : (univ.filter fun j => ρ' j = none)
          = (univ.filter fun j => ρ j = none).erase i := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [hρ']
        · simp [hρ', Function.update_apply, hj]
      have hcard' : rest.length < (univ.filter fun j => ρ' j = none).card := by
        rw [hfilter, card_erase_of_mem (mem_filter.mpr ⟨mem_univ i, hρi⟩)]
        simp only [List.length_cons] at hcard
        omega
      obtain ⟨x, y, hxc, hyc, hpar, hagree⟩ := ih hfixrest ρ' hcard'
      have hsub : ∀ z : Fin n → Bool, memCube ρ' z → memCube ρ z := by
        intro z hz j bj hjb
        have hne : j ≠ i := fun h => by rw [h, hρi] at hjb; cases hjb
        exact hz j bj (by rw [hρ', Function.update_apply, if_neg hne]; exact hjb)
      refine ⟨x, y, hsub x hxc, hsub y hyc, hpar, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with hgf | hgrest
      · subst hgf
        rw [hconst x (hsub x hxc) (hxc i b hρ'i), hconst y (hsub y hyc) (hyc i b hρ'i)]
      · exact hagree g hgrest

/-! ## The general collision lemma and the capstone -/

/-- **General collision lemma.** For any k < n hard-attention heads on n-bit
    inputs there exist two inputs of opposite parity on which every head
    produces the same output. Replaces the enumerated `collision_exists_3` /
    `collision_exists_4` at arbitrary n, with no `native_decide`. -/
theorem collision_exists_n {n k d : ℕ} [NeZero n] (hk : k < n)
    (h : Fin k → HardAttentionHead n d) :
    ∃ x y : Fin n → Bool,
      parityN x ≠ parityN y ∧ ∀ i : Fin k, headOutput (h i) x = headOutput (h i) y := by
  have hall : ∀ f ∈ (List.ofFn fun i => headOutput (h i)), Fixable f := by
    intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn ..).mp hf
    exact headOutput_fixable (h i)
  have hcard : (List.ofFn fun i => headOutput (h i)).length
      < (univ.filter fun i : Fin n => (fun _ : Fin n => (none : Option Bool)) i = none).card := by
    simpa using hk
  obtain ⟨x, y, _, _, hpar, hagree⟩ :=
    collision_of_fixable _ hall (fun _ => none) hcard
  exact ⟨x, y, hpar, fun i => hagree _ ((List.mem_ofFn ..).mpr ⟨i, rfl⟩)⟩

/-- **Capstone: parity on n bits requires n heads.** For every n, no k < n
    hard-attention heads combined through a thresholded affine readout
    compute `parityN`. Generalizes `parity3_requires_three_heads` and
    `parity4_requires_four_heads` (the k = n − 1 instances at n = 3, 4). -/
theorem parityN_requires_N_heads {n k d : ℕ} [NeZero n] (hk : k < n)
    (h : Fin k → HardAttentionHead n d) (w : Fin k → ℝ) (bias : ℝ) :
    ¬ (∀ x : Fin n → Bool,
      (if (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0)) + bias > 0
       then true else false) = parityN x) := by
  intro hcomp
  obtain ⟨x, y, hpar, hagree⟩ := collision_exists_n hk h
  have hx := hcomp x
  have hy := hcomp y
  have hsum : (∑ i, w i * (if headOutput (h i) x then (1 : ℝ) else 0))
      = ∑ i, w i * (if headOutput (h i) y then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun i _ => by rw [hagree i]
  rw [hsum] at hx
  exact hpar (hx.symm.trans hy)
