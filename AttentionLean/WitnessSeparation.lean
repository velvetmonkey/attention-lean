/-
  AttentionLean.WitnessSeparation

  The abstract kernel behind the parity3 antipode kill, extracted and
  instantiated twice.

  STEP 0 — THE FROZEN ABSTRACTION. Over a state type `S`, a witness-value
  type `V`, and an output type `B`, a computation-by-witnesses is a triple:

    target      T   : S → B
    witnesses   w   : Fin k → S → V     (the simple certifiers: heads,
                                         potentials, invariants)
    aggregator  agg : (Fin k → V) → B   (the readout / decision rule)

  computing `fun s => agg (fun i => w i s)`. The kernel lemma
  (`witness_separation_fails`, frozen): if every witness takes the same
  value on two states `s, s'` while the target separates them, then no
  aggregator recovers the target — the witness family FAILS on a
  distinction it cannot see. Collision ⇒ non-computation.

  STEP 0 — THE MAPPING (parity3 as an instance). In `Parity3Clean`, the
  same-inputs kill (`kill3`) — in particular the final `T`-versus-antipode
  step of the all-directions-distinct case — is exactly this kernel at
    S   := Fin 3 → Bool,   V := Bool,   B := Bool,   k := 3,
    w i := headOutput (h i),
    agg := fun v => if 0 < w₀·χ(v 0) + w₁·χ(v 1) + w₂·χ(v 2) + bias
           then true else false,
    T   := parityN,
  where the threshold hypothesis of `kill3` converts to
  `(fun s => agg (fun i => w i s)) = parityN` by `funext` and a per-point
  Bool/iff case split. The factoring is clean: `kill3`'s proof now routes
  through `witness_separation_fails` (statement untouched), and
  `parity3_indicator_heads_cannot_separate` below reconstructs the
  antipode-collision step with concrete heads, for EVERY aggregator — a
  fortiori for the thresholded affine readout.

  INSTANCE B (ordered / descent). A finite family of MONOTONE potentials
  over a preorder collides on any two order-equivalent states, so no
  decision rule over those potentials certifies a predicate separating
  them (`potential_separation_fails`). Witnessed concretely: rank-ordered
  states with a hidden flag — two states of equal rank, different flag;
  both potentials provably collide, the flag separates
  (`rank_potentials_cannot_see_flag`).

  BRIDGE NOTE (gradient-descent-lean, prose only — no dependency). A
  Lyapunov certificate for a descent process is exactly an `(S, V, agg)`
  triple in this sense: `S` the process states, the witness family the
  monotone potentials `Φ i : S → V` non-increasing along steps, and any
  convergence-certifying decision rule an aggregator over their values.
  `potential_separation_fails` is then the lower-bound principle: a
  potential family that maps two states equally can certify NO property
  distinguishing them — e.g. a single scalar Lyapunov function cannot
  certify which of two equal-energy states a trajectory ends in, and more
  witnesses are NECESSARY exactly when the target separates states inside
  a level set. That is the witness-theory spine: the minimum number of
  witnesses to separate an entangled target is a lower-bound question, and
  this kernel is its refutation half.

  Axioms: every declaration here sits on
  `propext, Classical.choice, Quot.sound` or less. No `native_decide`.
-/
import AttentionLean.ParityAchieve

open Classical

noncomputable section

/-! ## §1 The kernel -/

/-- **Witness separation fails on a collision.** If every witness takes the
    same value at `s` and `s'` while the target separates them, then no
    aggregator over the witness values computes the target. -/
theorem witness_separation_fails {S V B : Type*} {k : ℕ}
    (T : S → B) (w : Fin k → S → V) (agg : (Fin k → V) → B)
    (s s' : S) (hw : ∀ i, w i s = w i s') (hT : T s ≠ T s') :
    (fun t => agg (fun i => w i t)) ≠ T := by
  intro heq
  apply hT
  calc T s = agg (fun i => w i s) := (congrFun heq s).symm
    _ = agg (fun i => w i s') := by rw [funext hw]
    _ = T s' := congrFun heq s'

/-! ## §2 Instance A — the parity3 antipode collision, reconstructed

Three concrete indicator heads (at the three basis points, none of which is
the all-true or all-false point) collide on the all-true point and its
antipode; parity separates the pair. Hence NO aggregator over these heads'
outputs — a fortiori no thresholded affine readout — computes parity3.
`Parity3Clean.kill3` routes the in-proof kill through the same kernel. -/

/-- The `i`-th basis point of the 3-cube: true exactly at coordinate `i`. -/
def offPoint (i : Fin 3) : Fin 3 → Bool := fun j => decide (j = i)

/-- No basis point is the all-true or the all-false point. -/
theorem offPoint_misses : ∀ i : Fin 3,
    (fun _ : Fin 3 => true) ≠ offPoint i ∧
    (fun _ : Fin 3 => false) ≠ offPoint i := by decide

/-- **The collision, build-gated**: each indicator head takes the SAME value
    on the all-true point and its antipode. -/
theorem indicator_heads_collide (i : Fin 3) :
    headOutput (indicatorHead (offPoint i)) (fun _ => true)
      = headOutput (indicatorHead (offPoint i)) (fun _ => false) := by
  rw [indicatorHead_computes, indicatorHead_computes,
    if_neg (offPoint_misses i).1, if_neg (offPoint_misses i).2]

/-- **The separation, build-gated**: parity distinguishes the pair. -/
theorem parity_separates_antipodes :
    parityN (fun _ : Fin 3 => true) ≠ parityN (fun _ : Fin 3 => false) := by
  decide

/-- **INSTANCE A.** No aggregator over the three indicator heads' outputs
    computes parity3: the heads cannot see the all-true/all-false
    distinction that parity makes. Kernel lemma applied to real model
    objects (`headOutput`, `indicatorHead`, `parityN`). -/
theorem parity3_indicator_heads_cannot_separate :
    ∀ agg : (Fin 3 → Bool) → Bool,
      (fun x : Fin 3 → Bool =>
        agg (fun i => headOutput (indicatorHead (offPoint i)) x)) ≠ parityN :=
  fun agg =>
    witness_separation_fails parityN
      (fun i => headOutput (indicatorHead (offPoint i))) agg
      (fun _ => true) (fun _ => false)
      indicator_heads_collide parity_separates_antipodes

/-! ## §3 Instance B — monotone potentials cannot see inside a level set -/

/-- **Potential separation fails on order-equivalent states.** Monotone
    potentials over a preorder collide on any two order-equivalent states
    (`s ≤ s' ≤ s`), so no decision rule over the potential values certifies
    a target separating them. -/
theorem potential_separation_fails {S : Type*} [Preorder S]
    {V : Type*} [PartialOrder V] {B : Type*} {k : ℕ}
    (T : S → B) (Φ : Fin k → S → V) (hmono : ∀ i, Monotone (Φ i))
    (agg : (Fin k → V) → B)
    (s s' : S) (hle : s ≤ s') (hge : s' ≤ s) (hT : T s ≠ T s') :
    (fun t => agg (fun i => Φ i t)) ≠ T :=
  witness_separation_fails T Φ agg s s'
    (fun i => le_antisymm (hmono i hle) (hmono i hge)) hT

/-- Concrete descent-style state: an observable rank and a hidden flag,
    ordered by rank alone — a genuinely non-antisymmetric preorder. -/
structure RankState where
  rank : ℕ
  flag : Bool

instance : Preorder RankState := Preorder.lift RankState.rank

/-- Two monotone potentials over `RankState` (both functions of the rank). -/
def rankPotentials : Fin 2 → RankState → ℕ
  | 0 => fun s => s.rank
  | 1 => fun s => 2 * s.rank + 1

theorem rankPotentials_monotone : ∀ i, Monotone (rankPotentials i) := by
  intro i a b h
  have hr : a.rank ≤ b.rank := h
  fin_cases i
  · exact hr
  · simp only [rankPotentials]
    omega

/-- The two order-equivalent witness states: equal rank, different flag. -/
def sLow : RankState := ⟨0, false⟩

def sHigh : RankState := ⟨0, true⟩

-- Build-gated witness data: the potentials collide, the flag separates.
#guard rankPotentials 0 sLow == rankPotentials 0 sHigh
#guard rankPotentials 1 sLow == rankPotentials 1 sHigh
#guard sLow.flag != sHigh.flag

/-- **INSTANCE B.** No decision rule over the two monotone potentials
    computes the flag: within a level set of every potential, the flag is
    invisible. An explicit two-state separation (`sLow`, `sHigh`). -/
theorem rank_potentials_cannot_see_flag :
    ∀ agg : (Fin 2 → ℕ) → Bool,
      (fun s => agg (fun i => rankPotentials i s)) ≠ RankState.flag :=
  fun agg =>
    potential_separation_fails RankState.flag rankPotentials
      rankPotentials_monotone agg sLow sHigh
      (Nat.le.refl) (Nat.le.refl) (fun h => nomatch h)

end
