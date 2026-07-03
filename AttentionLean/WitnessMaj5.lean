/-
  AttentionLean.WitnessMaj5

  k(maj₅), settled: **VERDICT B — k(maj₅) = 4. The first gap.**

  STEP 0 — VERDICT (frozen after an exhaustive computational search, before
  any Lean proof; script: scripts/maj5_witness_search.py):

  * NO three fixable witnesses compute maj₅. The conjecture
    k(T) = minCert(T) FAILS at maj₅: minCert(maj₅) = 3 (three agreeing
    votes), but the witness number is 4.
  * FOUR fixable witnesses DO compute maj₅ — machine-checked below:
      w₁ = x₀ ∧ (x₁ ∨ x₃ ∨ (x₂ ∧ x₄)),   w₂ = x₀ ∧ (x₂ ∨ x₄ ∨ (x₁ ∧ x₃)),
      w₃ = ¬x₀ ∧ x₁ ∧ x₃ ∧ (x₂ ∨ x₄),    w₄ = ¬x₀ ∧ x₂ ∧ x₄ ∧ (x₁ ∨ x₃),
      maj₅ = (w₁ ∧ w₂) ∨ w₃ ∨ w₄.
    On {x₀=1} the pair (w₁,w₂) is the factorization
    T₂⁴ = (a∨c∨(b∧d)) ∧ (b∨d∨(a∧c)); on {x₀=0} the pair (w₃,w₄) is the
    dual factorization T₃⁴ = (a∧c∧(b∨d)) ∨ (b∧d∧(a∨c)); the only
    cross-half fiber merge is at label (0,0,0,0), where both thresholds
    are false. Each witness is a literal-guarded decision list, hence
    `Fixable` (kernel `decide`, 243 subcubes each).

  THE SEARCH BEHIND k ≥ 4 (why no 3-witness family exists). Necessary
  facts, all previously formalized: every fixable witness is constant on
  some half-cube (`Fixable` at the empty restriction), and restrictions of
  fixable witnesses to half-cubes are fixable on the 4-cube
  (`fixable_restrict`). Exhaustively enumerating the EXACT class:
  |Fixable(4)| = 1050 truth tables; exactly 24 ordered fixable pairs
  refine T₂⁴, and 24 refine T₃⁴. Any 3-witness family has each witness
  constant on a half-cube, giving three signed directions; up to the
  symmetry of maj₅ (coordinate permutations; self-duality kills the
  all-zeros sign) the complete case split is:
    (1) two witnesses share a signed direction — the third's restriction
        must refine a 4-bit threshold ALONE, i.e. equal ±T₂⁴/±T₃⁴; none
        of the four is fixable (verified). Dead.
    (2) two share a direction with opposite signs — both faces force
        catalog pairs (T₂⁴-pair on one, T₃⁴-pair on the other), the third
        witness is fully determined by the two faces; all
        24 × 24 × 4 assemblies fail refinement-or-fixability. Dead.
    (3) all directions distinct — the triple-overlap square forces a
        uniform sign; each face forces a catalog pair with slice-constant
        and overlap-consistency constraints; the {x₀=x₁=x₂=0} region is
        free (16³ choices). All 262,144 surviving assemblies fail. Dead.
  Positive controls: the same pipeline reproduces |Fixable(3)| = 96 (the
  priority-function count) and finds the 144 two-witness refinements of
  maj₃ (including the maj₃ construction shipped in WitnessTightness).

  HONEST STATUS. The k ≤ 4 half is fully machine-checked here. The
  k ≥ 4 half is exhaustive-search evidence (complete case analysis, tiny
  catalogs), NOT yet a Lean theorem: the natural formalization must
  quantify the pair catalogs over all 2^16 truth tables under a `Fixable`
  hypothesis, which is far past kernel-`decide` range (2^32 pairs), so it
  needs a Parity3Clean-style structural classification of Fixable(4) —
  a real project, stated as future work, not smuggled. What IS formal
  today: k ≥ 3 (`maj_needs_half_fixable_witnesses`, 2·2 < 5), so the
  machine-checked bracket is 3 ≤ k(maj₅) ≤ 4 with the exact value 4
  pinned by the search.

  CONSEQUENCES FOR THE LADDER. k(T) = minCert(T) held for parity_n (= n),
  ip2 (= m), maj₃ (= 2) — and BREAKS at maj₅: witness number is NOT
  certificate complexity; the certificate rung is a lower bound only.
  Next frontier: maj₇ — certificate rung gives k ≥ 4 (= minCert); the
  split pattern here gives k ≤ 2 + 2 = 4? No: it gives
  k(maj₇) ≤ k(T₃⁶ pairs) + k(T₄⁶ pairs) with the guard literal absorbing
  the halves, and those 6-bit threshold pair-numbers are unknown; the
  honest statement is k(maj₇) ∈ [4, 7], gap growth OPEN.

  Axioms: every declaration on `propext, Classical.choice, Quot.sound`
  or less. No `native_decide`; all finite checks are kernel `decide`.
-/
import AttentionLean.WitnessTightness

open Classical

noncomputable section

/-! ## §1 The four witnesses -/

/-- `x₀ ∧ (x₁ ∨ x₃ ∨ (x₂ ∧ x₄))` — first `T₂⁴`-factor, guarded by `x₀`. -/
def maj5W1 : (Fin 5 → Bool) → Bool :=
  fun x => x 0 && (x 1 || x 3 || (x 2 && x 4))

/-- `x₀ ∧ (x₂ ∨ x₄ ∨ (x₁ ∧ x₃))` — second `T₂⁴`-factor, guarded by `x₀`. -/
def maj5W2 : (Fin 5 → Bool) → Bool :=
  fun x => x 0 && (x 2 || x 4 || (x 1 && x 3))

/-- `¬x₀ ∧ x₁ ∧ x₃ ∧ (x₂ ∨ x₄)` — first `T₃⁴`-summand, guarded by `¬x₀`. -/
def maj5W3 : (Fin 5 → Bool) → Bool :=
  fun x => !(x 0) && (x 1 && x 3 && (x 2 || x 4))

/-- `¬x₀ ∧ x₂ ∧ x₄ ∧ (x₁ ∨ x₃)` — second `T₃⁴`-summand, guarded by `¬x₀`. -/
def maj5W4 : (Fin 5 → Bool) → Bool :=
  fun x => !(x 0) && (x 2 && x 4 && (x 1 || x 3))

set_option maxRecDepth 8192 in
theorem maj5W1_fixable : Fixable maj5W1 := by
  unfold Fixable
  decide

set_option maxRecDepth 8192 in
theorem maj5W2_fixable : Fixable maj5W2 := by
  unfold Fixable
  decide

set_option maxRecDepth 8192 in
theorem maj5W3_fixable : Fixable maj5W3 := by
  unfold Fixable
  decide

set_option maxRecDepth 8192 in
theorem maj5W4_fixable : Fixable maj5W4 := by
  unfold Fixable
  decide

/-! ## §2 The construction computes maj₅ -/

/-- **The equality, kernel `decide` over all 32 cube points** — build-gated
    non-vacuity: this is the proof it computes maj₅ itself, not something
    near it. -/
theorem maj5_eq_four_witness_combination :
    (fun x => (maj5W1 x && maj5W2 x) || maj5W3 x || maj5W4 x)
      = (maj : (Fin 5 → Bool) → Bool) := by
  decide

/-- **k(maj₅) ≤ 4**: four fixable witnesses and an aggregator compute
    strict majority on 5 bits. -/
theorem maj5_computable_by_four_fixable :
    ∃ w : Fin 4 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 4 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj := by
  refine ⟨![maj5W1, maj5W2, maj5W3, maj5W4], ?_,
    fun v => (v 0 && v 1) || v 2 || v 3, ?_⟩
  · intro i
    fin_cases i
    · exact maj5W1_fixable
    · exact maj5W2_fixable
    · exact maj5W3_fixable
    · exact maj5W4_fixable
  · exact maj5_eq_four_witness_combination

/-- The machine-checked bracket: four fixable witnesses suffice for maj₅,
    and two provably fail (certificate rung, `2·2 < 5` — hence k ≥ 3). The
    exact value k(maj₅) = 4 is pinned by the exhaustive search in
    `scripts/maj5_witness_search.py`: no three fixable witnesses work, so
    witness number strictly exceeds certificate complexity — the first
    gap. -/
theorem maj5_witness_bracket :
    (∃ w : Fin 4 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) ∧
      ∃ agg : (Fin 4 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) = maj) ∧
    (∀ w : Fin 2 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (w i)) →
      ∀ agg : (Fin 2 → Bool) → Bool,
        (fun x => agg (fun i => w i x)) ≠ maj) :=
  ⟨maj5_computable_by_four_fixable,
   fun w hfix agg => maj_needs_half_fixable_witnesses (by norm_num) w hfix agg⟩

-- Build-gated sanity: the witnesses genuinely split the cube as designed.
#guard maj5W1 (fun _ => true) == true
#guard maj5W3 (fun _ => true) == false
#guard maj5W3 (fun i => decide (i.val ≠ 0)) == true
#guard maj (fun i : Fin 5 => decide (i.val < 3)) == true
#guard maj (fun i : Fin 5 => decide (i.val < 2)) == false

end
