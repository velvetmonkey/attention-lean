/-
  AttentionLean.AttentionBridge          ⚠ WIP MODULE — NOT IN THE CLEAN GATE ⚠

  THE ATTENTION-EXPRESSIVITY BRIDGE: witness complexity ⇒ attention head
  counts. This module is a STATEMENT SCAFFOLD: all definitions compile
  clean; theorem statements that are not yet closed carry exactly one
  documented `sorry` each and form the Aristotle work-queue below. This
  module is deliberately NOT imported by `AttentionLean/Axioms.lean` and
  has NO axiom pins — the clean corpus stays zero-sorry.

  ────────────────────────────────────────────────────────────────────
  THEOREM MAP

  Already PROVED on main (clean tier, pinned in the gate):
  * `headOutput_fixable` (ParityN.lean)      — a hard-attention head's
    output is a Fixable witness. THE LINCHPIN; already closed.
  * `parityN_requires_N_heads` (ParityN.lean) — parity_n needs n heads.
  * Witness ladder: k(parity_n) = n, k(ip2 on 2m bits) = m, k(maj₃) = 2
    (WitnessTheory/Embedding/Majority/Tightness); maj₅ bracket
    3 ≤ k(maj₅) ≤ 4 + structural reduction (WitnessMaj5/Lower);
    Fixable = decision lists (FixableNormalForm); the L1 threshold
    catalogs, |R2| = |R3| = 24 (ThresholdCatalog).

  PROVED CLEAN IN THIS MODULE (new; may be promoted + pinned on merge):
  * `attnComputes_to_fixable_witnesses` — k heads + thresholded affine
    readout computing T yield k Fixable witnesses + an aggregator
    computing T. THE TRANSFER: head count ≥ witness number k(T).
  * `no_attn_of_witness_lower_bound` — contrapositive wrapper: every
    ladder lower bound becomes a head lower bound.
  * `maj_attention_lower_bound` — 2k < n ⇒ k heads cannot compute maj_n.
  * `maj3_requires_two_heads` — one head cannot compute maj₃.
  * `maj5_requires_three_heads` — two heads cannot compute maj₅.
  * `ip2_attention_lower_bound` — k < m ⇒ k heads cannot compute ip2.
  * `parityN_attention_lower_bound` — the existing parity capstone,
    restated through `AttnComputes` (definitional).
  * `headRealizable_fixable` — head-realizable ⇒ Fixable (converse
    direction of the class equality, easy half).
  * `maj5_has_size3_certificate` — maj₅ has a certificate of size 3
    (the decided half of the headline gap).

  SORRIED (Aristotle work-queue, one `sorry` per line item):
  * S1 `dl_realizable_as_head` — every decision list is the output
    function of a single hard-attention head (score gadget: strictly
    decreasing scores down the list, matched read values; d = 2
    suffices). Difficulty: MEDIUM. This is the converse linchpin: with
    `fixable_exists_dl` it makes head-realizable = Fixable EXACTLY
    (`fixable_headRealizable` is already derived from it below, clean).
  * S2 `maj5_no_three_fixable_witnesses` — no 3 Fixable witnesses + any
    aggregator compute maj₅. THE OPEN BOOLEAN GAP (= L2+L3+L4 of the
    k(maj₅) program; consume `maj5_reduction` + the L1 catalogs
    `T2_refining_pair_classified`/`T3_refining_pair_classified`).
    Difficulty: HARD. Currently search-pinned
    (scripts/maj5_witness_search.py, exhaustive, positive-controlled).
  * S3 `maj5_computable_by_four_heads` — 4 heads + affine readout
    compute maj₅ (route: the four shipped witnesses maj5W1..W4 are
    decision lists → S1 heads; aggregator (v₀∧v₁)∨v₂∨v₃ is the LTF
    v₀+v₁+2v₂+2v₃ > 3/2… any separating weights work). Difficulty:
    MEDIUM (mechanical once S1 lands).

  DERIVED FROM THE QUEUE (already written below; inherit `sorry` taint
  until their inputs close — no new work needed):
  * `fixable_headRealizable` (from S1) — Fixable ⇒ head-realizable.
  * `maj5_requires_four_heads` (from S2) — 3 heads cannot compute maj₅.
  * `maj5_attention_certificate_gap` (from S2) — THE HEADLINE.

  ────────────────────────────────────────────────────────────────────
  PAPER SKELETON — "Attention lower bounds via witness complexity"

  1. Model: single-layer hard attention (unique-argmax with min-index
     tie-break), Boolean inputs, per-head Boolean output, thresholded
     affine readout over head outputs (`AttnComputes`).
  2. The witness class: `Fixable` — value on any subcube forced by one
     literal. Heads ARE fixable witnesses (`headOutput_fixable`);
     conversely every fixable function is a head (S1; = decision lists
     by `fixable_iff_dl`). So head expressivity per-head is EXACTLY the
     decision-list class, and the minimal head count for T equals the
     witness number k(T) up to readout shape.
  3. Lower-bound engine: any readout is an aggregator, so
     k_heads(T) ≥ k(T) (the transfer, this module). The ladder then
     gives: parity_n needs n heads (tight: 2^(n−1) upper known),
     ip2 needs m heads, maj_n needs > n/2 heads.
  4. FLAGSHIP: k(maj₅) = 4 > 3 = certificate complexity of maj₅ —
     attention head count is NOT certificate complexity; the certificate
     measure (used for all prior ladder bounds) is a strict lower bound.
     Formally: `maj5_attention_certificate_gap` = (size-3 certificate
     exists) ∧ (no 3 heads compute maj₅). Boolean side search-verified,
     kernel formalization = S2 (catalogs already kernel-classified).
  5. Discussion: certificate rung vs witness number; the first gap;
     maj₇ ∈ [4, 7] open; multi-layer / soft-attention out of scope
     (soft-attention = flagged tarpit).
  ────────────────────────────────────────────────────────────────────
-/
import AttentionLean.ThresholdCatalog

open Classical Finset

noncomputable section

/-! ## §1 Definitions (all compile clean) -/

/-- Thresholded affine readout over `k` Boolean head outputs — the exact
    readout shape of `parityN_requires_N_heads`. -/
def attnReadout {k : ℕ} (w : Fin k → ℝ) (bias : ℝ) (v : Fin k → Bool) :
    Bool :=
  if (∑ i, w i * (if v i then (1 : ℝ) else 0)) + bias > 0 then true
  else false

/-- `k` hard-attention heads plus a thresholded affine readout compute
    the target `T`. -/
def AttnComputes {n d k : ℕ} [NeZero n] (h : Fin k → HardAttentionHead n d)
    (w : Fin k → ℝ) (bias : ℝ) (T : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, attnReadout w bias (fun i => headOutput (h i) x) = T x

/-- `f` is the output function of a single hard-attention head (any
    internal dimension). -/
def HeadRealizable {n : ℕ} [NeZero n] (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (d : ℕ) (head : HardAttentionHead n d), ∀ x, headOutput head x = f x

instance {m : ℕ} [NeZero m] : NeZero (2 * m) :=
  ⟨fun h => NeZero.ne m (by omega)⟩

/-! ## §2 The transfer: head count ≥ witness number (PROVED) -/

/-- **THE TRANSFER.** Heads computing `T` through a thresholded affine
    readout yield Fixable witnesses computing `T` through an aggregator:
    the witnesses are the head outputs (`headOutput_fixable`), the
    aggregator is the readout. Hence every witness-number lower bound is
    an attention-head lower bound. -/
theorem attnComputes_to_fixable_witnesses {n d k : ℕ} [NeZero n]
    {h : Fin k → HardAttentionHead n d} {w : Fin k → ℝ} {bias : ℝ}
    {T : (Fin n → Bool) → Bool} (hc : AttnComputes h w bias T) :
    ∃ ws : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (ws i)) ∧
      ∃ agg : (Fin k → Bool) → Bool,
        (fun x => agg (fun i => ws i x)) = T :=
  ⟨fun i => headOutput (h i), fun i => headOutput_fixable (h i),
    attnReadout w bias, funext hc⟩

/-- Contrapositive wrapper: a witness-number lower bound for `T` kills
    every `k`-head attention implementation of `T`. -/
theorem no_attn_of_witness_lower_bound {n d k : ℕ} [NeZero n]
    {T : (Fin n → Bool) → Bool}
    (hlb : ∀ ws : Fin k → (Fin n → Bool) → Bool, (∀ i, Fixable (ws i)) →
      ∀ agg : (Fin k → Bool) → Bool,
        (fun x => agg (fun i => ws i x)) ≠ T)
    (h : Fin k → HardAttentionHead n d) (w : Fin k → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias T := by
  intro hc
  obtain ⟨ws, hfix, agg, hagg⟩ := attnComputes_to_fixable_witnesses hc
  exact hlb ws hfix agg hagg

/-- Head-realizable functions are Fixable — the easy half of the class
    equality (the hard half is S1 in the queue). -/
theorem headRealizable_fixable {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : HeadRealizable f) : Fixable f := by
  obtain ⟨d, head, hh⟩ := hf
  exact fixable_congr hh (headOutput_fixable head)

/-! ## §3 The ladder, transferred (PROVED) -/

/-- Majority on `n` bits needs more than `n/2` heads. -/
theorem maj_attention_lower_bound {n k d : ℕ} [NeZero n] (hk : 2 * k < n)
    (h : Fin k → HardAttentionHead n d) (w : Fin k → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (maj : (Fin n → Bool) → Bool) :=
  no_attn_of_witness_lower_bound
    (fun ws hfix agg => maj_needs_half_fixable_witnesses hk ws hfix agg)
    h w bias

/-- One head cannot compute maj₃. -/
theorem maj3_requires_two_heads {d : ℕ}
    (h : Fin 1 → HardAttentionHead 3 d) (w : Fin 1 → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (maj : (Fin 3 → Bool) → Bool) :=
  maj_attention_lower_bound (by norm_num) h w bias

/-- Two heads cannot compute maj₅. -/
theorem maj5_requires_three_heads {d : ℕ}
    (h : Fin 2 → HardAttentionHead 5 d) (w : Fin 2 → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (maj : (Fin 5 → Bool) → Bool) :=
  maj_attention_lower_bound (by norm_num) h w bias

/-- Inner product mod 2 on `2m` bits needs `m` heads. -/
theorem ip2_attention_lower_bound {m k d : ℕ} [NeZero m] (hk : k < m)
    (h : Fin k → HardAttentionHead (2 * m) d) (w : Fin k → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (ip2 : (Fin (2 * m) → Bool) → Bool) :=
  no_attn_of_witness_lower_bound
    (fun ws hfix agg => ip2_needs_m_fixable_witnesses hk ws hfix agg)
    h w bias

/-- The existing parity capstone, restated through `AttnComputes`
    (definitional repackaging of `parityN_requires_N_heads`). -/
theorem parityN_attention_lower_bound {n k d : ℕ} [NeZero n] (hk : k < n)
    (h : Fin k → HardAttentionHead n d) (w : Fin k → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (parityN : (Fin n → Bool) → Bool) :=
  fun hc => parityN_requires_N_heads hk h w bias hc

/-- maj₅ has a certificate of size 3: three pinned ones force the
    output. The decided half of the headline gap. -/
theorem maj5_has_size3_certificate :
    ∃ ρ : Fin 5 → Option Bool, (pins ρ).card = 3 ∧
      ∀ x, memCube ρ x → maj x = true := by
  refine ⟨fun j => if j.val < 3 then some true else none, by decide, ?_⟩
  decide

/-! ## §4 The Aristotle queue (each `sorry` = one work item) -/

/-- **S1 (queue).** Every decision list is the output function of a
    single hard-attention head. Construction sketch: internal dimension
    2 suffices; give the list's literals strictly decreasing scores
    (e.g. score `2^(len − depth)` for the literal at `depth`, its
    negation lower, unlisted literals lowest), so the argmax lands on
    the first live literal, and set the read value at each literal to
    match its node output (default handled by the terminal read values).
    With `fixable_exists_dl` this makes head-realizable = Fixable. -/
theorem dl_realizable_as_head {n : ℕ} [NeZero n] (r : DL n) :
    HeadRealizable (DL.eval r) := by
  sorry

/-- Fixable ⇒ head-realizable — derived from S1 (no extra work): the
    class of single-head output functions is EXACTLY `Fixable`
    (equivalently, decision lists — `fixable_iff_dl`). -/
theorem fixable_headRealizable {n : ℕ} [NeZero n]
    {f : (Fin n → Bool) → Bool} (hf : Fixable f) : HeadRealizable f := by
  obtain ⟨r, hr⟩ := fixable_exists_dl hf
  obtain ⟨d, head, hh⟩ := dl_realizable_as_head r
  exact ⟨d, head, fun x => (hh x).trans (hr x)⟩

/-- **S2 (queue).** No three Fixable witnesses compute maj₅ through any
    aggregator — the open Boolean gap (L2+L3+L4 of the k(maj₅)
    program). Inputs available: `maj5_reduction` narrows to two shapes;
    `T2_refining_pair_classified` / `T3_refining_pair_classified`
    classify the face catalogs those shapes force. Search-verified
    exhaustively (scripts/maj5_witness_search.py). -/
theorem maj5_no_three_fixable_witnesses :
    ∀ ws : Fin 3 → (Fin 5 → Bool) → Bool, (∀ i, Fixable (ws i)) →
    ∀ agg : (Fin 3 → Bool) → Bool,
      (fun x => agg (fun i => ws i x)) ≠ (maj : (Fin 5 → Bool) → Bool) := by
  sorry

/-- Three heads cannot compute maj₅ — derived from S2 via the transfer
    (no extra work). -/
theorem maj5_requires_four_heads {d : ℕ}
    (h : Fin 3 → HardAttentionHead 5 d) (w : Fin 3 → ℝ) (bias : ℝ) :
    ¬ AttnComputes h w bias (maj : (Fin 5 → Bool) → Bool) :=
  no_attn_of_witness_lower_bound maj5_no_three_fixable_witnesses h w bias

/-- **S3 (queue).** Four heads + affine readout compute maj₅. Route:
    the shipped witnesses `maj5W1..maj5W4` are decision lists → S1
    heads; the aggregator `(v₀ ∧ v₁) ∨ v₂ ∨ v₃` is the linear threshold
    `v₀ + v₁ + 2v₂ + 2v₃ > 3/2`. Mechanical once S1 lands. -/
theorem maj5_computable_by_four_heads :
    ∃ (d : ℕ) (h : Fin 4 → HardAttentionHead 5 d) (w : Fin 4 → ℝ)
      (bias : ℝ),
      AttnComputes h w bias (maj : (Fin 5 → Bool) → Bool) := by
  sorry

/-! ## §5 The headline -/

/-- **THE HEADLINE (derived from S2).** Attention head count is NOT
    certificate complexity: maj₅ has a certificate of size 3, yet no 3
    hard-attention heads compute it through any thresholded affine
    readout. The first gap, transferred to transformers. -/
theorem maj5_attention_certificate_gap :
    (∃ ρ : Fin 5 → Option Bool, (pins ρ).card = 3 ∧
      ∀ x, memCube ρ x → maj x = true) ∧
    (∀ (d : ℕ) (h : Fin 3 → HardAttentionHead 5 d) (w : Fin 3 → ℝ)
      (bias : ℝ),
      ¬ AttnComputes h w bias (maj : (Fin 5 → Bool) → Bool)) :=
  ⟨maj5_has_size3_certificate,
   fun _ h w bias => maj5_requires_four_heads h w bias⟩

end
