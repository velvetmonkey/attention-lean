# softmax_margin_realizes_dl scoping

Date: 2026-07-04
Branch: `scope/softmax-margin`
Mathlib pin: Lean/mathlib `v4.28.0`

## Verdict

`NEEDS-LEMMAS-FIRST`, not `ANALYSIS-SWAMP`, if the theorem is stated as
finite-temperature threshold/argmax agreement under an explicit positive
margin.

It becomes a weak bridge, and probably an analysis distraction, if the target
is exact equality of the soft-attention value with a hard selected value at
finite temperature. That equality is false in general: a finite softmax assigns
positive mass to every position, so the soft read is normally a convex mixture,
not the selected table entry. Exact equality is available only in the limiting
or degenerate case where all nonwinner values match the winner.

The clean Fable-shaped theorem is therefore not "softmax exactly equals hard
attention". It is:

* a finite decision-list score table has a strict positive score margin;
* if logits are scaled by `beta` above an explicit bound, the soft read has the
  same thresholded Boolean output as the hard decision list;
* the proof is finite inequalities over `Real.exp`, not topology.

That is a useful bridge, but it must be labelled honestly: it proves robust
classification agreement for sufficiently sharp softmax, not exact soft-value
realization.

## Candidate Statement

Use the existing finite Boolean domain and decision-list machinery:

* inputs: `x : Fin n -> Bool`;
* decision lists: `DL n` / `PriorityDL n`;
* score/read tables: `s r : Fin n -> Bool -> Real`;
* softmax inverse temperature: `beta : Real`;
* finite arity assumption: `[NeZero n]`;
* read values encoded as signs, e.g. `+1` for `true`, `-1` for `false`.

A concrete Lean-facing definition shape:

```lean
noncomputable def softWeight {n : Nat} [NeZero n]
    (beta : Real) (s : Fin n -> Real) (i : Fin n) : Real :=
  Real.exp (beta * s i) /
    ((Finset.univ : Finset (Fin n)).sum fun j => Real.exp (beta * s j))

noncomputable def softRead {n : Nat} [NeZero n]
    (beta : Real) (s r : Fin n -> Real) : Real :=
  (Finset.univ : Finset (Fin n)).sum fun i => softWeight beta s i * r i

def softBool (z : Real) : Bool :=
  if z > 0 then true else false
```

For the table-head form used in this repo, specialize per input:

```lean
softReadInput beta s r x :=
  softRead beta (fun i => s i (x i)) (fun i => r i (x i))
```

The scoped theorem should be a sign-agreement theorem:

```lean
theorem softmax_margin_realizes_dl
    {n : Nat} [NeZero n]
    (P : PriorityDL n) (beta gamma : Real)
    (hbeta_pos : 0 < beta)
    (hgamma : 0 < gamma)
    (hbeta : Real.log ((n - 1 : Nat) : Real) < beta * gamma) :
    forall x : Fin n -> Bool,
      let s := pscore P.entries
      let r := pread P.entries P.dflt
      softBool (softReadInput beta s r x) = P.eval x
```

That exact `hbeta` needs small edge-case cleanup for `n = 1` and for the
number of nonwinner alternatives. A proof-friendly statement is likely:

```lean
theorem softmax_margin_realizes_argmax_sign
    {n : Nat} [NeZero n]
    (beta gamma : Real) (scores reads : Fin n -> Real) (winner : Fin n)
    (want : Bool)
    (hbeta_pos : 0 < beta)
    (hgamma : 0 < gamma)
    (hbeta : (Fintype.card (Fin n) - 1 : Real) * Real.exp (-(beta * gamma)) < 1)
    (hwin : forall j, j != winner -> scores j + gamma <= scores winner)
    (hread_win : reads winner = if want then 1 else -1)
    (hread_bound : forall j, -1 <= reads j /\ reads j <= 1) :
    softBool (softRead beta scores reads) = want
```

Then instantiate it for `PriorityDL` via the existing `pscore`/`pread` tables.

This pins "realizes" as:

**finite-temperature thresholded output agreement**, uniformly for every input,
under a positive score margin and a sufficiently large inverse temperature.

It is not:

* exact equality of the soft read and the hard selected read at finite `beta`;
* a theorem about learned transformers;
* an approximation theorem unless a separate epsilon statement is added.

## Margin Encodability

Finite decision lists do encode with a strictly positive margin.

The repo already has the construction in hard-attention form:

* `PriorityDL.entries` is a list of `(coordinate, tested value, output)`
  triples;
* `pscore` gives the first matching entry a score equal to remaining-list
  length plus one;
* unmatched/complementary literals fall through to score `0`;
* `pread` gives the entry/default sign read (`+1`/`-1`);
* `priorityDL_realizable` proves the hard argmax output agrees with
  `PriorityDL.eval`.

Construction sketch:

1. Flatten a `DL n` to a priority list using `DL.toEntries`.
2. For the kth priority entry, assign score `length - k` to its tested
   literal and `0` to fall-through cases.
3. On an input with at least one live entry, the first live entry has score at
   least one greater than any later live entry. So `gamma = 1` works in the
   live case.
4. On an input with no live entry, all scores are `0`. The existing hard proof
   uses deterministic smallest-index tie-breaking and reads the default from
   all fall-through table entries. Softmax also reads the default exactly in
   this all-dead case because every `pread` value is the same default sign.

So the only "no strict unique winner" case is harmless: if no entry fires, all
reads are equal to the default, and the soft average is exactly the default
sign even though the scores are tied.

For duplicated literals, the existing construction still behaves correctly:
`pscore` and `pread` return the first matching table value, matching
`pevalList`. The margin is over live table values after this fall-through
resolution, not over raw list entries.

## Analysis Load

The argmax/margin semantics avoids heavy analysis.

For each fixed input, the desired bound is finite algebra:

* winner score exceeds every nonwinner score by at least `gamma`;
* therefore
  `exp (beta * score_j) / exp (beta * score_winner) <= exp (-(beta * gamma))`;
* the total nonwinner softmax mass is bounded by
  `(m - 1) * exp (-(beta * gamma))`;
* if that mass is `< 1/2`, and reads are in `[-1, 1]` with winner read `+1`,
  the soft read is positive; dually for winner read `-1`.

No continuity, compactness, differentiability, filters, or epsilon-delta
limits are needed for the sign-agreement theorem.

Heavy analysis becomes unavoidable only for different semantics:

* "as `beta -> infinity`, soft attention converges to hard attention";
* "for every epsilon, the soft read is within epsilon of the selected read";
* uniform convergence over a parameterized real input space;
* differentiability or learning-dynamics claims.

Those are not the right Fable target for this pass.

## Mathlib Inventory

Checked present under the repo's `v4.28.0` pin with `lake env lean --stdin`
unless marked as project-local.

Present:

* `Real.exp_pos`
  `Real.exp x` is positive.
* `Real.exp_lt_exp`
  Strict monotonicity as an iff.
* `Real.exp_le_exp`
  Non-strict monotonicity as an iff.
* `Real.exp_strictMono`
  Strict monotonicity packaged as `StrictMono`.
* `Real.exp_add`
  `exp (x + y) = exp x * exp y`.
* `Real.exp_sub`
  `exp (x - y) = exp x / exp y`.
* `Real.tendsto_exp_atTop`
  Present, but not needed for finite sign agreement.
* `Real.tendsto_exp_neg_atTop_nhds_zero`
  Present, but only needed for a limit/epsilon formulation.
* `Finset.sum_pos`, `Finset.sum_pos'`, `Finset.sum_nonneg`
  Enough for denominator positivity and finite mass bounds.
* `div_pos`, `div_lt_div_of_pos_right`, `div_le_div_of_nonneg_right`
  Enough for positivity and order through normalization.
* `one_div_lt_one_div`
  Useful for reciprocal comparisons.
* `Finset.exists_mem_eq_sup'`, `Finset.sup'_le`, `Finset.le_sup'`
  Existing finite maximum support.
* `Finset.min'_le`, `Finset.min'_mem`
  Existing finite tie-break support.
* `List.argmax`, `List.mem_argmax_iff`
  Available if a list-based argmax route is preferred.
* Project-local: `argmaxScore_eq_of`, `tableHeadN_output_strict`,
  `priorityDL_realizable`, `fixable_iff_dl`, `head_output_iff_fixable`,
  `pscore`, `pread`, `DL`, `PriorityDL`.

Missing / should be added locally:

* No mathlib `softmax` definition was found by source search.
  Add a local finite softmax definition rather than importing a new concept.
* No ready lemma of the form "winner margin bounds softmax nonwinner mass".
  Add a small local lemma.
* No ready lemma of the form "softmax sign agrees with bounded signed winner
  read under mass bound".
  Add a small local lemma.
* No project-local lemma yet extracting a uniform `gamma = 1` margin from
  `pscore` in the live-entry case.
  This should be proved next to `priority_live_winner` if implemented.
* No project-local soft fall-through lemma for the all-dead case.
  It should reuse `pread_all_dead` and `pscore_all_dead`.

Expected local lemma ladder:

1. `softWeight_pos`
2. `softWeight_sum_eq_one`
3. `softWeight_nonwinner_mass_le_of_margin`
4. `softRead_sign_eq_of_winner_mass`
5. `priorityDL_soft_margin_live`
6. `priorityDL_soft_all_dead`
7. `softmax_margin_realizes_dl`

Items 1-4 are real-inequality lemmas. Items 5-7 are finite decision-list
plumbing.

## Feasibility Call

`NEEDS-LEMMAS-FIRST`.

This is a plausible Fable target only after the finite softmax/mass-bound
lemma layer is added. It does not look like a real-analysis swamp if the
statement remains finite and thresholded.

Risk level:

* Low for definitions and positivity.
* Medium for algebraic normalization of finite softmax weights, because Lean
  can be fussy about division and sums.
* Medium for the explicit beta bound, especially casts around
  `Fintype.card (Fin n) - 1`.
* High if the statement is changed to exact finite-beta soft-value equality or
  general limit convergence.

## Weak-Bridge Trap

If the only final theorem says "under artificial margin assumptions and
sufficiently large logits, softmax approximates hard selection", that is a weak
bridge.

The defensible version here is slightly stronger and more honest:

* the margin is not artificial for finite decision lists; the existing
  priority-score construction gives it, with `gamma = 1` in live cases;
* the theorem gives exact Boolean output agreement at finite `beta`, not merely
  informal approximation;
* it still does not give exact equality of internal soft attention with hard
  attention.

So the bridge is meaningful for Boolean decision-list outputs, but it must not
be advertised as "soft attention realizes hard attention exactly".

## Finite / Piecewise-Linear Dodge

A finite or piecewise-linear version can dodge the swamp entirely.

Options:

* Replace exponential softmax by a finite "winner-take-most" rational weighting
  with an explicit margin parameter and prove the same mass bound by arithmetic.
* Use sparsemax/entmax-style piecewise-linear projection only if its finite
  support and normalization lemmas are stated locally; this avoids `exp` but
  introduces projection case splits.
* Stay purely hard/finite by proving a "margin-stable hard argmax" theorem:
  perturbing scores by less than `gamma / 2` preserves the selected decision
  list. This is the cleanest finite robustness story and uses no softmax.

The piecewise-linear route is likely easier than epsilon-limit softmax but less
standard. The hard margin-stability route is the cleanest no-analysis result.

## Open Questions

* Should `softmax_margin_realizes_dl` expose a beta bound using
  `(Fintype.card (Fin n) - 1) * exp (-(beta * gamma)) < 1`, avoiding `log`, or
  a more user-friendly `log` bound? The former is easier in Lean.
* Should the theorem be stated for `PriorityDL` first, then derive `DL` via
  `DL.toEntries`, matching the existing bridge?
* Should all reads be restricted to signs `{-1, +1}` in the first theorem?
  That makes the mass-to-sign lemma clean.
* Is the downstream target Boolean-only, or does the council need value-level
  approximation? Value-level approximation is possible but should be a separate
  theorem with an explicit epsilon and finite bound.
