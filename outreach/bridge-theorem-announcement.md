# attention-lean: distribution copy (bridge-theorem lead)

Draft outreach copy for the `attention-lean` release. The paper (`paper.md`, Zenodo DOI 10.5281/zenodo.21188380) leads with the scope caveat by design, correct for a paper. These are the distribution-facing versions that lead with the punchline instead. Nothing here changes the frozen artifact.

Prompted by an external review (Grok, 2026-07-04) that judged the work legitimate and flagged "lead with the bridge theorem" for reception. That framing belongs here, not in the paper.

## Lean Zulip post (community; #machine-learning-for-theorem-proving or #general)

**Title:** Machine-checked: single hard-attention head outputs are exactly decision lists

I have released `attention-lean`, a Lean 4 + Mathlib library proving an exact expressivity characterisation for a single-layer hard-attention model over Boolean cubes.

The core result (`head_output_iff_fixable`, with `fixable_iff_dl`): a Boolean function is the output of some hard-attention head if and only if it is a decision list. Both directions, and internal dimension two suffices for the realisation. So "what can one head compute" has an exact answer: the decision-list class, no more and no less.

That bridge turns head-count questions into a combinatorial witness number k(T). The flagship consequence is a genuine separation: k(maj5) = 4 while three agreeing votes certify five-bit majority, so witness number sits strictly above certificate complexity. maj5 needs four heads, and three provably cannot (`maj5_head_number_exact`).

Everything is kernel-checked on the axiom footprint {propext, Classical.choice, Quot.sound}, zero `sorry`, no `native_decide` on the clean tier, behind a compile-time gate that pins 103 declarations' footprints so any drift fails `lake build`.

Scope is deliberately narrow: single layer, position-local scores, thresholded affine readout, Boolean inputs. It is not a claim about deployed transformers. Scrutiny welcome, especially on the model choices.

Repo: github.com/velvetmonkey/attention-lean
Paper + DOI: 10.5281/zenodo.21188380

## arXiv teaser / short abstract (bridge-first ordering)

We give an exact, machine-checked characterisation of single-head expressivity in a hard-attention model over Boolean cubes: a Boolean function is a head output if and only if it is a decision list. This reduces head-count lower bounds to a combinatorial witness number, which yields the first separation in the model between witness number and certificate complexity: five-bit majority needs four heads though three votes certify it. The Lean 4 / Mathlib development is kernel-checked on a three-axiom footprint behind a compile-time gate, with no `sorry` and no `native_decide` on the clean tier.

## One-line hooks (pick per channel)

- One hard-attention head computes exactly the decision lists. Nothing more. Proved in Lean 4, kernel-checked.
- We machine-checked what a single attention head can compute. Answer: exactly decision lists. And five-bit majority needs four of them, not three.
