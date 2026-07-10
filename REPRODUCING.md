# Reproducing the results

Everything below is deterministic: kernel-checked Lean plus exhaustive Python searches with no randomness.

## Toolchain

- Lean 4, pinned by `lean-toolchain` (elan installs it automatically): `leanprover/lean4:v4.28.0`
- Mathlib `v4.28.0` (pinned in `lake-manifest.json`)
- Python 3 (stdlib only) for the guard and the independent cross-check scripts

## Build and verify

```bash
# from the repo root
lake exe cache get                  # fetch the Mathlib build cache (without it, Mathlib builds from source — hours)
lake build                          # builds the library AND the axiom transcripts (defaultTargets)
lake exe axiom_check                # replays the pinned axiom footprint of every headline theorem
python3 scripts/check_no_sorry.py   # comment-aware guard: no `sorry` outside comments
```

`lake build` compiles `AttentionLean/Axioms.lean` (clean tier: 111 `#guard_msgs` pins, each declaration on exactly `propext, Classical.choice, Quot.sound`) and `AttentionLean/AxiomsDirty.lean` (the two enumerated `native_decide` results, pinned WITH their `Lean.ofReduceBool` / `Lean.trustCompiler` footprint). Any axiom drift fails the build itself.

Expected tail of a successful run:

```text
Build completed successfully (16100 jobs).
$ lake exe axiom_check
axiom gate passed: all checks pinned by #guard_msgs at compile time
$ python3 scripts/check_no_sorry.py
no sorry outside comments (43 files checked)
```

Measured times (8-core / 15 GiB Linux VPS):

| Step | Time |
|---|---|
| `lake build`, cold project cache (after `cache get`; the package rename in July 2026 invalidated all project traces, so this is the true worst case) | ~3.5–4 h wall-clock, dominated by the four `Parity4AchieveR3*` `native_decide` enumeration batches (>1 h each, run in parallel) |
| `lake build`, warm (no-op rebuild) | ~7 s |
| `lake exe axiom_check` (replay) | ~7 s |
| `python3 scripts/check_no_sorry.py` | <1 s |

Note the memory pressure during the cold build: with the four enumeration batches elaborating in parallel, system memory usage peaked around 8 GiB. On smaller boxes, build those modules one at a time first (e.g. `lake build AttentionLean.Parity4AchieveR3TT`, then the rest) to serialize the peaks.

## Independent cross-checks (Python, no code shared with the Lean development)

```bash
python3 scripts/parity_head_search.py     # ~17 s
python3 scripts/maj5_witness_search.py    # ~13 s
python3 scripts/maj5_case_kill_oracle.py  # ~15 s
```

Expected output (verbatim, deterministic):

```text
parity3 with 3 heads: IMPOSSIBLE  <- refutes parityN_achievable_with_N_heads
parity3 with 4 heads: ACHIEVABLE  (4 = 2^(3-1); see ParityAchieve.lean for the general theorem)

config (c) assemblies tried: 262144 solutions: 0
4-witness construction ok: True

case2: candidates 2880 unfixable 2880 (per-e hitting lists of size 8)
case3 matched bad triples: sigma=1: 0  sigma=0: 0
```

## Archived version

Zenodo: version DOI [10.5281/zenodo.21298767](https://doi.org/10.5281/zenodo.21298767) (v5, the hard-and-soft re-headline; concept DOI [10.5281/zenodo.21188380](https://doi.org/10.5281/zenodo.21188380) always resolves to the latest). The archived deposit corresponds to commit `f8dc423`. The paper source is `paper.md`; build the PDF with `bash build-pdf.sh` (pandoc + tectonic + JuliaMono).
