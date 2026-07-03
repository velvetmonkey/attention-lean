/-
  AttentionLean — A Lean 4 / Mathlib library for hard attention over finite sequences.

  Phase 1: single-head expressiveness bounds for 2-bit Boolean functions.
  Phase 2: AndOr / Xor expressiveness results.
  Phase 3: Parity-on-4-bits requires 4 heads (imported from Aristotle proof run).
  Phase 4: General parity lower bound — fewer than n heads cannot compute
           parity on n bits, structurally (no native_decide).
-/
import AttentionLean.Defs
import AttentionLean.Compute
import AttentionLean.AndOr
import AttentionLean.Xor
import AttentionLean.Parity4Data
import AttentionLean.Parity4AchieveDefs
import AttentionLean.Parity4AchieveND
import AttentionLean.Parity4AchieveR3FF
import AttentionLean.Parity4AchieveR3FT
import AttentionLean.Parity4AchieveR3TF
import AttentionLean.Parity4AchieveR3TT
import AttentionLean.Parity4AchieveAssembly
import AttentionLean.Parity4Achieve
import AttentionLean.Parity4TripleA
import AttentionLean.Parity4TripleB
import AttentionLean.Parity4TripleC
import AttentionLean.Parity4TripleD
import AttentionLean.Parity4Triple
import AttentionLean.ParitySmall
import AttentionLean.Parity4Main
import AttentionLean.ParityN
import AttentionLean.ParityNCompat
import AttentionLean.ParityWindow
import AttentionLean.ParityAchieve
import AttentionLean.Parity3Clean
import AttentionLean.WitnessSeparation
import AttentionLean.WitnessTheory
import AttentionLean.WitnessEmbedding
import AttentionLean.WitnessMajority
import AttentionLean.WitnessTightness
import AttentionLean.WitnessMaj5
import AttentionLean.WitnessMaj5Lower
