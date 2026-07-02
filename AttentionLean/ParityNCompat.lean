/-
Compatibility of the general `parityN` with the hardcoded small-case parity
functions. Kept separate from `ParityN` so that the general lower bound's
dependency chain stays off the heavy enumeration modules that `ParitySmall`
transitively imports.
-/

import AttentionLean.ParityN
import AttentionLean.ParitySmall

/-- `parityN` agrees with the hardcoded 3-bit parity. -/
theorem parityN_eq_parity3 : ∀ x : Fin 3 → Bool, parityN x = parity3 x := by decide

/-- `parityN` agrees with the hardcoded 4-bit parity. (`parity4` in
    `ParitySmall` is definitionally identical to `parity4M` in `Parity4Main`.) -/
theorem parityN_eq_parity4 : ∀ x : Fin 4 → Bool, parityN x = parity4 x := by decide
