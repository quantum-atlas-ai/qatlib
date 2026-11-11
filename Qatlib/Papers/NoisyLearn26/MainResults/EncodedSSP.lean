/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
import Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation

/-!
# Encoded oracle interfaces and a square-root bound

Constructs `encodedShufflingOracle` with identity evaluation and an identity shadow, and defines
the fixed-depth predicate `BPPQNC`. The theorem `o2h_encoded_oracle` extracts a square-root
bound from an assumed squared difference estimate. See [CotlerGongKannan2025] for the
surrounding analysis.

## Main statements

* `encodedShufflingOracle`: An encoded oracle interface of width `n * (d + 2)` with identity
  evaluation, a true shuffling proposition, and an identity shadow.
* `o2h_encoded_oracle`: An assumed bound `|Ptrue - Pshadow|² ≤ 2 * q * p` yields `|Ptrue -
  Pshadow| ≤ √(2 * q * p)` when `p` is nonnegative.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.EncodedSSP

open Qatlib.Papers.NoisyLearn26.MainResults
open Qatlib.Papers.NoisyLearn26.MainResults.OracleSeparation

/-- An encoded oracle interface of width `n * (d + 2)` with identity evaluation, a true
shuffling proposition, and an identity shadow. -/
def encodedShufflingOracle {n : ℕ} (f : Reg n → Reg n) (d : ℕ) :
    EncodedShufflingOracle n d where
  width := n * (d + 2)
  eval := fun x => x
  isShuffling := True
  shadow := { width := n * (d + 2), eval := fun x => x }

/-- The predicate that an oracle-relative algorithm uses polynomially bounded queries and has
constant depth function equal to `d`. -/
def BPPQNC {O : Oracle} (d : ℕ) (A : RelAlgorithm O) : Prop :=
  IsPolynomial A.queries ∧ A.depth = fun _ => d

/-- An assumed bound `|Ptrue - Pshadow|² ≤ 2 * q * p` yields `|Ptrue - Pshadow| ≤ √(2 * q * p)`
when `p` is nonnegative. -/
theorem o2h_encoded_oracle (q : ℕ) (p Ptrue Pshadow : ℝ)
    (hp : 0 ≤ p) (hO2H : |Ptrue - Pshadow| ^ 2 ≤ 2 * (q : ℝ) * p) :
    |Ptrue - Pshadow| ≤ Real.sqrt (2 * (q : ℝ) * p) := by
  calc
    |Ptrue - Pshadow| = Real.sqrt (|Ptrue - Pshadow| ^ 2) := by
      rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (2 * (q : ℝ) * p) := Real.sqrt_le_sqrt hO2H

end Qatlib.Papers.NoisyLearn26.MainResults.EncodedSSP
