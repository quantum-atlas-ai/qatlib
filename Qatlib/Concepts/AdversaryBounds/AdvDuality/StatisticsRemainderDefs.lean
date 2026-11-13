/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsRemainder

/-!
# Rare-event distributions for variance estimation

`rareBitLaw` assigns probability `1 / D` to a true bit, and `rareValue` maps that bit to `D * A`
while mapping false to zero. `pilotFailure` measures the probability that a pilot statistic from
independent samples falls below the resulting variance.

The integer weights `rareWeights` encode the same rare-event ratio for sampling constructions.
This family supports analysis of variance information in Monte Carlo estimation; see
[Montanaro2015].

## Main statements

* `rareBitLaw`: defines the two-point rare-event distribution for `D ≥ 2`.
* `rareValue`: defines the scaled rare-event observable.
* `pilotFailure`: measures variance underestimation by a sample-based pilot.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
open scoped Classical

/-- The two integer weights `D - 1` and `1`, assigned to indices zero and one respectively. -/
def rareWeights (D : ℕ) (j : Fin 2) : ℕ := if j = 0 then D - 1 else 1

/-- The Boolean distribution with true probability `1 / D` and false probability `1 - 1 / D`,
for `D ≥ 2`. -/
noncomputable def rareBitLaw (D : ℕ) (hD : 2 ≤ D) : FinDist Bool where
  prob b := if b then 1 / (D : ℝ) else 1 - 1 / (D : ℝ)
  nonneg b := by
    have hpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hone : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    cases b
    · exact sub_nonneg.mpr ((div_le_one hpos).mpr hone)
    · change 0 ≤ 1 / (D : ℝ)
      positivity
  sum_one := by simp

/-- The rare-event observable taking value `D * A` on true and zero on false. -/
def rareValue (D A : ℕ) (b : Bool) : ℝ := if b then (D * A : ℕ) else 0

/-- The probability that the pilot evaluated on `m` independent rare-event observations is
strictly below the observable's variance. -/
noncomputable def pilotFailure (D A m : ℕ) (hD : 2 ≤ D)
    (pilot : (Fin m → ℝ) → ℝ) : ℝ :=
  (rareBitLaw D hD).probEvent (fun ω =>
    pilot (fun i => rareValue D A (ω i)) < (rareBitLaw D hD).variance (rareValue D A))

end Qatlib.Concepts.AdversaryBounds.AdvDuality
