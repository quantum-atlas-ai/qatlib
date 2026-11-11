/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core

/-!
# Q2 truncated-differential distinguisher costs

`singleStructureCost` and `multiStructureCost` express the two structure regimes, and
`q2TruncatedDistinguisherCost` takes their maximum. The identities combine two-thirds-power pair
checking with inverse-square-root amplification of the multi-structure success scale. The
mathematical context is [KaplanEtAl2015].

## Main statements

* `multi_structure_total_cost`: Multiplying the multi-structure amplification and checking
  factors gives `2^((hT+1)/2-Δin/3)`.
* `q2_truncated_distinguisher_cost`: The Q2 cost expression is the maximum of the
  single-structure two-thirds-power cost and the multi-structure amplification factor times its
  checking cost.

## References

* [Kaplan et al., 2015][KaplanEtAl2015]
-/

set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential

open Complexity

/-- The multi-structure success-scale expression `2^(2Δin-hT-1)`. -/
noncomputable def truncatedMultiEpsilon (hT Δin : ℝ) : ℝ := pow2 (2 * Δin - hT - 1)

/-- The single-structure cost expression `2^((hT+1)/3)`. -/
noncomputable def singleStructureCost (hT : ℝ) : ℝ := pow2 ((hT + 1) / 3)

/-- The multi-structure cost expression `2^((hT+1)/2-Δin/3)`. -/
noncomputable def multiStructureCost (hT Δin : ℝ) : ℝ :=
  pow2 ((hT + 1) / 2 - Δin / 3)

/-- The maximum of the single-structure and multi-structure Q2 cost expressions. -/
noncomputable def q2TruncatedDistinguisherCost (hT Δin : ℝ) : ℝ :=
  max (singleStructureCost hT) (multiStructureCost hT Δin)

/-- The two-thirds power of `2^((hT+1)/2)` equals `2^((hT+1)/3)`. See [KaplanEtAl2015]. -/
theorem single_structure_ambainis_cost (hT : ℝ) :
    pow2 ((hT + 1) / 2) ^ (2 / 3 : ℝ) = pow2 ((hT + 1) / 3) := by
  rw [← pow2_mul]
  congr 1
  ring

/-- The multi-structure success-scale expression is `2^(2Δin-hT-1)`. -/
theorem multi_structure_success_epsilon (hT Δin : ℝ) :
    truncatedMultiEpsilon hT Δin = pow2 (2 * Δin - hT - 1) := rfl

/-- The reciprocal square root of the multi-structure success scale is `2^((hT+1)/2-Δin)`. See
[KaplanEtAl2015]. -/
theorem multi_structure_grover_iterations (hT Δin : ℝ) :
    (Real.sqrt (truncatedMultiEpsilon hT Δin))⁻¹ = pow2 ((hT + 1) / 2 - Δin) := by
  unfold truncatedMultiEpsilon
  have hexp : 2 * Δin - hT - 1 = -(hT + 1 - 2 * Δin) := by ring
  rw [hexp, inv_sqrt_pow2_neg]
  congr 1
  ring

/-- The two-thirds power of `2^Δin` is `2^(2Δin/3)`. See [KaplanEtAl2015]. -/
theorem multi_structure_check_cost (Δin : ℝ) :
    pow2 Δin ^ (2 / 3 : ℝ) = pow2 (2 * Δin / 3) := by
  rw [← pow2_mul]
  congr 1
  ring

/-- Multiplying the multi-structure amplification and checking factors gives
`2^((hT+1)/2-Δin/3)`. See [KaplanEtAl2015]. -/
theorem multi_structure_total_cost (hT Δin : ℝ) :
    pow2 ((hT + 1) / 2 - Δin) * pow2 (2 * Δin / 3) =
      pow2 ((hT + 1) / 2 - Δin / 3) := by
  rw [← pow2_add]
  congr 1
  ring

/-- The Q2 cost expression is the maximum of the single-structure two-thirds-power cost and the
multi-structure amplification factor times its checking cost. See [KaplanEtAl2015]. -/
theorem q2_truncated_distinguisher_cost (hT Δin : ℝ) :
    q2TruncatedDistinguisherCost hT Δin =
      max (pow2 ((hT + 1) / 2) ^ (2 / 3 : ℝ))
        ((Real.sqrt (truncatedMultiEpsilon hT Δin))⁻¹ * pow2 Δin ^ (2 / 3 : ℝ)) := by
  unfold q2TruncatedDistinguisherCost singleStructureCost multiStructureCost
  rw [single_structure_ambainis_cost, multi_structure_grover_iterations,
    multi_structure_check_cost, multi_structure_total_cost]

end Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential
