/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# FeMoCo spacetime resource comparisons

Defines the simple spacetime proxy `spacetime` as logical qubits multiplied by Toffoli count.
Exact rational inequalities compare two pairs of FeMoCo resource estimates reported in
[LeeEtAl2021].

The combined theorem `feMoCo_spacetime_reduction` records lower bounds of three and `29 / 5` for
the respective ratios.

## Main statements

* `reiher_spacetime_reduction`: bounds the first resource ratio between three and `7 / 2`.
* `li_spacetime_reduction`: bounds the second resource ratio between `29 / 5` and six.
* `feMoCo_spacetime_reduction`: combines the two lower bounds.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.FeMoCoResources

/-- The product of a logical-qubit count and a Toffoli count. -/
def spacetime (qubits toffolis : ℕ) : ℕ := qubits * toffolis

/-- The ratio of the spacetime proxies for `(3725, 10000000000)` and `(2142, 5300000000)` lies
between three and `7 / 2`. -/
theorem reiher_spacetime_reduction :
    (3 : ℚ) ≤ (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ∧
      (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ≤ 7 / 2 := by
  norm_num [spacetime]

/-- The ratio of the spacetime proxies for `(6404, 64000000000)` and `(2196, 32000000000)` lies
between `29 / 5` and six. -/
theorem li_spacetime_reduction :
    (29 / 5 : ℚ) ≤ (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) ∧
      (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) ≤ 6 := by
  norm_num [spacetime]

/-- The two specified FeMoCo spacetime ratios are at least three and `29 / 5`, respectively. See
[LeeEtAl2021]. -/
theorem feMoCo_spacetime_reduction :
    (3 : ℚ) ≤ (spacetime 3725 10000000000 : ℚ) / (spacetime 2142 5300000000 : ℚ) ∧
      (29 / 5 : ℚ) ≤
        (spacetime 6404 64000000000 : ℚ) / (spacetime 2196 32000000000 : ℚ) :=
  ⟨reiher_spacetime_reduction.1, li_spacetime_reduction.1⟩

end Qatlib.Papers.TensorHyper20.MainResults.FeMoCoResources
