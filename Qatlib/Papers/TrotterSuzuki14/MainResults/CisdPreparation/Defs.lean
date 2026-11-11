/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic

/-!
# CISD precision exponent and T-count ledger

This module defines the real precision expression `cisdExponentReal`, its natural-number ceiling
`cisdExponent`, and the resulting CISD reduction T-count ledger. These expressions encode the
dimension and target-precision dependence used in the preparation estimates. See
[BabbushEtAl2015].

## Main statements

* `cisdExponent`: Natural-number ceiling of the real precision exponent.
* `cisdReductionTCount`: Explicit resource ledger in terms of the rounded exponent.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

/-- The real CISD precision exponent `(1/4) * (1 + log₂((D + 2) / (sqrt (1 + δ) - 1)²))`. -/
noncomputable def cisdExponentReal (D : ℕ) (δ : ℝ) : ℝ :=
  (1 / 4) * (1 + Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2))

/-- The natural-number ceiling of `cisdExponentReal D δ`. -/
noncomputable def cisdExponent (D : ℕ) (δ : ℝ) : ℕ :=
  ⌈cisdExponentReal D δ⌉₊

/-- The real-valued CISD reduction T-count ledger `(22 * cisdExponent D δ + 64 * (N - 3)) * (D +
1)`. -/
noncomputable def cisdReductionTCount (D N : ℕ) (δ : ℝ) : ℝ :=
  (22 * (cisdExponent D δ : ℝ) + 64 * ((N : ℝ) - 3)) * ((D : ℝ) + 1)

end Qatlib.Papers.TrotterSuzuki14.MainResults
