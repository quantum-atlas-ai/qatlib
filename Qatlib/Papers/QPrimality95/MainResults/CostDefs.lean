/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Logarithmic cost expressions for quantum primality testing

This module defines the real-valued logarithmic expressions used in the running-time analysis of
[ChauLo1995]. `basicCost` has a squared double-logarithm factor, while `mainCost` uses a single
double-logarithm factor; both contain cubic logarithm and triple-logarithm factors.

## Main statements

* `basicCost`: The real-valued expression `(log N)³ * (log (log N))² * log (log (log N))`.
* `mainCost`: The real-valued expression `(log N)³ * log (log N) * log (log (log N))`.

## References

* [Chau and Lo, 1995][ChauLo1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPrimality95.MainResults

open scoped BigOperators

/-- The real-valued expression `(log N)³ * (log (log N))² * log (log (log N))`. -/
noncomputable def basicCost (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 3 * (Real.log (Real.log (N : ℝ))) ^ 2 *
    Real.log (Real.log (Real.log (N : ℝ)))

/-- The real-valued expression `(log N)³ * log (log N) * log (log (log N))`. -/
noncomputable def mainCost (N : ℕ) : ℝ :=
  (Real.log (N : ℝ)) ^ 3 * Real.log (Real.log (N : ℝ)) *
    Real.log (Real.log (Real.log (N : ℝ)))

end Qatlib.Papers.QPrimality95.MainResults
