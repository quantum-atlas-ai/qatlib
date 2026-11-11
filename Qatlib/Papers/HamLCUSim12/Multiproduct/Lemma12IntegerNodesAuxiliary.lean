/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rounded multiproduct parameters

This module defines the parameters used to replace the terminal exponential multiproduct node by
an integer. The threshold `gammaReq`, rounded `integerNode`, and `correctedGamma` specify the
new node, while `errorBudget` and `retryCount` encode the accuracy and repetition requirements.
See [ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `integerNode`: The integer ceiling of exp((k + 1) · `gammaReq η k`), used as the terminal
  multiproduct node.
* `retryCount`: The integer ceiling of the maximum of the accuracy-dependent repetition bound
  and 13 log(2 / β).

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Real
open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The logarithmic threshold 1 + log η / 2 + log(2 (2k)^(5/2)) / (2k) for the terminal-node
exponent. -/
noncomputable def gammaReq (η : ℝ) (k : ℕ) : ℝ :=
  1 + log η / 2 + (1 / (2 * (k : ℝ))) * log (2 * ((2 * (k : ℝ)) : ℝ)^(5 / 2 : ℝ))

/-- The integer ceiling of exp((k + 1) · `gammaReq η k`), used as the terminal multiproduct
node. -/
noncomputable def integerNode (η : ℝ) (k : ℕ) : ℤ :=
  Int.ceil (exp (((k + 1 : ℕ) : ℝ) * gammaReq η k))

/-- The exponent log(`integerNode η k`) / (k + 1) corresponding to the rounded terminal node. -/
noncomputable def correctedGamma (η : ℝ) (k : ℕ) : ℝ :=
  log (integerNode η k) / ((k + 1 : ℕ) : ℝ)

/-- The minimum of 1, ε, β, and mht / k^(4k), used as the auxiliary error budget. -/
noncomputable def errorBudget (m h t ε β : ℝ) (k : ℕ) : ℝ :=
  min 1 (min ε (min β (m * h * t / ((k : ℝ)^((4 * k : ℕ) : ℝ)))))

/-- The integer ceiling of the maximum of the accuracy-dependent repetition bound and 13 log(2 /
β). -/
noncomputable def retryCount (m h t ε β : ℝ) (k : ℕ) : ℤ :=
  Int.ceil
    (max
      ((4 * m * ((5 : ℝ) / 3)^(k - 1) * h * t)^(1 + 1 / ((4 : ℝ) * (k : ℝ)))
        / ((errorBudget m h t ε β k / 5)^(1 / ((4 : ℝ) * (k : ℝ)))))
      (13 * log (2 / β)))
end Qatlib.Papers.HamLCUSim12.Multiproduct
