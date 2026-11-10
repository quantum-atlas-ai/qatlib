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

open Real
open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

noncomputable def gammaReq (η : ℝ) (k : ℕ) : ℝ :=
  1 + log η / 2 + (1 / (2 * (k : ℝ))) * log (2 * ((2 * (k : ℝ)) : ℝ)^(5 / 2 : ℝ))

noncomputable def integerNode (η : ℝ) (k : ℕ) : ℤ :=
  Int.ceil (exp (((k + 1 : ℕ) : ℝ) * gammaReq η k))

noncomputable def correctedGamma (η : ℝ) (k : ℕ) : ℝ :=
  log (integerNode η k) / ((k + 1 : ℕ) : ℝ)

noncomputable def errorBudget (m h t ε β : ℝ) (k : ℕ) : ℝ :=
  min 1 (min ε (min β (m * h * t / ((k : ℝ)^((4 * k : ℕ) : ℝ)))))

noncomputable def retryCount (m h t ε β : ℝ) (k : ℕ) : ℤ :=
  Int.ceil
    (max
      ((4 * m * ((5 : ℝ) / 3)^(k - 1) * h * t)^(1 + 1 / ((4 : ℝ) * (k : ℝ)))
        / ((errorBudget m h t ε β k / 5)^(1 / ((4 : ℝ) * (k : ℝ)))))
      (13 * log (2 / β)))
end Qatlib.Papers.HamLCUSim12.Multiproduct
