/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

noncomputable def cisdExponentReal (D : ℕ) (δ : ℝ) : ℝ :=
  (1 / 4) * (1 + Real.logb 2 (((D : ℝ) + 2) / (Real.sqrt (1 + δ) - 1) ^ 2))

noncomputable def cisdExponent (D : ℕ) (δ : ℝ) : ℕ :=
  ⌈cisdExponentReal D δ⌉₊

noncomputable def cisdReductionTCount (D N : ℕ) (δ : ℝ) : ℝ :=
  (22 * (cisdExponent D δ : ℝ) + 64 * ((N : ℝ) - 3)) * ((D : ℝ) + 1)

end Qatlib.Papers.TrotterSuzuki14.MainResults
