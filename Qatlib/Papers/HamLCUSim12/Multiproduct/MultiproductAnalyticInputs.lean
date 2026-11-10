/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

def EtaMaxProperty (η : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      lam ^ 2 / ((1 + lam) ^ ((1 + lam : ℝ)) * (1 - lam) ^ ((1 - lam : ℝ))) ≤ η

def FactorialLowerBound : Prop :=
  ∀ n : ℕ,
    Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ) ^ ((n : ℝ)) * Real.exp (-((n : ℝ) + 1 / 13))
      ≤ (n.factorial : ℝ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
