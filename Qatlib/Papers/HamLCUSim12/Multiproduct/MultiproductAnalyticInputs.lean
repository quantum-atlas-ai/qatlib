/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Analytic inputs for multiproduct coefficient bounds

This module defines the two analytic properties used in the multiproduct coefficient estimates.
`EtaMaxProperty` bounds a scalar ratio on [0, 1), and `FactorialLowerBound` gives an explicit
Stirling-type lower bound for natural-number factorials. See [ChildsWiebe2012] for the
multiproduct and linear-combination simulation framework.

## Main statements

* `EtaMaxProperty`: The property that η bounds λ² / ((1 + λ)^(1 + λ) (1 − λ)^(1 − λ)) for every
  0 ≤ λ < 1.
* `FactorialLowerBound`: The property that √(2πn) · n^n · exp(−n − 1 / 13) is at most n! for
  every natural number n.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option autoImplicit false
namespace Qatlib.Papers.HamLCUSim12.Multiproduct

/-- The property that η bounds λ² / ((1 + λ)^(1 + λ) (1 − λ)^(1 − λ)) for every 0 ≤ λ < 1. -/
def EtaMaxProperty (η : ℝ) : Prop :=
  ∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      lam ^ 2 / ((1 + lam) ^ ((1 + lam : ℝ)) * (1 - lam) ^ ((1 - lam : ℝ))) ≤ η

/-- The property that √(2πn) · n^n · exp(−n − 1 / 13) is at most n! for every natural number n. -/
def FactorialLowerBound : Prop :=
  ∀ n : ℕ,
    Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ) ^ ((n : ℝ)) * Real.exp (-((n : ℝ) + 1 / 13))
      ≤ (n.factorial : ℝ)

end Qatlib.Papers.HamLCUSim12.Multiproduct
