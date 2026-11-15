/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace Qatlib.Foundations.ProbabilityCore.Concentration

open scoped BigOperators

def GaussianShiftTVDBound : Prop :=
  ∀ (N : ℕ) (v : Fin N → ℂ),
    (1 / 2) * ∫ x : Fin N → ℂ,
        |∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i - v i))))
          - ∏ i, (Real.pi⁻¹ * Real.exp (-(Complex.normSq (x i))))|
      ∂MeasureTheory.volume
      ≤ ∑ i, Real.sqrt (Complex.normSq (v i))

end Qatlib.Foundations.ProbabilityCore.Concentration
