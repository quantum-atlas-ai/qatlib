/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
set_option warningAsError false

open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

open Polynomial
open scoped BigOperators

noncomputable section

def thresholdIntegralPrimitive (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial (i + 1) (p.coeff i / (i + 1 : ℝ))

def integratedThresholdPolynomial (γ δ : ℝ) (k : ℕ) : Polynomial ℝ :=
  Polynomial.C γ * thresholdIntegralPrimitive
    (1 - thresholdPolynomial ((1 - δ / 2) / γ) k)

def integratedThresholdGap (γ δ : ℝ) : ℝ := δ / (4 * γ ^ 2)

def integratedThresholdTolerance (γ δ ε : ℝ) : ℝ := min ε (δ / (4 * γ))

def integratedThresholdCutoff (γ δ ε : ℝ) : ℕ :=
  Nat.ceil (Real.log ((integratedThresholdGap γ δ)⁻¹ ^ 2 *
    Real.log (1 / integratedThresholdTolerance γ δ ε)) / Real.log 2)

end
end Qatlib.Concepts.NonNormalSpec.ResolventWord
