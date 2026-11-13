/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Threshold integral amplifier definitions

`thresholdIntegralPrimitive` fixes a primitive with zero constant term, and
`integratedThresholdPolynomial` applies it to the complement of a threshold polynomial. Gap,
tolerance, and cutoff parameters specify the resulting amplifier construction in the polynomial
transformation setting of [GilyenSuLowWiebe2019]

## Main statements

* `integratedThresholdPolynomial`: defines the scaled primitive of the threshold complement.
* `integratedThresholdCutoff`: chooses the iteration count from the gap and tolerance.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

open Polynomial
open scoped BigOperators

noncomputable section

/-- The real polynomial primitive formed by dividing each coefficient by its new exponent and
setting the constant term to zero. -/
def thresholdIntegralPrimitive (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.monomial (i + 1) (p.coeff i / (i + 1 : ℝ))

/-- The polynomial obtained by multiplying by `γ` the zero constant term primitive of the
complement of `thresholdPolynomial ((1 - δ / 2) / γ) k`. -/
def integratedThresholdPolynomial (γ δ : ℝ) (k : ℕ) : Polynomial ℝ :=
  Polynomial.C γ * thresholdIntegralPrimitive
    (1 - thresholdPolynomial ((1 - δ / 2) / γ) k)

/-- The real amplifier gap `δ / (4 * γ²)`. -/
def integratedThresholdGap (γ δ : ℝ) : ℝ := δ / (4 * γ ^ 2)

/-- The real amplifier tolerance `min ε (δ / (4 * γ))`. -/
def integratedThresholdTolerance (γ δ ε : ℝ) : ℝ := min ε (δ / (4 * γ))

/-- The natural ceiling of `log (gap⁻² * log (1 / tolerance)) / log 2`, using the integrated
threshold gap and tolerance. -/
def integratedThresholdCutoff (γ δ ε : ℝ) : ℕ :=
  Nat.ceil (Real.log ((integratedThresholdGap γ δ)⁻¹ ^ 2 *
    Real.log (1 / integratedThresholdTolerance γ δ ε)) / Real.log 2)

end
end Qatlib.Concepts.NonNormalSpec.ResolventWord
