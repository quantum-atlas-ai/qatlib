/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Log

/-!
# Rational data for threshold integral amplification

Coefficient list operations define a rational integrated threshold polynomial and explicit
native budgets for its cutoff and degree. `nativeAmplifierPhaseResult` passes these data to
finite phase synthesis, providing a computational counterpart to the polynomial transformations
studied in [GilyenSuLowWiebe2019]

## Main statements

* `rationalIntegratedThresholdCoefficients`: constructs the amplifier coefficient list.
* `nativeAmplifierCutoff` and `nativeAmplifierDegree`: specify the native iteration and degree
  budgets.
* `nativeAmplifierPhaseResult`: runs finite synthesis with tolerance `ε / 2`.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option autoImplicit false

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

/-- Composition of rational coefficient lists, evaluated recursively in Horner form. -/
def rationalPolynomialCompose : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => ratAddList [x] (ratMulList (rationalPolynomialCompose xs ys) ys)

/-- The rational coefficient list for one half of one plus the sign polynomial evaluated at `x²
- τ²`. -/
def rationalThresholdCoefficients (τ : ℚ) (k : ℕ) : List ℚ :=
  (ratAddList [1]
    (rationalPolynomialCompose (rationalSignCoefficients k) [-(τ ^ 2), 0, 1])).map
      (fun x => x / 2)

/-- The coefficient list of the primitive scaled by `γ`, with zero constant coefficient and each
original coefficient divided by its new exponent. -/
def rationalIntegralCoefficients (γ : ℚ) (xs : List ℚ) : List ℚ :=
  0 :: xs.zipIdx.map (fun ai => γ * ai.1 / (ai.2 + 1 : ℚ))

/-- The rational coefficient list obtained by integrating `γ` times the complement of the
threshold polynomial at threshold `(1 - δ / 2) / γ`. -/
def rationalIntegratedThresholdCoefficients (γ δ : ℚ) (k : ℕ) : List ℚ :=
  rationalIntegralCoefficients γ
    (ratSubList [1] (rationalThresholdCoefficients ((1 - δ / 2) / γ) k))

/-- The rational amplifier gap `δ / (4 * γ²)`. -/
def nativeAmplifierGap (γ δ : ℚ) : ℚ := δ / (4 * γ ^ 2)
/-- The rational amplifier tolerance `min ε (δ / (4 * γ))`. -/
def nativeAmplifierTolerance (γ δ ε : ℚ) : ℚ := min ε (δ / (4 * γ))
/-- The ceiling base two logarithm of the natural ceiling of the reciprocal native amplifier
tolerance. -/
def nativeAmplifierLogBudget (γ δ ε : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / nativeAmplifierTolerance γ δ ε))
/-- The natural ceiling of the inverse squared native gap times the logarithmic budget. -/
def nativeAmplifierExponentBudget (γ δ ε : ℚ) : ℕ :=
  Nat.ceil ((nativeAmplifierGap γ δ)⁻¹ ^ 2 * nativeAmplifierLogBudget γ δ ε)
/-- The ceiling base two logarithm of the native exponent budget. -/
def nativeAmplifierCutoff (γ δ ε : ℚ) : ℕ :=
  Nat.clog 2 (nativeAmplifierExponentBudget γ δ ε)
/-- The amplifier degree budget `2 * 3^cutoff + 1`. -/
def nativeAmplifierDegree (γ δ ε : ℚ) : ℕ := 2 * 3 ^ nativeAmplifierCutoff γ δ ε + 1

/-- The finite phase synthesis result for the native integrated threshold coefficients, using
the native degree budget and tolerance `ε / 2`. -/
def nativeAmplifierPhaseResult (γ δ ε : ℚ) : SynthesisResult :=
  finitePhaseSynthesis
    (rationalIntegratedThresholdCoefficients γ δ (nativeAmplifierCutoff γ δ ε))
    (nativeAmplifierDegree γ δ ε) (ε / 2)

end Qatlib.Concepts.NonNormalSpec.ResolventWord
