/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreAuxiliary

/-!
# Polynomial response moduli and rectangle bands

This module defines the coefficient-weighted Lipschitz bound `polynomialLipschitzWeight` and its
associated response modulus. It also specifies bounded odd sign approximations and the rectangle
polynomial obtained by adding two translated sign responses. Background and related
constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `SignApproximation`: boundedness, gap error, and oddness for a sign response.
* `rectanglePolynomial`: forms the symmetric translated response.
* `RectangleBand`: specifies the interior and exterior value bands.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

/-- The coefficient weight given by the sum of k times the absolute value of the coefficient of
degree k. -/
noncomputable def polynomialLipschitzWeight (p : Polynomial ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k|

/-- The linear response modulus `polynomialLipschitzWeight p * δ`. -/
noncomputable def polynomialResponseModulus (p : Polynomial ℝ) (δ : ℝ) : ℝ :=
  polynomialLipschitzWeight p * δ

/-- Requires an odd real polynomial bounded by one on [−2, 2] and within `σ` of the sign
function at points with |x| ≥ δ. -/
def SignApproximation (S : Polynomial ℝ) (δ σ : ℝ) : Prop :=
  (∀ x : ℝ, |x| ≤ 2 → |S.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 2 → δ ≤ |x| → |S.eval x - Real.sign x| ≤ σ) ∧
  (∀ x : ℝ, S.eval (-x) = -S.eval x)

/-- The symmetric translated response ((1 − ε₀)/2)(S(X + t) + S(t − X)) + ε₀. -/
noncomputable def rectanglePolynomial (S : Polynomial ℝ) (ε₀ t : ℝ) : Polynomial ℝ :=
  Polynomial.C ((1 - ε₀) / 2) *
    (S.comp (Polynomial.X + Polynomial.C t) +
      S.comp (Polynomial.C t - Polynomial.X)) +
    Polynomial.C ε₀

/-- Requires boundedness by one on [−1, 1], exterior values within `e` of `ε₀`, and interior
values within `e` of one, with transition gap `δ` around the thresholds ±t. -/
def RectangleBand (P : Polynomial ℝ) (ε₀ δ t e : ℝ) : Prop :=
  (∀ x : ℝ, |x| ≤ 1 → |P.eval x| ≤ 1) ∧
  (∀ x : ℝ, |x| ≤ 1 → (x ≤ -(t + δ) ∨ t + δ ≤ x) →
    ε₀ - e ≤ P.eval x ∧ P.eval x ≤ ε₀ + e) ∧
  (∀ x : ℝ, |x| ≤ 1 → -(t - δ) ≤ x ∧ x ≤ t - δ →
    1 - e ≤ P.eval x ∧ P.eval x ≤ 1 + e)

end Qatlib.Concepts.QsvtCore.ApproxToolkit
