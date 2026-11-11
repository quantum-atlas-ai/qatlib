/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Schatten quantities and superoperator factorizations

`schatten` is the real-power expression in the singular values of a square matrix, and
`schattenTop` uses the Euclidean operator norm. `schattenDual` packages a trace-pairing supremum
with conjugate-exponent constraints, in the setting of matrix norms described in [Watrous2018].

`CbFactorization` represents a superoperator as a finite sum of terms of the form `Aᴴ * X * B`.
`cbFactorizationNorm` assigns a product of Hilbert--Schmidt size bounds to such a
representation, and `cbNormDual` takes their extended-real infimum.

## Main statements

* `schatten_one_eq_traceNorm`: the exponent-one expression equals the trace norm.
* `CbStrictlyFeasible`: existence of a factorization with positive assigned cost.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

namespace Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

open Matrix
open scoped BigOperators ENNReal

section Schatten

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The real-power expression `(∑ i, singularValues A i ^ p) ^ p⁻¹` defining the finite Schatten
quantity at exponent `p`. -/
noncomputable def schatten (p : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (∑ i, (singularValues A i) ^ p) ^ (p⁻¹)

/-- The Schatten quantity at exponent one equals the matrix trace norm. -/
theorem schatten_one_eq_traceNorm (A : Matrix n n ℂ) :
    schatten 1 A = A.traceNorm := by
  simp [schatten, Matrix.traceNorm_eq_sum_singularValues]

section Top

variable {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]

open scoped Matrix.Norms.L2Operator

/-- The Euclidean operator norm of a rectangular complex matrix, used as the Schatten infinity
quantity. -/
noncomputable def schattenTop (A : Matrix m k ℂ) : ℝ := ‖A‖

end Top

/-- The supremum of absolute trace pairings with matrices of Schatten `q` quantity at most one,
subject to `1 < p` and `p⁻¹ + q⁻¹ = 1`. -/
noncomputable def schattenDual (p q : ℝ) (A : Matrix n n ℂ) : ℝ :=
  sSup {r | 1 < p ∧ p⁻¹ + q⁻¹ = 1 ∧ ∃ B : Matrix n n ℂ,
    schatten q B ≤ 1 ∧ r = ‖Matrix.trace (Bᴴ * A)‖}

end Schatten

section Diamond

variable {D E : ℕ}

/-- A complex-linear map from operators in dimension `D` to operators in dimension `E`. -/
abbrev Superoperator (D E : ℕ) := Operator D →ₗ[ℂ] Operator E

/-- A representation of a superoperator as a sum of `D * D * E * E` terms of the form `(A j)ᴴ *
X * B j`. -/
structure CbFactorization (T : Superoperator D E) where
  A : Fin (D * D * E * E) → Matrix (Fin D) (Fin E) ℂ
  B : Fin (D * D * E * E) → Matrix (Fin D) (Fin E) ℂ
  repr : ∀ X : Operator D, T X = ∑ j, (A j)ᴴ * X * (B j)

/-- The product of the square roots of the summed real traces of `(A j)ᴴ * A j` and `(B j)ᴴ * B
j` for a superoperator factorization. -/
noncomputable def cbFactorizationNorm {D E : ℕ} {T : Superoperator D E}
    (F : CbFactorization T) : ℝ :=
  Real.sqrt (∑ j, ((F.A j)ᴴ * (F.A j)).trace.re) *
    Real.sqrt (∑ j, ((F.B j)ᴴ * (F.B j)).trace.re)

/-- The extended nonnegative real infimum of `cbFactorizationNorm` over all factorizations of
the superoperator. -/
noncomputable def cbNormDual (T : Superoperator D E) : ℝ≥0∞ :=
  ⨅ F : CbFactorization T, ENNReal.ofReal (cbFactorizationNorm F)

/-- The superoperator possesses a factorization with strictly positive `cbFactorizationNorm`. -/
def CbStrictlyFeasible (T : Superoperator D E) : Prop :=
  ∃ F : CbFactorization T, 0 < cbFactorizationNorm F

end Diamond

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
