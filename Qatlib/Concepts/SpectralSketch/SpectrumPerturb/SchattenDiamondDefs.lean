/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.SchattenDiamondDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Schatten and diamond norm interfaces

This module defines a unified real-or-infinite Schatten exponent interface and aliases for
finite dimensional diamond norms and distances. It also provides Hermitian-input and completely
bounded factorization interfaces used in later norm estimates; see [Watrous2018] for the quantum
information setting.

## Main statements

* `schattenUnified`: combines finite Schatten expressions with the operator norm endpoint.
* `diamondNorm` and `diamondError`: expose the stabilized norm and its half-distance
  normalization.
* `diamondHermitianNorm`: restricts amplified inputs to Hermitian matrices.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false

variable {m k : Type} [Fintype m] [Fintype k]

/-- The extended real exponent type `WithTop ℝ` used for finite Schatten exponents and the
operator norm endpoint. -/
abbrev SchattenExponent := WithTop ℝ

/-- The real expression obtained by taking the `p`-power sum of square roots of Gram eigenvalues
and raising it to `p⁻¹`. -/
noncomputable def schattenPower (p : ℝ) (A : Matrix m k ℂ) : ℝ :=
  let hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  (∑ i : k, (Real.sqrt (hH.eigenvalues i)) ^ p) ^ (p⁻¹)

/-- The Schatten expression at a finite exponent, or the imported operator norm endpoint at the
top exponent. -/
noncomputable def schattenUnified (p : SchattenExponent) (A : Matrix m k ℂ) : ℝ :=
  match p with
  | .none => Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schattenTop A
  | .some q => schattenPower q A

/-- The finite dimensional diamond norm of a complex linear map between matrix operator spaces. -/
noncomputable def diamondNorm {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm T

/-- The finite dimensional diamond distance between two complex linear maps, with the imported
half-norm normalization. -/
noncomputable def diamondError {D E : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondDistance T S

/-- The supremum of amplified output trace norms over Hermitian inputs of trace norm at most one
and all finite reference dimensions. -/
noncomputable def diamondHermitianNorm {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
    if X.IsHermitian ∧ Matrix.traceNorm X ≤ 1 then
      ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) else 0

/-- The imported completely bounded factorization norm objective of a factorization `F`. -/
noncomputable def cbFactorizationObjective {D E : ℕ} {T : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Superoperator D E}
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization T) : ℝ :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F

/-- The imported dual completely bounded norm value `cbNormDual T`. -/
noncomputable def cbPrimalValue {D E : ℕ} (T : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Superoperator D E) : ℝ≥0∞ :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual T

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
