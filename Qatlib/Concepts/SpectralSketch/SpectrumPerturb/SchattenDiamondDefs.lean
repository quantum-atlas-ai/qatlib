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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false

variable {m k : Type} [Fintype m] [Fintype k]

abbrev SchattenExponent := WithTop ℝ

noncomputable def schattenPower (p : ℝ) (A : Matrix m k ℂ) : ℝ :=
  let hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  (∑ i : k, (Real.sqrt (hH.eigenvalues i)) ^ p) ^ (p⁻¹)

noncomputable def schattenUnified (p : SchattenExponent) (A : Matrix m k ℂ) : ℝ :=
  match p with
  | .none => Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schattenTop A
  | .some q => schattenPower q A

noncomputable def diamondNorm {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm T

noncomputable def diamondError {D E : ℕ}
    (T S : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondDistance T S

noncomputable def diamondHermitianNorm {D E : ℕ}
    (T : Operator D →ₗ[ℂ] Operator E) : ℝ≥0∞ :=
  ⨆ r : ℕ, ⨆ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
    if X.IsHermitian ∧ Matrix.traceNorm X ≤ 1 then
      ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) else 0

noncomputable def cbFactorizationObjective {D E : ℕ} {T : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Superoperator D E}
    (F : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.CbFactorization T) : ℝ :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbFactorizationNorm F

noncomputable def cbPrimalValue {D E : ℕ} (T : Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.Superoperator D E) : ℝ≥0∞ :=
  Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.cbNormDual T

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
