/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
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

noncomputable def schatten (p : ℝ) (A : Matrix n n ℂ) : ℝ :=
  (∑ i, (singularValues A i) ^ p) ^ (p⁻¹)

theorem schatten_one_eq_traceNorm (A : Matrix n n ℂ) :
    schatten 1 A = A.traceNorm := by
  simp [schatten, Matrix.traceNorm_eq_sum_singularValues]

section Top

variable {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]

open scoped Matrix.Norms.L2Operator

noncomputable def schattenTop (A : Matrix m k ℂ) : ℝ := ‖A‖

end Top

noncomputable def schattenDual (p q : ℝ) (A : Matrix n n ℂ) : ℝ :=
  sSup {r | 1 < p ∧ p⁻¹ + q⁻¹ = 1 ∧ ∃ B : Matrix n n ℂ,
    schatten q B ≤ 1 ∧ r = ‖Matrix.trace (Bᴴ * A)‖}

end Schatten

section Diamond

variable {D E : ℕ}

abbrev Superoperator (D E : ℕ) := Operator D →ₗ[ℂ] Operator E

structure CbFactorization (T : Superoperator D E) where
  A : Fin (D * D * E * E) → Matrix (Fin D) (Fin E) ℂ
  B : Fin (D * D * E * E) → Matrix (Fin D) (Fin E) ℂ
  repr : ∀ X : Operator D, T X = ∑ j, (A j)ᴴ * X * (B j)

noncomputable def cbFactorizationNorm {D E : ℕ} {T : Superoperator D E}
    (F : CbFactorization T) : ℝ :=
  Real.sqrt (∑ j, ((F.A j)ᴴ * (F.A j)).trace.re) *
    Real.sqrt (∑ j, ((F.B j)ᴴ * (F.B j)).trace.re)

noncomputable def cbNormDual (T : Superoperator D E) : ℝ≥0∞ :=
  ⨅ F : CbFactorization T, ENNReal.ofReal (cbFactorizationNorm F)

def CbStrictlyFeasible (T : Superoperator D E) : Prop :=
  ∃ F : CbFactorization T, 0 < cbFactorizationNorm F

end Diamond

end Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
