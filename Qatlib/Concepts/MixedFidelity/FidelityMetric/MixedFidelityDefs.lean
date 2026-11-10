/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric

open Matrix
open scoped MatrixOrder ComplexOrder

variable {D E : ℕ}

noncomputable def Froot (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

theorem Froot_nonneg (ρ σ : Operator D) : 0 ≤ Froot ρ σ := by
  simp only [Froot]
  exact Matrix.traceNorm_nonneg _

noncomputable def traceDistance (ρ σ : Operator D) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

theorem traceDistance_nonneg (ρ σ : Operator D) : 0 ≤ traceDistance ρ σ := by
  simp only [traceDistance]
  exact div_nonneg (Matrix.traceNorm_nonneg _) zero_le_two

def IsPurification (ψ : QState (Fin D × Fin E)) (ρ : Operator D) : Prop :=
  Normalized ψ ∧ PartialTrace (outerProduct ψ) = ρ

def IsProbVector (p : Fin D → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def diagDensity (p : Fin D → ℝ) : Operator D :=
  Matrix.diagonal fun i => (p i : ℂ)

@[simp]
theorem diagDensity_apply (p : Fin D → ℝ) (i j : Fin D) :
    diagDensity p i j = if i = j then (p i : ℂ) else 0 := by
  simp [diagDensity, Matrix.diagonal_apply]

def CommutesToClassical (ρ σ : Operator D) : Prop :=
  ρ * σ = σ * ρ → ∃ (U : Matrix (Fin D) (Fin D) ℂ) (p q : Fin D → ℝ),
    U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ IsProbVector p ∧ IsProbVector q ∧
    U * ρ * Uᴴ = diagDensity p ∧ U * σ * Uᴴ = diagDensity q

end Qatlib.Concepts.MixedFidelity.FidelityMetric
