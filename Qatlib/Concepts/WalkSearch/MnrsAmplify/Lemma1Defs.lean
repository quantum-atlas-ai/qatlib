/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.InnerProductSpace.l2Space

open scoped Real

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

noncomputable def lineProj (u : W) : W →L[ℂ] W :=
  (Submodule.subtypeL (Submodule.span ℂ {u})).comp
    (Submodule.orthogonalProjection (Submodule.span ℂ {u}))

noncomputable def markProj (M : Submodule ℂ W) : W →L[ℂ] W :=
  M.subtypeL.comp M.orthogonalProjection

noncomputable def markedMass (M : Submodule ℂ W) (x₀ : W) : ℝ :=
  ‖markProj M x₀‖ ^ 2

noncomputable def betaAt (γ : ℝ) (i : ℕ) : ℝ :=
  18 / (4 * Real.pi ^ 3) * γ / (i : ℝ) ^ 2

def raaUnitary (unmarkRefl : W ≃ₗᵢ[ℂ] W) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) : ℕ → (W ≃ₗᵢ[ℂ] W)
  | 0 => LinearIsometryEquiv.refl ℂ W
  | i + 1 => ((raaUnitary unmarkRefl R i).trans unmarkRefl).trans (R (i + 1))

def raaState (unmarkRefl : W ≃ₗᵢ[ℂ] W) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (x₀ : W) (i : ℕ) : W :=
  (raaUnitary unmarkRefl R i) x₀

noncomputable def raaCost (costR : ℕ → ℝ) (costMark : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => 3 * raaCost costR costMark i + costR (i + 1) + costMark
end Qatlib.Concepts.WalkSearch.MnrsAmplify
