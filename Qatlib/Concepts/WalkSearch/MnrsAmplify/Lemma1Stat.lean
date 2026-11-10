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
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Defs

open scoped Real

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

section Schedule

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

end Schedule

def Lemma1 : Prop :=
  ∀ (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W),

    (∀ z ∈ Mr, unmarkRefl z = -z) →
    (∀ z ∈ Mrᗮ, unmarkRefl z = z) →
    ∀ (x₀ : W), ‖x₀‖ = 1 →
    ∀ (γ : ℝ), 0 < γ → γ ≤ 1 →
    ∀ (t : ℕ) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (c₁ c₂ : ℝ), 0 ≤ c₁ → 0 ≤ c₂ →
    ∀ (costR : ℕ → ℝ) (costMark : ℝ),
    ∀ (Rs : Submodule ℂ W),

    x₀ ∈ Rs →
    (∀ z ∈ Rs, markProj Mr z ∈ Rs) →
    (∀ i, 1 ≤ i → i ≤ t → ∀ z ∈ Rs, R i z ∈ Rs) →

    (∀ i, 1 ≤ i → i ≤ t →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1)) →

    (∀ i, 1 ≤ i → i ≤ t → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt γ i * ‖ψ‖) →

    (∀ i, 1 ≤ i → i ≤ t → costR i ≤ c₁ * Real.log (1 / betaAt γ i)) →
    costMark ≤ c₂ →

    3 ^ t * Real.arcsin (Real.sqrt (markedMass Mr x₀)) ∈ Set.Icc (π / 4) (3 * π / 4) →
    (∀ j, j < t →
      3 ^ j * Real.arcsin (Real.sqrt (markedMass Mr x₀)) ∉ Set.Icc (π / 4) (3 * π / 4)) →

    (1 / Real.sqrt 2 - γ ≤ ‖markProj Mr (raaState unmarkRefl R x₀ t)‖) ∧
    (raaCost costR costMark t ≤ 3 ^ t * (c₁ * (Real.log (1 / γ) + 3) + c₂))

end Qatlib.Concepts.WalkSearch.MnrsAmplify
