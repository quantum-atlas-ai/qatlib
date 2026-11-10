/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Stat
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2Defs

open scoped Real

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

section Tolerant

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

end Tolerant

def Lemma2 : Prop :=
  ∀ (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W),
    (∀ z ∈ Mr, unmarkRefl z = -z) →
    (∀ z ∈ Mrᗮ, unmarkRefl z = z) →
    ∀ (x₀ : W), ‖x₀‖ = 1 →
    ∀ (γ : ℝ), 0 < γ → γ ≤ 1 / 40 →
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    (markedMass Mr x₀ ≠ 0 → ε ≤ markedMass Mr x₀) →
    ∀ (tMax : ℕ) (R : ℕ → (W ≃ₗᵢ[ℂ] W)) (c₁ c₂ : ℝ), 0 ≤ c₁ → 0 ≤ c₂ →
    ∀ (costR : ℕ → ℝ) (costMark : ℝ),
    ∀ (Rs : Submodule ℂ W),

    x₀ ∈ Rs →
    (∀ z ∈ Rs, markProj Mr z ∈ Rs) →
    (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ z ∈ Rs, R i z ∈ Rs) →
    (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      R i (raaState unmarkRefl R x₀ (i - 1)) = raaState unmarkRefl R x₀ (i - 1)) →
    (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → ∀ ψ ∈ Rs,
      ψ ∈ (Submodule.span ℂ {raaState unmarkRefl R x₀ (i - 1)})ᗮ →
      ‖R i ψ + ψ - (2 : ℂ) • (lineProj (raaState unmarkRefl R x₀ (i - 1)) ψ)‖
        ≤ betaAt γ i * ‖ψ‖) →
    (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 → costR i ≤ c₁ * Real.log (1 / betaAt γ i)) →
    costMark ≤ c₂ →
    3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (π / 4) (3 * π / 4) →
    (∀ j, j < tMax →
      3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (π / 4) (3 * π / 4)) →
    (markedMass Mr x₀ ≠ 0 →
      1 / 12 - 3 * γ ≤
        tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1)) ∧
    (∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
      2 * 3 ^ tMax * (c₁ * (Real.log (1 / γ) + 3) + c₂))

end Qatlib.Concepts.WalkSearch.MnrsAmplify
