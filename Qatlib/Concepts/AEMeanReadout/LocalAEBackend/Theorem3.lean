/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2Stat

/-!
# Recursive amplification search specification

`Theorem3` specifies recursive amplitude amplification using approximate reflections on an
invariant subspace. Its hypotheses control reflection errors and costs, and its conclusions give
marked-mass guarantees and an explicit inverse-square-root search-cost bound in the framework of
[MagniezNayakRolandSantha2011].

## Main statements

* `Theorem3`: the approximate-reflection search and cost contract.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

open Qatlib.Concepts.WalkSearch.MnrsAmplify

open scoped Real

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

/-- Specifies recursive amplification with controlled reflection errors: zero marked mass gives
zero success, nonzero marked mass gives success at least `1/24`, and the accumulated costs
satisfy the stated geometric and inverse-square-root bounds. -/
def Theorem3 : Prop :=
  ∀ (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (Mr : Submodule ℂ W) (unmarkRefl : W ≃ₗᵢ[ℂ] W),
    (∀ z ∈ Mr, unmarkRefl z = -z) →
    (∀ z ∈ Mrᗮ, unmarkRefl z = z) →
    ∀ (x₀ : W), ‖x₀‖ = 1 →
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
        ≤ betaAt (1 / 72) i * ‖ψ‖) →
    (∀ i, 1 ≤ i → i ≤ Nat.max tMax 1 →
      costR i ≤ c₁ * Real.log (1 / betaAt (1 / 72) i)) →
    costMark ≤ c₂ →
    3 ^ tMax * Real.arcsin (Real.sqrt ε) ∈ Set.Icc (π / 4) (3 * π / 4) →
    (∀ j, j < tMax →
      3 ^ j * Real.arcsin (Real.sqrt ε) ∉ Set.Icc (π / 4) (3 * π / 4)) →
    (markedMass Mr x₀ = 0 →
      tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1) = 0) ∧
    (markedMass Mr x₀ ≠ 0 →
      1 / 24 ≤ tolerantSuccess Mr (raaUnitary unmarkRefl R) x₀ (Nat.max tMax 1)) ∧
    (∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
      2 * 3 ^ tMax * (c₁ * (Real.log 72 + 3) + c₂)) ∧
    (∀ (U C δ : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ C →
      c₁ ≤ 2 * U / Real.sqrt δ → c₂ ≤ C →
      ∑ i ∈ Finset.Icc 1 (Nat.max tMax 1), raaCost costR costMark i ≤
        99 * (1 / Real.sqrt ε) * ((1 / Real.sqrt δ) * U + C))

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
