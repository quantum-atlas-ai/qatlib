/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyNonlin25 — Kolmogorov-equation operator model

Fixed source: arXiv:2507.06198 (*Quantum simulation of a noisy classical nonlinear
dynamics*).

This file provides the paper-layer abstraction used by every claim in
`NoisyNonlin25.MainResults`.  The paper works on the Fock space `𝓕` of `N` bosonic modes and
its vacuum-orthogonal subspace `𝓕₀` (`|ψ⟩ ∈ 𝓕` with `⟨0|ψ⟩ = 0`, Eq. (23)).  The second
quantized Kolmogorov equation is `d/dt |ψ(t)⟩ = (−A + B + C)|ψ(t)⟩` (Eq. (19)) with

* `A = ∑ᵢ λᵢ aᵢ† aᵢ` (Eq. (20)), hermitian and positive semi-definite with spectral gap
  `⟨ψ|A|ψ⟩ ≥ λ₁‖ψ‖²` on `𝓕₀` (Section 2.1),
* `B = ∑ᵢⱼ bᵢⱼ (λᵢ/λⱼ)^{1/2} aⱼ† aᵢ` (Eq. (20)), skew-hermitian when the ODE is
  divergence-free (Lemma 1),
* `C` the cubic operator of Eq. (22), skew-hermitian.

All analytic content (the Fock basis, ladder operators, the infinite-dimensional limit) is
kept implicit: the model records exactly the operator-level structural facts that the paper
establishes or assumes before each result.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ComplexOrder InnerProduct
open Finset

namespace Qatlib.Papers.NoisyNonlin25.MainResults

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `⟨ψ|T|ψ⟩ = re ⟪ψ, T ψ⟫`, the real expectation of an operator in state `ψ`. -/
def expect (T : H →L[ℂ] H) (ψ : H) : ℝ := (inner ℂ ψ (T ψ)).re

/-- `⟨φ|T|ψ⟩ = ⟪φ, T ψ⟫`, the complex matrix element of `T`. -/
def matrixElement (T : H →L[ℂ] H) (φ ψ : H) : ℂ := inner ℂ φ (T ψ)

/-- The operator model of the paper's Fock-space setting.

`lam1` is `λ₁ = minᵢ λᵢ` (the spectral gap of `A` on `𝓕₀`, Section 2.1); `A_self`/`A_pos`
record that `A` is hermitian positive semi-definite; `B_anti`/`C_anti` record the
skew-hermitian structure of Lemma 1 (established there from the divergence-free condition);
`gap` is the lower spectral bound `⟨ψ|A|ψ⟩ ≥ λ₁‖ψ‖²` for `ψ ∈ 𝓕₀`. -/
structure KolmogorovModel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The noise/dissipation operator `A` of Eq. (20). -/
  A : H →L[ℂ] H
  /-- The linear drift operator `B` of Eq. (20). -/
  B : H →L[ℂ] H
  /-- The quadratic drift operator `C` of Eq. (22). -/
  C : H →L[ℂ] H
  /-- `λ₁`, the smallest dissipation rate / spectral gap of `A`. -/
  lam1 : ℝ
  lam1_pos : 0 < lam1
  A_self : IsSelfAdjoint A
  A_pos : ContinuousLinearMap.IsPositive A
  B_anti : B† = -B
  C_anti : C† = -C
  /-- Spectral gap: `⟨ψ|A|ψ⟩ ≥ λ₁‖ψ‖²` (Section 2.1). -/
  gap : ∀ ψ : H, lam1 * ‖ψ‖ ^ 2 ≤ expect A ψ

namespace KolmogorovModel

variable (M : KolmogorovModel H)

/-- `⟨ψ|A|ψ⟩ ≥ 0`: `A` is positive semi-definite. -/
theorem expect_A_nonneg (ψ : H) : 0 ≤ expect M.A ψ :=
  M.A_pos.re_inner_nonneg_right ψ

/-- The spectral gap in the form `λ₁‖ψ‖² ≤ ⟨ψ|A|ψ⟩`. -/
theorem gap_le (ψ : H) : M.lam1 * ‖ψ‖ ^ 2 ≤ expect M.A ψ := M.gap ψ

/-- `⟨ψ|A²|ψ⟩ ≥ 0`: `A²` is positive semi-definite. -/
theorem expect_A_sq_nonneg (ψ : H) : 0 ≤ expect (M.A * M.A) ψ := by
  rw [expect]
  have h1 : inner ℂ ψ ((M.A * M.A) ψ) = inner ℂ (M.A ψ) (M.A ψ) := by
    rw [ContinuousLinearMap.mul_apply]
    exact (M.A_pos.inner_left_eq_inner_right ψ (M.A ψ)).symm
  rw [h1]
  exact inner_self_nonneg (𝕜 := ℂ) (x := M.A ψ)

end KolmogorovModel

end Qatlib.Papers.NoisyNonlin25.MainResults
