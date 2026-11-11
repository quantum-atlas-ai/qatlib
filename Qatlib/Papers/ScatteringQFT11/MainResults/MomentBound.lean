/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ScatteringQFT11.MainResults.ExpectationCore

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2: the moment bound `|⟨ψ|M|ψ⟩| ≤ √⟨ψ|M²|ψ⟩`

Jordan–Lee–Preskill, *Quantum Computation of Scattering in Scalar Quantum Field
Theories* (arXiv:1112.4833v1), Proposition 2 (p. 22) states: for a Hermitian
operator `M` and a unit-norm state `|ψ⟩`,

`|⟨ψ|M|ψ⟩| ≤ √⟨ψ|M²|ψ⟩`.

The paper proves it from positivity of `(M − ⟨M⟩𝟙)²`, giving
`0 ≤ ⟨M²⟩ − ⟨M⟩²`. Here the same inequality is proved through the Hilbert-space
Cauchy–Schwarz inequality on the `EuclideanSpace` model of the state, transported
back to the library's `Inner` by `inner_euclidean_fromVec`; both routes give the
same proposition.

The final section records the consequence used in the proof of Proposition 4:
applying the bound to `M = φ(x)²` gives `⟨φ(x)²⟩² ≤ ⟨φ(x)⁴⟩`.
-/

namespace Qatlib.Papers.ScatteringQFT11.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Proposition 2** (p. 22): for a Hermitian observable `M` and a state of unit
norm, `|⟨ψ|M|ψ⟩| ≤ √⟨ψ|M²|ψ⟩`, in the form of the complex modulus of the
expectation bounded by the square root of the expectation of `M²`. -/
theorem abs_inner_le_sqrt_inner_sq (M : Matrix n n ℂ) (ψ : QState n)
    (hM : Mᴴ = M) (hψ : Normalized ψ) :
    ‖stateInner ψ (M *ᵥ ψ)‖ ≤ Real.sqrt (expectation (M * M) ψ) := by
  have hψ1 : ‖toEuclidean_fromVec ψ‖ = 1 := by
    have h : ‖toEuclidean_fromVec ψ‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_sq_eq_re_inner, (normalized_iff_inner_self ψ).mp hψ]
      simp
    nlinarith [norm_nonneg (toEuclidean_fromVec ψ)]
  have hnorm : ‖toEuclidean_fromVec (M *ᵥ ψ)‖ ^ 2 = expectation (M * M) ψ := by
    rw [norm_toEuclidean_sq_eq_re_inner, expectation, stateInner]
    congr 1
    rw [Qatlib.Foundations.PureStateMath.inner_mulVec_left_rect M ψ (M *ᵥ ψ),
      ← Matrix.mulVec_mulVec, hM]
  have hcs : ‖stateInner ψ (M *ᵥ ψ)‖
      ≤ ‖toEuclidean_fromVec ψ‖ * ‖toEuclidean_fromVec (M *ᵥ ψ)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec ψ) (toEuclidean_fromVec (M *ᵥ ψ))
    rwa [inner_euclidean_fromVec] at h
  calc ‖stateInner ψ (M *ᵥ ψ)‖
      ≤ ‖toEuclidean_fromVec ψ‖ * ‖toEuclidean_fromVec (M *ᵥ ψ)‖ := hcs
    _ = ‖toEuclidean_fromVec (M *ᵥ ψ)‖ := by rw [hψ1, one_mul]
    _ = Real.sqrt (‖toEuclidean_fromVec (M *ᵥ ψ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (expectation (M * M) ψ) := by rw [hnorm]

/-- **Proposition 2** (p. 22) in the paper's real form:
`|⟨ψ|M|ψ⟩| ≤ √⟨ψ|M²|ψ⟩` for Hermitian `M` and a unit-norm state. -/
theorem abs_expectation_le_sqrt_expectation_sq (M : Matrix n n ℂ) (ψ : QState n)
    (hM : Mᴴ = M) (hψ : Normalized ψ) :
    |expectation M ψ| ≤ Real.sqrt (expectation (M * M) ψ) := by
  rw [abs_expectation_eq_norm hM ψ]
  exact abs_inner_le_sqrt_inner_sq M ψ hM hψ

/-- The consequence of Proposition 2 used in the proof of Proposition 4 (p. 23):
applying the bound to the Hermitian operator `φ(x)²` yields
`⟨φ(x)²⟩² ≤ ⟨φ(x)⁴⟩`. -/
theorem expectation_sq_le_expectation_pow_four (A : Matrix n n ℂ) (ψ : QState n)
    (hA : Aᴴ = A) (hψ : Normalized ψ) :
    expectation (A * A) ψ ^ 2 ≤ expectation (A ^ 4) ψ := by
  have hA2 : (A * A)ᴴ = A * A := by
    rw [Matrix.conjTranspose_mul, hA]
  have hsq : (A * A) * (A * A) = A ^ 4 := by noncomm_ring
  have hbound := abs_expectation_le_sqrt_expectation_sq (A * A) ψ hA2 hψ
  have hnn : 0 ≤ expectation (A * A) ψ := expectation_sq_nonneg hA ψ
  have hsq_le : expectation (A * A) ψ ^ 2
      ≤ Real.sqrt (expectation ((A * A) * (A * A)) ψ) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mpr hbound
    rwa [sq_abs] at this
  rwa [Real.sq_sqrt (expectation_sq_nonneg hA2 ψ), hsq] at hsq_le

end Qatlib.Papers.ScatteringQFT11.MainResults
