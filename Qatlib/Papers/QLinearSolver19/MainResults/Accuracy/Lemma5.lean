/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Paper-layer formalisation: Lemma 5 of An–Lin, *Quantum Linear Solver with Time-dependent
Hamiltonian and its Applications* (arXiv:1909.05500v3, ACM TQC 3(2) Article 5, 2022).

Lemma 5 (paper page 5:15, equation (16)) states that the adiabatic infidelity, the squared
fidelity loss and the squared 2-norm of the density-matrix error all agree, and derives the
fidelity / density-error bounds from a bound on the adiabatic error.

The paper's equation (16) is an identity between
* `1 - ⟨ψ_T(s)|P₀(s)|ψ_T(s)⟩`,
* `1 - |⟨ψ_T(s)|x̃(s)⟩|²`, and
* `‖ |ψ_T(s)⟩⟨ψ_T(s)| - |x̃(s)⟩⟨x̃(s)| ‖₂²`,

where `P₀(s) = |x̃(s)⟩⟨x̃(s)| + |b̄⟩⟨b̄|` is the ground-space projector (page 5:15, proof of
Lemma 5) and `⟨b̄|ψ_T(s)⟩ = 0` holds throughout the evolution.  We model the Hilbert space by
an arbitrary complex inner-product space, `|v⟩⟨v|` by `InnerProductSpace.rankOne ℂ v v`, and
`P₀(s)` by `densityMat x + densityMat b`, with `b` the (unit) vector `|b̄⟩` orthogonal to `ψ`.

The proof of the second equality follows the paper: with `M = |ψ⟩⟨ψ| - |x̃⟩⟨x̃|`, one studies
`M†M`; on `span{ψ, x̃}` it acts as `1 - |⟨ψ|x̃⟩|²`, and it vanishes on the orthogonal complement,
so `‖M‖₂² = 1 - |⟨ψ|x̃⟩|²`.  We formalise this as `densityMat_sub_norm_sq`.
-/

/-!
# Lemma5

Paper-specific definitions and results for QLinearSolver19.
-/

set_option backward.isDefEq.respectTransparency false

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace Qatlib.Papers.QLinearSolver19.MainResults.Accuracy

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The rank-one density matrix `|v⟩⟨v|` attached to a state vector `v`
(paper notation `|v⟩⟨v|`).  Defined as `InnerProductSpace.rankOne ℂ v v`. -/
noncomputable def densityMat (v : E) : E →L[ℂ] E := InnerProductSpace.rankOne ℂ v v

/-- `|v⟩⟨v| w = ⟪v, w⟫ • v`. -/
lemma densityMat_apply (v w : E) : densityMat v w = ⟪v, w⟫_ℂ • v := by
  simp [densityMat, InnerProductSpace.rankOne_apply]

/-- For a unit vector `v`, `|v⟩⟨v| v = v`. -/
lemma densityMat_apply_self_of_norm_one (v : E) (hv : ‖v‖ = 1) :
    densityMat v v = v := by
  rw [densityMat_apply, inner_self_eq_norm_sq_to_K, hv]
  simp

/-- `|v⟩⟨v|` is self-adjoint (paper: `|v⟩⟨v|† = |v⟩⟨v|`). -/
lemma densityMat_adjoint (v : E) :
    ContinuousLinearMap.adjoint (densityMat v) = densityMat v := by
  simp [densityMat, InnerProductSpace.adjoint_rankOne]

/-- The key operator identity behind Lemma 5 (paper page 5:15, proof of equation (16)):
for unit vectors `ψ`, `x`, the squared operator norm of `|ψ⟩⟨ψ| - |x⟩⟨x|` equals
`1 - |⟨ψ|x⟩|²`. -/
theorem densityMat_sub_norm_sq (ψ x : E) (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1) :
    ‖densityMat ψ - densityMat x‖ ^ 2 = 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 := by
  -- `c * conj c = |c|²` for the overlap `c = ⟪x, ψ⟫`.
  have hcc : ⟪x, ψ⟫_ℂ * star ⟪x, ψ⟫_ℂ = ((‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- Cauchy–Schwarz gives `|c| ≤ 1`.
  have hcs : ‖⟪x, ψ⟫_ℂ‖ ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) x ψ
    rw [hx, hψ, mul_one] at h
    exact h
  have hr : (0 : ℝ) ≤ 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 := by
    nlinarith [norm_nonneg ⟪x, ψ⟫_ℂ]
  -- The difference operator `M = |ψ⟩⟨ψ| - |x⟩⟨x|`.
  let M : E →L[ℂ] E := densityMat ψ - densityMat x
  have hMψ : M ψ = ψ - ⟪x, ψ⟫_ℂ • x := by
    simp [M, densityMat, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hψ]
  have hψx : ⟪ψ, x⟫_ℂ = star ⟪x, ψ⟫_ℂ := by
    simpa using congrArg star (inner_conj_symm x ψ)
  have hMx : M x = star ⟪x, ψ⟫_ℂ • ψ - x := by
    simp only [M, densityMat, ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hx, hψx, RCLike.ofReal_one, Complex.ofReal_one, one_pow, one_smul]
  -- The two-dimensional subspace `span{ψ, x}`.
  let K : Submodule ℂ E := Submodule.span ℂ ({ψ, x} : Set E)
  have hψK : ψ ∈ K := Submodule.subset_span (by simp)
  have hxK : x ∈ K := Submodule.subset_span (by simp)
  haveI : FiniteDimensional ℂ K :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton x).insert ψ)
  haveI : CompleteSpace K := FiniteDimensional.complete ℂ K
  -- `M` is self-adjoint.
  have hMadj : ContinuousLinearMap.adjoint M = M := by
    simp [M, densityMat, InnerProductSpace.adjoint_rankOne]
  -- `M†M = M²` acts as `1 - |c|²` on `span{ψ, x}`.
  have hM2 : ∀ u ∈ K, M (M u) = ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) • u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · subst y
        calc M (M ψ) = M (ψ - ⟪x, ψ⟫_ℂ • x) := by rw [hMψ]
          _ = M ψ - ⟪x, ψ⟫_ℂ • M x := by rw [map_sub, map_smul]
          _ = (ψ - ⟪x, ψ⟫_ℂ • x) - ⟪x, ψ⟫_ℂ • (star ⟪x, ψ⟫_ℂ • ψ - x) := by
              rw [hMψ, hMx]
          _ = ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) • ψ := by
              rw [smul_sub, smul_smul, hcc]
              module
      · subst y
        calc M (M x) = M (star ⟪x, ψ⟫_ℂ • ψ - x) := by rw [hMx]
          _ = star ⟪x, ψ⟫_ℂ • M ψ - M x := by rw [map_sub, map_smul]
          _ = star ⟪x, ψ⟫_ℂ • (ψ - ⟪x, ψ⟫_ℂ • x) - (star ⟪x, ψ⟫_ℂ • ψ - x) := by
              rw [hMx, hMψ]
          _ = ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) • x := by
              rw [smul_sub, smul_smul]
              have hc' : star ⟪x, ψ⟫_ℂ * ⟪x, ψ⟫_ℂ = ((‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
                rw [mul_comm, hcc]
              rw [hc']
              module
    · simp
    · intro u v _ _ hu hv
      rw [map_add, map_add, hu, hv, smul_add]
    · intro a u _ hu
      simp only [map_smul, hu]
      rw [smul_comm]
  -- Hence `‖M u‖² = (1 - |c|²) ‖u‖²` for `u ∈ span{ψ, x}`.
  have hkey : ∀ u ∈ K, ‖M u‖ ^ 2 = (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) * ‖u‖ ^ 2 := by
    intro u hu
    have hinnerM : ⟪M u, M u⟫_ℂ =
        ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right M u (M u), hMadj, hM2 u hu,
        inner_smul_right]
    have hsq : ((‖M u‖ ^ 2 : ℝ) : ℂ) =
        (((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by
      calc ((‖M u‖ ^ 2 : ℝ) : ℂ) = ⟪M u, M u⟫_ℂ := by
              rw [inner_self_eq_norm_sq_to_K]; push_cast; first | rfl | ring
        _ = ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := hinnerM
        _ = (((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) * ‖u‖ ^ 2 : ℝ) : ℂ) := by
              rw [inner_self_eq_norm_sq_to_K]; push_cast; first | rfl | ring
    exact Complex.ofReal_inj.mp hsq
  have hnorm : ∀ u ∈ K, ‖M u‖ = Real.sqrt (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) * ‖u‖ := by
    intro u hu
    rw [← Real.sqrt_sq (norm_nonneg (M u)), hkey u hu, Real.sqrt_mul hr,
      Real.sqrt_sq (norm_nonneg u)]
  -- Upper bound for the operator norm: `M` vanishes on `Kᗮ`.
  have hop : ‖M‖ ≤ Real.sqrt (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound M (Real.sqrt_nonneg _) (fun v => ?_)
    have hzero : M (v - K.starProjection v) = 0 := by
      have hψv : ⟪ψ, v - K.starProjection v⟫_ℂ = 0 := by
        have h1 : ⟪v - K.starProjection v, ψ⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal' K (v - K.starProjection v)).1
            (Submodule.sub_starProjection_mem_orthogonal (K := K) v) ψ hψK
        exact inner_eq_zero_symm.1 h1
      have hxv : ⟪x, v - K.starProjection v⟫_ℂ = 0 := by
        have h1 : ⟪v - K.starProjection v, x⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal' K (v - K.starProjection v)).1
            (Submodule.sub_starProjection_mem_orthogonal (K := K) v) x hxK
        exact inner_eq_zero_symm.1 h1
      have hPψ : densityMat ψ (v - K.starProjection v) = 0 := by
        rw [densityMat_apply, hψv, zero_smul]
      have hPx : densityMat x (v - K.starProjection v) = 0 := by
        rw [densityMat_apply, hxv, zero_smul]
      simp [M, hPψ, hPx]
    have hEq : M v = M (K.starProjection v) := by
      conv_lhs =>
        rw [show v = K.starProjection v + (v - K.starProjection v) from by abel]
      rw [map_add, hzero, add_zero]
    rw [hEq, hnorm (K.starProjection v) (Submodule.starProjection_apply_mem K v)]
    exact mul_le_mul_of_nonneg_left (Submodule.norm_starProjection_apply_le (K := K) v)
      (Real.sqrt_nonneg _)
  -- Lower bound: test against `ψ`.
  have hlow : Real.sqrt (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) ≤ ‖M‖ := by
    have h1 : ‖M ψ‖ ≤ ‖M‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm M ψ
    rw [hψ, mul_one] at h1
    have h2 : ‖M ψ‖ = Real.sqrt (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) := by
      rw [hnorm ψ hψK, hψ, mul_one]
    linarith [h1, h2]
  have hMnorm : ‖M‖ = Real.sqrt (1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2) := le_antisymm hop hlow
  change ‖M‖ ^ 2 = 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2
  rw [hMnorm, Real.sq_sqrt hr]

/-- Lemma 5(i), first equality (paper page 5:15, equation (16)): for unit `ψ`, `x`, and the
ground-space projector `P₀ = |x⟩⟨x| + |b⟩⟨b|` with `⟪b, ψ⟫ = 0`, the adiabatic infidelity equals
`1 - |⟨ψ|x⟩|²`. -/
theorem lemma5_infidelity_eq (ψ x b : E) (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1)
    (hbψ : ⟪b, ψ⟫_ℂ = 0) :
    ‖(1 : ℂ) - ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ‖ = 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 := by
  have hxψ : ⟪ψ, x⟫_ℂ = star ⟪x, ψ⟫_ℂ := by
    simpa using congrArg star (inner_conj_symm x ψ)
  have hinner : ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ =
      ((‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.add_apply, inner_add_right, densityMat_apply, densityMat_apply,
      inner_smul_right, inner_smul_right, hbψ, zero_mul, add_zero, hxψ]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcs : ‖⟪x, ψ⟫_ℂ‖ ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℂ) x ψ
    rw [hx, hψ, mul_one] at h
    exact h
  rw [hinner]
  have hnum : (1 : ℂ) - ((‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ((1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hnum, Complex.norm_real, Real.norm_of_nonneg]
  nlinarith [norm_nonneg ⟪x, ψ⟫_ℂ]

/-- Lemma 5(i), combined statement (paper page 5:15, equation (16)): the infidelity equals
`1 - |⟨ψ|x⟩|²`, which in turn equals the squared 2-norm of the density-matrix error. -/
theorem lemma5_part_i (ψ x b : E) (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1)
    (hbψ : ⟪b, ψ⟫_ℂ = 0) :
    ‖(1 : ℂ) - ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ‖ = 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 ∧
      1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 = ‖densityMat ψ - densityMat x‖ ^ 2 :=
  ⟨lemma5_infidelity_eq ψ x b hψ hx hbψ,
    (densityMat_sub_norm_sq ψ x hψ hx).symm⟩

/-- Lemma 5(ii) (paper page 5:15): if the adiabatic infidelity is at most `η²`, then the fidelity
`|⟨ψ|x⟩|²` is at least `1 - η²` and the density-matrix 2-norm error is at most `η`. -/
theorem lemma5_part_ii (ψ x b : E) (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1)
    (hbψ : ⟪b, ψ⟫_ℂ = 0) {η : ℝ} (hη : 0 ≤ η)
    (h : ‖(1 : ℂ) - ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ‖ ≤ η ^ 2) :
    1 - η ^ 2 ≤ ‖⟪x, ψ⟫_ℂ‖ ^ 2 ∧ ‖densityMat ψ - densityMat x‖ ≤ η := by
  have h1 := lemma5_infidelity_eq ψ x b hψ hx hbψ
  have h2 := densityMat_sub_norm_sq ψ x hψ hx
  have hinf : 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 ≤ η ^ 2 := by
    rw [← h1]
    exact h
  constructor
  · linarith
  · have hsq : ‖densityMat ψ - densityMat x‖ ^ 2 ≤ η ^ 2 := by
      rw [h2]
      exact hinf
    calc ‖densityMat ψ - densityMat x‖
        = Real.sqrt (‖densityMat ψ - densityMat x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (η ^ 2) := Real.sqrt_le_sqrt hsq
      _ = η := Real.sqrt_sq hη

/-- Lemma 5 of An–Lin (arXiv:1909.05500v3, page 5:15, equation (16)), in full: (i) the identity
`|1 - ⟨ψ|P₀|ψ⟩| = 1 - |⟨ψ|x⟩|² = ‖|ψ⟩⟨ψ| - |x⟩⟨x|‖₂²`, and (ii) the fidelity lower bound and
density-matrix 2-norm error bound derived from `|1 - ⟨ψ|P₀|ψ⟩| ≤ η²`. -/
theorem lemma5 (ψ x b : E) (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1) (hbψ : ⟪b, ψ⟫_ℂ = 0) :
    (‖(1 : ℂ) - ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ‖ = 1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 ∧
        1 - ‖⟪x, ψ⟫_ℂ‖ ^ 2 = ‖densityMat ψ - densityMat x‖ ^ 2) ∧
      (∀ η : ℝ, 0 ≤ η →
        ‖(1 : ℂ) - ⟪ψ, (densityMat x + densityMat b) ψ⟫_ℂ‖ ≤ η ^ 2 →
        1 - η ^ 2 ≤ ‖⟪x, ψ⟫_ℂ‖ ^ 2 ∧ ‖densityMat ψ - densityMat x‖ ≤ η) :=
  ⟨lemma5_part_i ψ x b hψ hx hbψ, fun η hη h => lemma5_part_ii ψ x b hψ hx hbψ hη h⟩

end Qatlib.Papers.QLinearSolver19.MainResults.Accuracy
