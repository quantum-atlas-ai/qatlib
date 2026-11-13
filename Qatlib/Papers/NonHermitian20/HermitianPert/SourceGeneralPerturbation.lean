/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Spectrum

set_option backward.isDefEq.respectTransparency false

/-!
# Stability of Hermitian spectra under general non-Hermitian perturbations

This file formalizes Theorem 2.4 (Eq. (46), p. 14) of [Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020]:
for an `n × n` Hermitian matrix `M` and an arbitrary (not necessarily Hermitian) perturbation
`E`, every eigenvalue `μ'` of `M + E` lies within L2 operator-norm distance `‖E‖` of some
eigenvalue `μ` of `M`:

  `min_j |μ' - λ_j| ≤ ‖E‖,   ∀ μ' ∈ Λ(M + E)`.

This is the unitary-diagonalizable (`cond(V) = 1`) specialization of the Bauer–Fike theorem,
proved here directly via Parseval's identity in `hM.eigenvectorBasis`.

## Main statements

* `theorem_2_4_general_perturbation`: every eigenvalue of `M + E` (with `M` Hermitian and `E`
  arbitrary) lies within L2 operator norm `‖E‖` of an eigenvalue of `M`.

## References

* [Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020]
-/

set_option autoImplicit false
noncomputable section

open Matrix Module
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonHermitian20.HermitianPert

/-- **Theorem 2.4** ([Ashida, Gong, and Ueda, 2020][AshidaGongUeda2020], Eq. (46), p. 14):
for a Hermitian matrix `M : Matrix ι ι ℂ` and any complex matrix `E`, every eigenvalue `mu'`
of `M + E` lies within L2 operator norm `‖E‖` of some eigenvalue `mu` of `M`. -/
theorem theorem_2_4_general_perturbation (ι : Type) [Fintype ι] [DecidableEq ι]
    (M E : Matrix ι ι ℂ) (hM : M.IsHermitian) :
    ∀ mu' : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (M + E)) mu' →
      ∃ mu : ℂ, Module.End.HasEigenvalue (Matrix.toLin' M) mu ∧ ‖mu' - mu‖ ≤ ‖E‖ := by
  intro mu' hmu'
  obtain ⟨v, hv_mem, hv_ne⟩ := (Submodule.ne_bot_iff _).mp hmu'
  have hv_eig : (M + E) *ᵥ v = mu' • v := Module.End.mem_eigenspace_iff.mp hv_mem
  have hv_res : (mu' • (1 : Matrix ι ι ℂ) - M) *ᵥ v = E *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hadd : M *ᵥ v + E *ᵥ v = mu' • v := by
      rwa [← Matrix.add_mulVec]
    exact (eq_sub_of_add_eq' hadd).symm
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv_ne
  have huniv : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
  let b := hM.eigenvectorBasis
  let ev := hM.eigenvalues
  obtain ⟨j₀, _, hj₀_min⟩ :=
    Finset.exists_min_image Finset.univ (fun j : ι => ‖mu' - (ev j : ℂ)‖) huniv
  have hj₀_eig : Module.End.HasEigenvalue (Matrix.toLin' M) (ev j₀ : ℂ) := by
    refine (Submodule.ne_bot_iff _).mpr ⟨(b j₀).ofLp, ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact hM.mulVec_eigenvectorBasis j₀
    · intro hzero
      have hb_norm : ‖b j₀‖ = 1 := b.orthonormal.1 j₀
      have hb_zero : b j₀ = 0 := by
        ext k
        exact congrFun hzero k
      rw [hb_zero, norm_zero] at hb_norm
      norm_num at hb_norm
  refine ⟨(ev j₀ : ℂ), hj₀_eig, ?_⟩
  let x : EuclideanSpace ℂ ι := WithLp.toLp 2 v
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hv_ne
    ext k
    exact congrFun (congrArg WithLp.ofLp hx0) k
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  let y : EuclideanSpace ℂ ι := (mu' • (1 : Matrix ι ι ℂ) - M).toEuclideanLin x
  have hy_eq : y = E.toEuclideanLin x := by
    ext k
    exact congrFun hv_res k
  have hy_norm_le : ‖y‖ ≤ ‖E‖ * ‖x‖ := by
    rw [hy_eq]
    exact Matrix.l2_opNorm_mulVec E x
  -- Compute coordinates of `y` in the orthonormal basis `b`.
  have hy_coord : ∀ j : ι, (b.repr y) j = (mu' - (ev j : ℂ)) * (b.repr x) j := by
    intro j
    rw [b.repr_apply_apply, b.repr_apply_apply]
    have hadj : inner ℂ (b j) ((mu' • (1 : Matrix ι ι ℂ) - M).toEuclideanLin x) =
        inner ℂ (((mu' • (1 : Matrix ι ι ℂ) - M)ᴴ).toEuclideanLin (b j)) x := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
    rw [hadj]
    have hvec : ((mu' • (1 : Matrix ι ι ℂ) - M)ᴴ).toEuclideanLin (b j) =
        (star mu' - (ev j : ℂ)) • b j := by
      have hconj : (mu' • (1 : Matrix ι ι ℂ) - M)ᴴ = star mu' • (1 : Matrix ι ι ℂ) - M := by
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hM.eq]
      rw [hconj]
      ext k
      change ((star mu' • (1 : Matrix ι ι ℂ) - M) *ᵥ (b j).ofLp) k =
        ((star mu' - (ev j : ℂ)) • (b j).ofLp) k
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hM.mulVec_eigenvectorBasis j,
        sub_smul]
      dsimp only [b, ev]
      simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [hvec, inner_smul_left]
    simp
  have hx_sq : ‖x‖ ^ 2 = ∑ j : ι, ‖(b.repr x) j‖ ^ 2 := by
    rw [← b.repr.norm_map x, EuclideanSpace.norm_sq_eq]
  have hy_sq : ‖y‖ ^ 2 = ∑ j : ι, ‖mu' - (ev j : ℂ)‖ ^ 2 * ‖(b.repr x) j‖ ^ 2 := by
    rw [← b.repr.norm_map y, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy_coord j, norm_mul, mul_pow]
  have hlower : ‖mu' - (ev j₀ : ℂ)‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [hx_sq, Finset.mul_sum, hy_sq]
    refine Finset.sum_le_sum fun j hj => ?_
    have hmin_j : ‖mu' - (ev j₀ : ℂ)‖ ≤ ‖mu' - (ev j : ℂ)‖ := hj₀_min j hj
    have hsq_j : ‖mu' - (ev j₀ : ℂ)‖ ^ 2 ≤ ‖mu' - (ev j : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hmin_j 2
    exact mul_le_mul_of_nonneg_right hsq_j (sq_nonneg _)
  have hupper : ‖y‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖x‖ ^ 2 := by
    have h1 : ‖y‖ ^ 2 ≤ (‖E‖ * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg y) hy_norm_le 2
    rwa [mul_pow] at h1
  have hsq_bound : ‖mu' - (ev j₀ : ℂ)‖ ^ 2 ≤ ‖E‖ ^ 2 :=
    le_of_mul_le_mul_right (hlower.trans hupper) (pow_pos hx_pos 2)
  nlinarith [norm_nonneg (mu' - (ev j₀ : ℂ)), norm_nonneg E, hsq_bound]

end Qatlib.Papers.NonHermitian20.HermitianPert
