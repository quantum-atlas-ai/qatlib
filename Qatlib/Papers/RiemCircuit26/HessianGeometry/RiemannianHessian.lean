/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiemCircuit26.HessianGeometry.HessianAlgebra
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.RiemCircuit26.HessianGeometry

noncomputable def cost {p : ℕ} (O ψ₀ U : Mat p) : ℂ :=
  (O * U * ψ₀ * Uᴴ).trace

theorem cost_curve {p : ℕ} (O ψ₀ Ω U : Mat p) (t : ℝ) :
    cost O ψ₀ (evol Ω t * U) = (O * conjEvol Ω (U * ψ₀ * Uᴴ) t).trace := by
  simp only [cost, conjEvol, Matrix.conjTranspose_mul, Matrix.mul_assoc]

noncomputable def hessianTangent {p : ℕ} (O ψ Ω U : Mat p) : Mat p :=
  hessianMap O ψ Ω * U

theorem riemannianHessian_apply {p : ℕ} (O ψ Ω U : Mat p) :
    hessianTangent O ψ Ω U =
      (1 / 2 : ℂ) • ((comm O (comm Ω ψ) + comm (comm O Ω) ψ) * U) := by
  simp only [hessianTangent, hessianMap, hessianL, Matrix.smul_mul]

theorem trace_hessianL_mul {p : ℕ} (O ψ Ω : Mat p) :
    (hessianL O ψ Ω * Ω).trace = -2 * (O * comm Ω (comm Ω ψ)).trace := by
  have h1 : (comm O (comm Ω ψ) * Ω).trace =
      -((O * comm Ω (comm Ω ψ)).trace) := by
    rw [trace_commutator_mul O (comm Ω ψ) Ω, comm_neg_swap (comm Ω ψ) Ω,
      Matrix.mul_neg, Matrix.trace_neg]
  have h2 : (comm (comm O Ω) ψ * Ω).trace =
      -((O * comm Ω (comm Ω ψ)).trace) := by
    rw [trace_commutator_mul (comm O Ω) ψ Ω, comm_neg_swap ψ Ω, Matrix.mul_neg,
      Matrix.trace_neg, trace_commutator_mul O Ω (comm Ω ψ)]
  simp only [hessianL, add_mul, Matrix.trace_add]
  rw [h1, h2]
  ring

theorem trace_hessianMap_mul {p : ℕ} (O ψ Ω : Mat p) :
    (hessianMap O ψ Ω * Ω).trace = -((O * comm Ω (comm Ω ψ)).trace) := by
  rw [hessianMap, Matrix.smul_mul, Matrix.trace_smul, trace_hessianL_mul]
  ring

theorem hessianMap_adjoint {p : ℕ} (O ψ Ω : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ)
    (hΩ : Ωᴴ = -Ω) : (hessianMap O ψ Ω)ᴴ = -hessianMap O ψ Ω := by
  have hL : (hessianL O ψ Ω)ᴴ = -hessianL O ψ Ω := by
    have h := hessianL_adjoint O ψ Ω hO hψ
    rw [hΩ, hessianL_neg] at h
    exact h.symm
  rw [hessianMap, Matrix.conjTranspose_smul, hL, smul_neg]
  simp

theorem hessianMap_trace_adjoint {p : ℕ} (O ψ Ω : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ)
    (hΩ : Ωᴴ = -Ω) :
    (((hessianMap O ψ Ω)ᴴ) * Ω).trace = (O * comm Ω (comm Ω ψ)).trace := by
  rw [hessianMap_adjoint O ψ Ω hO hψ hΩ, neg_mul, Matrix.trace_neg,
    trace_hessianMap_mul]
  simp

theorem riemannianHessian_secondVariation {p : ℕ} (O ψ Ω : Mat p) (hO : Oᴴ = O)
    (hψ : ψᴴ = ψ) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (deriv (fun t : ℝ => (O * conjEvol Ω ψ t).trace))
      ((((hessianMap O ψ Ω)ᴴ) * Ω).trace) 0 := by
  have hfun : deriv (fun t : ℝ => (O * conjEvol Ω ψ t).trace) =
      fun t : ℝ => (O * conjEvol Ω (comm Ω ψ) t).trace := by
    funext t
    exact (hasDerivAt_trace_conjEvol Ω O ψ hΩ t).deriv
  rw [hfun]
  have hd := hasDerivAt_trace_conjEvol_zero Ω O (comm Ω ψ) hΩ
  rw [← hessianMap_trace_adjoint O ψ Ω hO hψ hΩ] at hd
  exact hd

theorem riemannianHessian_secondVariation_cost {p : ℕ} (O ψ₀ Ω U : Mat p) (hO : Oᴴ = O)
    (hψ₀ : ψ₀ᴴ = ψ₀) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (deriv (fun t : ℝ => cost O ψ₀ (evol Ω t * U)))
      ((((hessianMap O (U * ψ₀ * Uᴴ) Ω)ᴴ) * Ω).trace) 0 := by
  have hfun : (fun t : ℝ => cost O ψ₀ (evol Ω t * U)) =
      fun t : ℝ => (O * conjEvol Ω (U * ψ₀ * Uᴴ) t).trace := by
    funext t
    exact cost_curve O ψ₀ Ω U t
  rw [hfun]
  have hψ : (U * ψ₀ * Uᴴ)ᴴ = U * ψ₀ * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, hψ₀, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  exact riemannianHessian_secondVariation O (U * ψ₀ * Uᴴ) Ω hO hψ hΩ

theorem riemannianHessian_secondVariation_appendix {p : ℕ} (O ψ Ω : Mat p) (hO : Oᴴ = O)
    (hψ : ψᴴ = ψ) (hΩ : Ωᴴ = -Ω) :
    HasDerivAt (deriv (fun t : ℝ => (O * conjEvol Ω ψ t).trace))
      ((((hessianMap O ψ Ω)ᴴ) * Ω).trace) 0 :=
  riemannianHessian_secondVariation O ψ Ω hO hψ hΩ

theorem hessianMap_selfAdjoint {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    (((hessianMap O ψ X)ᴴ) * Y).trace = (Xᴴ * hessianMap O ψ Y).trace := by
  have hc : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.star_def,
      Complex.conj_ofReal]
  rw [hessianMap, hessianMap, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, hessianL_selfAdjoint O ψ X Y hO hψ, hc]

theorem hessianMap_selfAdjoint_skew {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O)
    (hψ : ψᴴ = ψ) (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    (hessianMap O ψ X * Y).trace = (X * hessianMap O ψ Y).trace := by
  rw [hessianMap, hessianMap, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, hessianL_selfAdjoint_skew O ψ X Y hO hψ hX hY]

end Qatlib.Papers.RiemCircuit26.HessianGeometry
