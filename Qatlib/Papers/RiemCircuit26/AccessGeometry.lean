/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TangentProject.EnergyGradient
import Qatlib.Foundations.MatrixGeometry.TangentProject.ProjectedHessian
import Qatlib.Papers.RiemCircuit26.HessianGeometry.RiemannianHessian
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.RiemCircuit26.AccessGeometry
open Qatlib.Papers.RiemCircuit26.HessianGeometry
open Qatlib.Foundations.MatrixGeometry.TangentProject

theorem actual_cost_eq {p : ℕ} (O ψ U : Mat p) : (cost O ψ U).re = energy O ψ U := by
  simp only [cost, energy, stateMap, Matrix.mul_assoc]

theorem actual_gradient_representation {p : ℕ} (O ψ U V : Mat p)
    (hO : Oᴴ = O) (hψ : ψᴴ = ψ) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ)
    (hV : IsTangent U V) :
    fderiv ℝ (fun W : Mat p => (cost O ψ W).re) U V =
      realFrob (comm O (U * ψ * Uᴴ) * U) V := by
  have he : (fun W : Mat p => (cost O ψ W).re) = energy O ψ :=
    funext (actual_cost_eq O ψ)
  rw [he, energy_fderiv_frobenius O ψ U V hO hψ]
  have ho := project_orthogonal U ((2 : ℝ) • (O * U * ψ)) V hU hV
  rw [realFrob_sub_left, project_energy_gradient O ψ U hO hψ] at ho
  change realFrob ((2 : ℝ) • (O * U * ψ)) V = realFrob (gradientExtension O ψ U) V
  linarith

theorem actual_hessian_projected_fderiv {p : ℕ} (O ψ U Ω : Mat p)
    (hO : Oᴴ = O) (hψ : ψᴴ = ψ) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ)
    (hΩ : Ωᴴ = -Ω) :
    project U (fderiv ℝ (gradientExtension O ψ) U (Ω * U)) =
      hessianTangent O (U * ψ * Uᴴ) Ω U := by
  rw [projected_gradient_fderiv O ψ U Ω hO hψ hU hΩ]
  unfold lieHessian bracket stateMap hessianTangent hessianMap hessianL HessianGeometry.comm
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

theorem actual_hessian_tangent {p : ℕ} (O ψ U Ω : Mat p)
    (hO : Oᴴ = O) (hψ : ψᴴ = ψ) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ)
    (hΩ : Ωᴴ = -Ω) : IsTangent U (hessianTangent O (U * ψ * Uᴴ) Ω U) := by
  rw [← actual_hessian_projected_fderiv O ψ U Ω hO hψ hU hΩ]
  exact project_tangent _ _
