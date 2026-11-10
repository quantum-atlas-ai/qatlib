/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiemCircuit26.ShiftRules.HessianCoefficient
import Qatlib.Papers.RiemCircuit26.HessianGeometry.RiemannianHessian
import Qatlib.Papers.RiemCircuit26.AccessGeometry
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.RiemCircuit26.ShiftRules
open Qatlib.Papers.RiemCircuit26.HessianGeometry
open Qatlib.Foundations.MatrixGeometry.TangentProject

def newtonEntry {p : ℕ} (O ψ P Q : Mat p) : ℝ :=
  realFrob (Complex.I • P) (hessianMap O ψ (Complex.I • Q))

def fourCorner {p : ℕ} (O ψ P Q : Mat p) : ℂ :=
  hessianCost O ψ P Q (Real.pi / 2) (Real.pi / 2) -
    hessianCost O ψ P Q (Real.pi / 2) (-(Real.pi / 2)) -
    hessianCost O ψ P Q (-(Real.pi / 2)) (Real.pi / 2) +
    hessianCost O ψ P Q (-(Real.pi / 2)) (-(Real.pi / 2))

theorem trace_hessian_coefficient {p : ℕ} (O ψ P Q : Mat p) :
    (P * hessianMap O ψ Q).trace =
      (1 / 2 : ℂ) * ((ψ * HessianGeometry.comm (HessianGeometry.comm P O) Q).trace + (ψ * HessianGeometry.comm (HessianGeometry.comm Q O) P).trace) := by
  have h1 : (P * HessianGeometry.comm O (HessianGeometry.comm Q ψ)).trace = (ψ * HessianGeometry.comm (HessianGeometry.comm P O) Q).trace := by
    rw [trace_mul_commutator, Matrix.trace_mul_comm, trace_mul_commutator]
  have h2 : (P * HessianGeometry.comm (HessianGeometry.comm O Q) ψ).trace = (ψ * HessianGeometry.comm (HessianGeometry.comm Q O) P).trace := by
    rw [trace_mul_commutator]
    congr 2
    unfold HessianGeometry.comm
    noncomm_ring
  simp only [hessianMap, hessianL, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_add, Matrix.trace_add]
  rw [h1, h2]

theorem newtonEntry_eq_trace {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) :
    newtonEntry O ψ P Q = (P * hessianMap O ψ Q).trace.re := by
  have hi : hessianMap O ψ (Complex.I • Q) = Complex.I • hessianMap O ψ Q := by
    simp only [hessianMap, hessianL_smul, smul_smul]
    congr 1
    ring
  rw [newtonEntry, realFrob, hi, Matrix.conjTranspose_smul, hP]
  simp only [Complex.star_def, Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem newtonEntry_measured {p : ℕ} (O ψ P Q : Mat p) (hP : Pᴴ = P) (hQ : Qᴴ = Q)
    (hP2 : P * P = 1) (hQ2 : Q * Q = 1) :
    newtonEntry O ψ P Q = ((1 / 2 : ℂ) * (fourCorner O ψ P Q + fourCorner O ψ Q P)).re := by
  rw [newtonEntry_eq_trace O ψ P Q hP, trace_hessian_coefficient]
  rw [fourCorner, fourCorner_eq O ψ P Q hP hQ hP2 hQ2,
    fourCorner, fourCorner_eq O ψ Q P hQ hP hQ2 hP2]
  congr 2
  ring

theorem diagonal_corrected {p : ℕ} (O ψ P : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    (ψ * HessianGeometry.comm (HessianGeometry.comm P O) P).trace =
      2 * (gradientCost O ψ P (Real.pi / 2) + gradientCost O ψ P (-(Real.pi / 2)) -
        2 * gradientCost O ψ P 0) := by
  have ht := trace_comm_comm_eq O ψ P hP2
  have hc := hessianCost_xx_centralDiff O ψ P P hP hP2
  simp only [hessianCost_y_zero] at hc
  rw [← hc] at ht
  linear_combination 4 * ht

theorem newtonEntry_native {p : ℕ} (O ψ U P Q : Mat p)
    (hO : Oᴴ = O) (hψ : ψᴴ = ψ) (hU : U ∈ Matrix.unitaryGroup (Fin p) ℂ) (hQ : Qᴴ = Q) :
    newtonEntry O (U * ψ * Uᴴ) P Q =
      realFrob ((Complex.I • P) * U)
        (project U (fderiv ℝ (gradientExtension O ψ) U ((Complex.I • Q) * U))) := by
  have hΩ : (Complex.I • Q)ᴴ = -(Complex.I • Q) := by
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_I, hQ, neg_smul]
  rw [AccessGeometry.actual_hessian_projected_fderiv O ψ U (Complex.I • Q) hO hψ hU hΩ,
    hessianTangent, realFrob_mul_unitary U _ _ hU]
  rfl
