/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RiemCircuit26.HessianGeometry.ExpTools
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Matrix
open scoped Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.RiemCircuit26.ShiftRules
open Qatlib.Papers.RiemCircuit26.HessianGeometry

noncomputable def gateEvol {p : ℕ} (P : Mat p) (x : ℝ) : Mat p :=
  evol (halfI P) x

noncomputable def gradientCost {p : ℕ} (O ψ P : Mat p) (x : ℝ) : ℂ :=
  (O * conjEvol (halfI P) ψ x).trace

theorem comm_halfI_left {p : ℕ} (P M : Mat p) :
    HessianGeometry.comm (halfI P) M = (Complex.I / 2) • HessianGeometry.comm P M := by
  rw [halfI, ← IsScalarTower.algebraMap_smul (A := ℂ) (M := Mat p) (1 / 2 : ℝ) (Complex.I • P),
    comm_smul_left, comm_smul_left, smul_smul]
  congr 1
  push_cast
  ring

theorem comm_halfI_right {p : ℕ} (M P : Mat p) :
    HessianGeometry.comm M (halfI P) = (Complex.I / 2) • HessianGeometry.comm M P := by
  rw [halfI, ← IsScalarTower.algebraMap_smul (A := ℂ) (M := Mat p) (1 / 2 : ℝ) (Complex.I • P),
    comm_smul_right, comm_smul_right, smul_smul]
  congr 1
  push_cast
  ring

theorem gradient_firstOrder {p : ℕ} (O ψ P : Mat p) (hP : Pᴴ = P) :
    HasDerivAt (gradientCost O ψ P) ((Complex.I / 2) * (ψ * HessianGeometry.comm O P).trace) 0 := by
  have h := hasDerivAt_trace_conjEvol_zero (halfI P) O ψ (halfI_star P hP)
  have hv : (O * HessianGeometry.comm (halfI P) ψ).trace = (Complex.I / 2) * (ψ * HessianGeometry.comm O P).trace := by
    rw [comm_halfI_left, Matrix.mul_smul, Matrix.trace_smul, trace_mul_commutator, smul_eq_mul]
  rw [hv] at h
  simpa only [gradientCost] using! h

theorem evol_halfI_eq {p : ℕ} (P : Mat p) (hP2 : P * P = 1) (t : ℝ) :
    evol (halfI P) t =
      (Real.cos (t / 2)) • (1 : Mat p) + (Real.sin (t / 2)) • (Complex.I • P) := by
  rw [evol]
  have h : t • halfI P = (t / 2) • (Complex.I • P) := by
    rw [halfI, smul_smul]
    congr 1
    ring
  rw [h, exp_half_euler P hP2 t]

theorem evol_halfI_pi_div_two {p : ℕ} (P : Mat p) (hP2 : P * P = 1) :
    evol (halfI P) (Real.pi / 2) =
      (Real.sqrt 2 / 2) • (1 + Complex.I • P) := by
  rw [evol_halfI_eq P hP2]
  rw [show Real.pi / 2 / 2 = Real.pi / 4 by ring]
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four, ← smul_add]

theorem evol_halfI_neg_pi_div_two {p : ℕ} (P : Mat p) (hP2 : P * P = 1) :
    evol (halfI P) (-(Real.pi / 2)) =
      (Real.sqrt 2 / 2) • (1 - Complex.I • P) := by
  rw [evol_halfI_eq P hP2]
  rw [show -(Real.pi / 2) / 2 = -(Real.pi / 4) by ring]
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four, neg_smul,
    ← sub_eq_add_neg, ← smul_sub]

theorem star_one_add_I_smul {p : ℕ} (P : Mat p) (hP : Pᴴ = P) :
    (1 + Complex.I • P)ᴴ = 1 - Complex.I • P := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hP]
  have hI : star Complex.I = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  rw [hI, neg_smul, sub_eq_add_neg]

theorem star_one_sub_I_smul {p : ℕ} (P : Mat p) (hP : Pᴴ = P) :
    (1 - Complex.I • P)ᴴ = 1 + Complex.I • P := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hP]
  have hI : star Complex.I = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  rw [hI, neg_smul, sub_neg_eq_add]

theorem conjEvol_pi_div_two {p : ℕ} (P ψ : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    conjEvol (halfI P) ψ (Real.pi / 2) =
      (1 / 2 : ℝ) • ((1 + Complex.I • P) * ψ * (1 - Complex.I • P)) := by
  rw [conjEvol, evol_halfI_pi_div_two P hP2, Matrix.conjTranspose_smul,
    star_one_add_I_smul P hP]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [star_trivial]
  rw [show (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_mul_div_comm, h2]
    norm_num]

theorem conjEvol_neg_pi_div_two {p : ℕ} (P ψ : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    conjEvol (halfI P) ψ (-(Real.pi / 2)) =
      (1 / 2 : ℝ) • ((1 - Complex.I • P) * ψ * (1 + Complex.I • P)) := by
  rw [conjEvol, evol_halfI_neg_pi_div_two P hP2, Matrix.conjTranspose_smul,
    star_one_sub_I_smul P hP]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [star_trivial]
  rw [show (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = (1 / 2 : ℝ) by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_mul_div_comm, h2]
    norm_num]

theorem conjEvol_sub_eq {p : ℕ} (P ψ : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    conjEvol (halfI P) ψ (Real.pi / 2) - conjEvol (halfI P) ψ (-(Real.pi / 2)) =
      Complex.I • HessianGeometry.comm P ψ := by
  rw [conjEvol_pi_div_two P ψ hP hP2, conjEvol_neg_pi_div_two P ψ hP hP2, ← smul_sub]
  let X : Mat p := Complex.I • P
  have hexp :
      ((1 + Complex.I • P) * ψ * (1 - Complex.I • P)) -
        ((1 - Complex.I • P) * ψ * (1 + Complex.I • P)) =
      2 • HessianGeometry.comm (Complex.I • P) ψ := by
    change ((1 + X) * ψ * (1 - X)) - ((1 - X) * ψ * (1 + X)) = 2 • HessianGeometry.comm X ψ
    rw [HessianGeometry.comm]
    noncomm_ring
  rw [hexp, comm_smul_left]
  module

theorem parameter_shift {p : ℕ} (O ψ P : Mat p) (hP : Pᴴ = P) (hP2 : P * P = 1) :
    HasDerivAt (gradientCost O ψ P)
      ((1 / 2 : ℂ) *
        (gradientCost O ψ P (Real.pi / 2) - gradientCost O ψ P (-(Real.pi / 2)))) 0 := by
  have hderiv := gradient_firstOrder O ψ P hP
  convert hderiv using 1
  have hdiff : gradientCost O ψ P (Real.pi / 2) - gradientCost O ψ P (-(Real.pi / 2))
      = (O * (conjEvol (halfI P) ψ (Real.pi / 2) - conjEvol (halfI P) ψ (-(Real.pi / 2)))).trace := by
    simp only [gradientCost, Matrix.mul_sub, Matrix.trace_sub]
  rw [hdiff, conjEvol_sub_eq P ψ hP hP2, Matrix.mul_smul, Matrix.trace_smul,
    trace_mul_commutator]
  ring

end Qatlib.Papers.RiemCircuit26.ShiftRules
