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

namespace Qatlib.Papers.RiemCircuit26.HessianGeometry

def hessianL {p : ℕ} (O ψ X : Mat p) : Mat p :=
  comm O (comm X ψ) + comm (comm O X) ψ

def hessianMap {p : ℕ} (O ψ X : Mat p) : Mat p :=
  (1 / 2 : ℂ) • hessianL O ψ X

theorem hessianMap_apply {p : ℕ} (O ψ X : Mat p) :
    hessianMap O ψ X = (1 / 2 : ℂ) • hessianL O ψ X := rfl

theorem hessianL_eq_neg {p : ℕ} (O ψ X : Mat p) :
    hessianL O ψ X = -(comm O (comm ψ X) + comm ψ (comm O X)) := by
  simp only [hessianL, comm_neg_swap X ψ, comm_neg_right, comm_neg_swap (comm O X) ψ]
  abel

theorem hessianL_add {p : ℕ} (O ψ X Y : Mat p) :
    hessianL O ψ (X + Y) = hessianL O ψ X + hessianL O ψ Y := by
  simp only [hessianL, comm_add_left, comm_add_right]
  abel

theorem hessianL_neg {p : ℕ} (O ψ X : Mat p) :
    hessianL O ψ (-X) = -hessianL O ψ X := by
  simp only [hessianL, comm_neg_left, comm_neg_right]
  abel

theorem hessianL_smul {p : ℕ} (c : ℂ) (O ψ X : Mat p) :
    hessianL O ψ (c • X) = c • hessianL O ψ X := by
  simp only [hessianL, comm_smul_left, comm_smul_right, smul_add]

theorem hessianL_smul_I {p : ℕ} (O ψ X : Mat p) :
    hessianL O ψ (Complex.I • X) = Complex.I • hessianL O ψ X :=
  hessianL_smul Complex.I O ψ X

theorem hessianL_real_smul {p : ℕ} (r : ℝ) (O ψ X : Mat p) :
    hessianL O ψ (r • X) = r • hessianL O ψ X := by
  rw [← IsScalarTower.algebraMap_smul (A := ℂ) (M := Mat p) r X, hessianL_smul,
    IsScalarTower.algebraMap_smul (A := ℂ) (M := Mat p) r (hessianL O ψ X)]

theorem hessianL_adjoint {p : ℕ} (O ψ X : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    hessianL O ψ Xᴴ = (hessianL O ψ X)ᴴ := by
  have h1 : comm Xᴴ ψ = -(comm X ψ)ᴴ := by
    rw [comm_star X ψ, hψ, neg_neg]
  have h2 : comm O (comm Xᴴ ψ) = (comm O (comm X ψ))ᴴ := by
    rw [comm_star O (comm X ψ), hO, h1, comm_neg_right]
  have h3 : comm (comm O Xᴴ) ψ = (comm (comm O X) ψ)ᴴ := by
    have hOX : comm O Xᴴ = -(comm O X)ᴴ := by
      rw [comm_star O X, hO, neg_neg]
    have hZ : comm ((comm O X)ᴴ) ψ = -((comm (comm O X) ψ))ᴴ := by
      rw [comm_star (comm O X) ψ, hψ, neg_neg]
    rw [hOX, comm_neg_left, hZ, neg_neg]
  simp only [hessianL]
  rw [Matrix.conjTranspose_add, ← h2, ← h3]

theorem hessianL_isHermitian {p : ℕ} (O ψ X : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ)
    (hX : Xᴴ = X) : (hessianL O ψ X)ᴴ = hessianL O ψ X := by
  rw [← hessianL_adjoint O ψ X hO hψ, hX]

theorem hessianL_isSkew {p : ℕ} (O ψ X : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ)
    (hX : Xᴴ = -X) : (hessianL O ψ X)ᴴ = -hessianL O ψ X := by
  rw [← hessianL_adjoint O ψ X hO hψ, hX, hessianL_neg]

theorem trace_commutator_adjoint {p : ℕ} (A X Y : Mat p) (hA : Aᴴ = A) :
    ((comm A X)ᴴ * Y).trace = (Xᴴ * comm A Y).trace := by
  have hmain : (A * (comm Xᴴ Y)).trace = -((Xᴴ * comm A Y).trace) := by
    have h1 : (A * (comm Xᴴ Y)).trace =
        (A * (Xᴴ * Y)).trace - (A * (Y * Xᴴ)).trace := by
      simp only [comm, mul_sub, Matrix.trace_sub]
    have h2 : (Xᴴ * comm A Y).trace =
        (Xᴴ * (A * Y)).trace - (Xᴴ * (Y * A)).trace := by
      simp only [comm, mul_sub, Matrix.trace_sub]
    rw [h1, h2]
    rw [← Matrix.mul_assoc A Xᴴ Y, ← Matrix.mul_assoc A Y Xᴴ,
      ← Matrix.mul_assoc Xᴴ A Y, ← Matrix.mul_assoc Xᴴ Y A]
    rw [Matrix.trace_mul_cycle Xᴴ A Y, Matrix.trace_mul_cycle Y Xᴴ A,
      Matrix.trace_mul_cycle Xᴴ Y A]
    ring
  rw [comm_star, hA, neg_mul, Matrix.trace_neg, trace_commutator_mul, hmain]
  ring

theorem hessianL_selfAdjoint {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    ((hessianL O ψ X)ᴴ * Y).trace = (Xᴴ * hessianL O ψ Y).trace := by
  rw [hessianL_eq_neg O ψ X, hessianL_eq_neg O ψ Y]
  rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_add, neg_mul, Matrix.trace_neg]
  rw [add_mul, Matrix.trace_add, Matrix.mul_neg, Matrix.trace_neg, mul_add, Matrix.trace_add]
  rw [trace_commutator_adjoint O (comm ψ X) Y hO,
    trace_commutator_adjoint ψ (comm O X) Y hψ]
  rw [← trace_commutator_adjoint O X (comm ψ Y) hO,
    ← trace_commutator_adjoint ψ X (comm O Y) hψ]
  ring

theorem hessianL_selfAdjoint_real {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    Complex.re ((hessianL O ψ X)ᴴ * Y).trace =
      Complex.re (Xᴴ * hessianL O ψ Y).trace := by
  rw [hessianL_selfAdjoint O ψ X Y hO hψ]

theorem hessianL_selfAdjoint_hermitian {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O)
    (hψ : ψᴴ = ψ) (hX : Xᴴ = X) (_hY : Yᴴ = Y) :
    (hessianL O ψ X * Y).trace = (X * hessianL O ψ Y).trace := by
  have hm := hessianL_selfAdjoint O ψ X Y hO hψ
  have hLX := hessianL_isHermitian O ψ X hO hψ hX
  rw [hLX, hX] at hm
  exact hm

theorem hessianL_selfAdjoint_skew {p : ℕ} (O ψ X Y : Mat p) (hO : Oᴴ = O)
    (hψ : ψᴴ = ψ) (hX : Xᴴ = -X) (_hY : Yᴴ = -Y) :
    (hessianL O ψ X * Y).trace = (X * hessianL O ψ Y).trace := by
  have hm := hessianL_selfAdjoint O ψ X Y hO hψ
  have hLX := hessianL_isSkew O ψ X hO hψ hX
  rw [hLX, hX] at hm
  rw [neg_mul, neg_mul, Matrix.trace_neg, Matrix.trace_neg] at hm
  exact neg_inj.mp hm

end Qatlib.Papers.RiemCircuit26.HessianGeometry
