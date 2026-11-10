/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiracEquation16.SpinGates.Spin
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.DiracEquation16.SpinGates
open Qatlib.Papers.DiracEquation16.SpinGates
open Qatlib.Papers.DiracEquation16.SpinGates.FourD

def alpha (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := ![alphaX4, alphaY4, alphaZ4] a

theorem alpha_hermitian (a : Fin 3) : (alpha a)ᴴ = alpha a := by
  fin_cases a <;> simp [alpha, alphaX4_hermitian, alphaY4_hermitian, alphaZ4_hermitian]

theorem alpha_sq (a : Fin 3) : alpha a * alpha a = 1 := by
  fin_cases a <;> simp [alpha, alphaX4_sq, alphaY4_sq, alphaZ4_sq]

theorem alpha_beta_anticomm (a : Fin 3) : alpha a * beta4 = -(beta4 * alpha a) := by
  fin_cases a <;> simp [alpha, alphaX4_anticomm, alphaY4_anticomm, alphaZ4_anticomm]

def S (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := Smat (alpha a) beta4

theorem S_hermitian (a : Fin 3) : (S a)ᴴ = S a :=
  Smat_hermitian (alpha_hermitian a) beta4_hermitian

theorem S_sq (a : Fin 3) : S a * S a = 1 :=
  Smat_mul_Smat (alpha_sq a) beta4_sq (alpha_beta_anticomm a)

theorem S_unitary (a : Fin 3) : S a ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (S a)ᴴ * S a = 1
  rw [S_hermitian, S_sq]

def hadBase : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,1,0; 0,1,0,1; 1,0,-1,0; 0,1,0,-1]

def hadFirst : Matrix (Fin 4) (Fin 4) ℂ := sCoeff • hadBase

def ctrlX : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0]

def ctrlY : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,0,-Complex.I; 0,0,Complex.I,0]

def ctrlZ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,-1]

def ctrl (a : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ := ![ctrlX, ctrlY, ctrlZ] a

theorem S_three_gate (a : Fin 3) : ctrl a * hadFirst * ctrl a = S a := by
  unfold hadFirst S Smat
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ctrl, ctrlX, ctrlY, ctrlZ, hadBase, alpha, alphaX4, alphaY4, alphaZ4,
      beta4, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem S_beta_conj (a : Fin 3) : S a * beta4 * S a = alpha a :=
  Smat_mul_beta_mul (alpha_sq a) beta4_sq (alpha_beta_anticomm a)

theorem ctrl_sq (a : Fin 3) : ctrl a * ctrl a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ctrl, ctrlX, ctrlY, ctrlZ, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem ctrl_unitary (a : Fin 3) : ctrl a ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (ctrl a)ᴴ * ctrl a = 1
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [ctrl, ctrlX, ctrlY, ctrlZ, Matrix.mul_apply, Fin.sum_univ_four,
      Complex.conj_I, Complex.I_mul_I]

theorem hadFirst_unitary : hadFirst ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hu := (Matrix.unitaryGroup (Fin 4) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin 4) ℂ).mul_mem (ctrl_unitary 0) (S_unitary 0)) (ctrl_unitary 0)
  have he : ctrl 0 * S 0 * ctrl 0 = hadFirst := by
    rw [← S_three_gate 0]
    calc
      _ = (ctrl 0 * ctrl 0) * hadFirst * (ctrl 0 * ctrl 0) := by noncomm_ring
      _ = hadFirst := by rw [ctrl_sq]; simp
  rwa [he] at hu
