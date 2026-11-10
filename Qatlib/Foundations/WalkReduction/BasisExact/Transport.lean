/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.WalkReduction.BasisExact.Orthogonal
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Foundations.WalkReduction.BasisExact
open Qatlib.Foundations.WalkReduction.FourDefs

theorem sourceBasis_mul_transpose {n : ℝ} (hn : 6 ≤ n) :
    sourceBasis n * (sourceBasis n).transpose = 1 :=
  mul_eq_one_comm.mp (sourceBasis_orthogonal hn)

theorem sourceBasis_inverse {n : ℝ} (hn : 6 ≤ n) :
    (sourceBasis n)⁻¹ = (sourceBasis n).transpose :=
  Matrix.inv_eq_left_inv (sourceBasis_orthogonal hn)

def changed (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (sourceBasis n).transpose * hamiltonian γ n * sourceBasis n

theorem changed_inverse {n : ℝ} (hn : 6 ≤ n) (γ : ℝ) :
    (sourceBasis n)⁻¹ * hamiltonian γ n * sourceBasis n = changed γ n := by
  rw [sourceBasis_inverse hn]
  rfl

theorem intertwines {n : ℝ} (hn : 6 ≤ n) (γ : ℝ) :
    hamiltonian γ n * sourceBasis n = sourceBasis n * changed γ n := by
  simp only [changed,← Matrix.mul_assoc,sourceBasis_mul_transpose hn,Matrix.one_mul]

theorem changed_hermitian (γ n : ℝ) : (changed γ n).IsHermitian := by
  change (changed γ n).transpose = changed γ n
  simp only [changed,Matrix.transpose_mul,Matrix.transpose_transpose,hamiltonian_transpose,
    Matrix.mul_assoc]

theorem marked_row (n : ℝ) (A : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    ((sourceBasis n).transpose*A) 0 j = A 0 j := by
  rw [Matrix.mul_apply,Fin.sum_univ_four]
  change 1*A 0 j+0*A 1 j+0*A 2 j+0*A 3 j=A 0 j
  ring

theorem changed_marked_r (γ n : ℝ) :
    changed γ n 0 1 = -γ*Real.sqrt (3*(n-3))*3*Real.sqrt 2/Real.sqrt (n^2+2) := by
  rw [changed,Matrix.mul_apply,Fin.sum_univ_four]
  simp only [marked_row]
  change (-γ*0-1)*0 + (-γ*Real.sqrt (3*(n-3))-0)*(3*Real.sqrt 2/Real.sqrt (n^2+2)) +
    (-γ*0-0)*(3*Real.sqrt (n-4)/Real.sqrt (n^2+2)) +
    (-γ*0-0)*(Real.sqrt (n-4)*Real.sqrt (n-5)/Real.sqrt (n^2+2)) = _
  ring

theorem changed_marked_r_ne_zero {γ n : ℝ} (hγ : γ ≠ 0) (hn : 6 ≤ n) :
    changed γ n 0 1 ≠ 0 := by
  rw [changed_marked_r]
  have h1 : Real.sqrt (3*(n-3)) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h3 : Real.sqrt (n^2+2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hγ) h1)
    (by norm_num)) h2) h3

theorem sourceBasis_mulVec_injective {n : ℝ} (hn : 6 ≤ n) :
    Function.Injective (sourceBasis n).mulVec := by
  intro v w h
  have h' := congrArg (sourceBasis n).transpose.mulVec h
  simpa only [Matrix.mulVec_mulVec,sourceBasis_orthogonal hn,Matrix.one_mulVec] using h'

theorem eigenvector_transport {n γ lam : ℝ} (hn : 6 ≤ n) (v : Fin 4 → ℝ)
    (hv : Module.End.HasEigenvector (changed γ n).toLin' lam v) :
    Module.End.HasEigenvector (hamiltonian γ n).toLin' lam ((sourceBasis n).mulVec v) := by
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff] at hv ⊢
  refine ⟨?_,?_⟩
  · change (hamiltonian γ n).mulVec ((sourceBasis n).mulVec v) = _
    rw [Matrix.mulVec_mulVec,intertwines hn γ,← Matrix.mulVec_mulVec]
    rw [show (changed γ n).mulVec v = lam • v from hv.1,Matrix.mulVec_smul]
  · intro h
    apply hv.2
    apply sourceBasis_mulVec_injective hn
    simpa only [Matrix.mulVec_zero] using h

end Qatlib.Foundations.WalkReduction.BasisExact
