/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

def ad (H X : A) : A := H * X - X * H

def adIter (H : A) : ℕ → A → A
  | 0, X => X
  | n+1, X => ad H (adIter H n X)

def left (H : A) : A →L[ℝ] A := ContinuousLinearMap.mul ℝ A H

def right (H : A) : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip H

def adMap (H : A) : A →L[ℝ] A := left H - right H

@[simp] theorem left_apply (H X : A) : left H X = H * X := rfl

@[simp] theorem right_apply (H X : A) : right H X = X * H := rfl

@[simp] theorem adMap_apply (H X : A) : adMap H X = ad H X := rfl

theorem left_pow_apply (H X : A) (n : ℕ) : (left H ^ n) X = H^n * X := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,ih,left_apply,pow_succ']
    exact (mul_assoc _ _ _).symm

theorem right_pow_apply (H X : A) (n : ℕ) : (right H ^ n) X = X * H^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply,ih,right_apply,pow_succ]
    exact mul_assoc _ _ _

theorem adMap_pow_apply (H X : A) (n : ℕ) : (adMap H ^ n) X = adIter H n X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',ContinuousLinearMap.mul_apply,ih,adMap_apply];rfl

theorem scaled_pow_apply (F : A →L[ℝ] A) (t : ℝ) (n : ℕ) (X : A) :
    ((t • F)^n) X = t^n • (F^n) X := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ',ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,ih,map_smul,smul_smul]
    rw [mul_comm]
variable [CompleteSpace A]
local instance : NormedAlgebra ℚ (A →L[ℝ] A) := .restrictScalars ℚ ℝ _

theorem exp_left_apply (H X : A) (t : ℝ) :
    NormedSpace.exp (t • left H) X = NormedSpace.exp (t • H) * X := by
  have hL :=
      (ContinuousLinearMap.apply ℝ A X).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • left H))
  have hR := (right X).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • H))
  apply hL.unique
  convert! hR using 1
  funext n
  simp only [ContinuousLinearMap.apply_apply,ContinuousLinearMap.smul_apply,scaled_pow_apply,smul_pow,left_pow_apply,right_apply,smul_mul_assoc]

theorem exp_right_apply (H X : A) (t : ℝ) :
    NormedSpace.exp (t • right H) X = X * NormedSpace.exp (t • H) := by
  have hL :=
      (ContinuousLinearMap.apply ℝ A X).hasSum
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • right H))
  have hR := (left X).hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • H))
  apply hL.unique
  convert! hR using 1
  funext n
  simp only [ContinuousLinearMap.apply_apply,ContinuousLinearMap.smul_apply,scaled_pow_apply,smul_pow,right_pow_apply,left_apply,mul_smul_comm]
omit [CompleteSpace A] in

theorem scaled_left_right_commute (H : A) (s t : ℝ) :
    Commute (s • left H) (t • right H) := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.smul_apply,left_apply,right_apply,mul_smul_comm,smul_mul_assoc,smul_smul,mul_assoc]
  rw [mul_comm s t]

theorem exp_ad_apply (H X : A) (t : ℝ) :
    NormedSpace.exp (t • adMap H) X =
      NormedSpace.exp (t • H) * X * NormedSpace.exp ((-t) • H) := by
  have he : t • adMap H = t • left H + (-t) • right H := by
    apply ContinuousLinearMap.ext
    intro Y
    change t • (H*Y-Y*H) = t • (H*Y) + (-t) • (Y*H)
    module
  rw [he,NormedSpace.exp_add_of_commute (scaled_left_right_commute H t (-t)),ContinuousLinearMap.mul_apply,exp_left_apply,exp_right_apply,mul_assoc]

theorem conjugation_hasSum (H X : A) (t : ℝ) :
    HasSum (fun n : ℕ => (t^n / (n.factorial : ℝ)) • adIter H n X)
      (NormedSpace.exp (t • H) * X * NormedSpace.exp ((-t) • H)) := by
  have h := (ContinuousLinearMap.apply ℝ A X).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • adMap H))
  rw [ContinuousLinearMap.apply_apply,exp_ad_apply] at h
  convert! h using 1
  funext n
  simp only [ContinuousLinearMap.apply_apply,ContinuousLinearMap.smul_apply,scaled_pow_apply,adMap_pow_apply,smul_smul]
  congr 1
  rw [div_eq_mul_inv,mul_comm]

theorem conjugation_tsum (H X : A) (t : ℝ) :
    (∑' n : ℕ,(t^n / (n.factorial : ℝ)) • adIter H n X) =
      NormedSpace.exp (t • H) * X * NormedSpace.exp ((-t) • H) :=
  (conjugation_hasSum H X t).tsum_eq
end Qatlib.Foundations.MatrixAlgebra.CommutatorExp
