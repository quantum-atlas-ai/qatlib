/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.JointApparatus
import Qatlib.Foundations.FiniteStats.BornEstimator.SecondMoment
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators
open Qatlib.Foundations.GraphFraction.CoverLP
variable {V d : Type*} [Fintype V] [DecidableEq V] [Fintype d] [DecidableEq d]

def contextLinearOperator (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S)) (a : V → ℝ) : HermitianMat d ℂ :=
  ∑ i,if i∈I.val then a i • S i else 0

theorem contextScore_eigen_action (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (a : V → ℝ) (s : Fin (Fintype.card V) → Bool) :
    (contextLinearOperator S I a).mat*((contextPOVM S hS I).mats s).mat=
      (∑ i,a i*contextSign S I i s) • ((contextPOVM S hS I).mats s).mat := by
  simp only [contextLinearOperator,HermitianMat.mat_finset_sum]
  rw [Finset.sum_mul,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈I.val
  · simp only [hi,ite_true,HermitianMat.mat_smul]
    have he := contextPOVM_eigen_action S hS I i s
    simp only [hi,ite_true] at he
    rw [smul_mul_assoc,he,smul_smul]
  · simp [hi,contextSign]

theorem contextScore_second_operator (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (a : V → ℝ) :
    (contextLinearOperator S I a).mat*(contextLinearOperator S I a).mat=
      ∑ s,(∑ i,a i*contextSign S I i s)^2 • ((contextPOVM S hS I).mats s).mat := by
  let B := (contextLinearOperator S I a).mat
  have hn : (∑ s,((contextPOVM S hS I).mats s).mat)=1 := by
    simpa only [HermitianMat.mat_finset_sum,HermitianMat.mat_one] using
      congrArg HermitianMat.mat (contextPOVM S hS I).normalized
  calc _ = (B*B)*(∑ s,((contextPOVM S hS I).mats s).mat) := by rw [hn,mul_one]
       _ = ∑ s,B*(B*((contextPOVM S hS I).mats s).mat) := by
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro s _
         rw [mul_assoc]
       _ = _ := by
         apply Finset.sum_congr rfl
         intro s _
         rw [contextScore_eigen_action,mul_smul_comm,contextScore_eigen_action,smul_smul,← pow_two]

theorem jointScore_secondOperator_matrix (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (q : Context (commutationGraph S) → ℝ) (a : V → ℝ) :
    (secondOperator (commutingJointScheme S hS) q (fun ω => ∑ i,a i*contextSign S ω.1 i ω.2)).mat=
      ∑ I,q I • ((contextLinearOperator S I a).mat*(contextLinearOperator S I a).mat) := by
  simp only [secondOperator,HermitianMat.mat_finset_sum,HermitianMat.mat_smul]
  apply Finset.sum_congr rfl
  intro I _
  rw [contextScore_second_operator S hS I a,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [smul_smul]
  rfl

end Qatlib.Foundations.FiniteStats.BornEstimator
