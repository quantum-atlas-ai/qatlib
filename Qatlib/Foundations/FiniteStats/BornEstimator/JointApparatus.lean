/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.InvolutionProj
import Qatlib.Foundations.GraphFraction.CoverLP.WeightedCover
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators ComplexOrder
open Qatlib.Foundations.GraphFraction.CoverLP
variable {V d : Type*} [Fintype V] [DecidableEq V] [Fintype d] [DecidableEq d]

def commutationGraph (S : V → HermitianMat d ℂ) : SimpleGraph V where
  Adj i j := ¬Commute (S i).mat (S j).mat
  symm := ⟨by intro i j hij hji;exact hij hji.symm⟩
  loopless := ⟨fun _ h => h (Commute.refl _)⟩

omit [Fintype V] [DecidableEq d] in

theorem context_observables_commute (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i j : V) (hi : i∈I.val) (hj : j∈I.val) : Commute (S i).mat (S j).mat := by
  by_cases he : i=j
  · subst j
    exact Commute.refl _
  · exact not_not.mp (I.property hi hj he)

def contextBranch (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (j : Fin (Fintype.card V)) (b : Bool) : HermitianMat d ℂ :=
  if (Fintype.equivFin V).symm j∈I.val then involutionProjector (S ((Fintype.equivFin V).symm j)) b
  else if b then 0 else 1

theorem contextBranch_idempotent (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (j : Fin (Fintype.card V)) (b : Bool) :
    (contextBranch S I j b).mat*(contextBranch S I j b).mat=(contextBranch S I j b).mat := by
  by_cases hi : (Fintype.equivFin V).symm j∈I.val
  · simpa only [contextBranch,if_pos hi] using involutionProjector_idempotent _ (hS _) b
  · cases b <;> simp [contextBranch,hi]

theorem contextBranch_sum (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S)) (j : Fin (Fintype.card V)) :
    (contextBranch S I j false).mat+(contextBranch S I j true).mat=1 := by
  by_cases hi : (Fintype.equivFin V).symm j∈I.val
  · simpa only [contextBranch,if_pos hi,HermitianMat.mat_add,HermitianMat.mat_one] using
      congrArg HermitianMat.mat (involutionProjector_sum (S ((Fintype.equivFin V).symm j)))
  · simp [contextBranch,hi]

theorem contextBranch_commute (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : Fin (Fintype.card V)) (a : Bool) (j : Fin (Fintype.card V)) (b : Bool) :
    Commute (contextBranch S I i a).mat (contextBranch S I j b).mat := by
  by_cases hi : (Fintype.equivFin V).symm i∈I.val
  · by_cases hj : (Fintype.equivFin V).symm j∈I.val
    · simpa only [contextBranch,if_pos hi,if_pos hj] using
        involutionProjector_commute _ _ (context_observables_commute S I _ _ hi hj) a b
    · cases b <;> simp [contextBranch,hi,hj,Commute,SemiconjBy]
  · cases a <;> simp [contextBranch,hi,Commute,SemiconjBy]

def contextPOVM (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) : POVM (Fin (Fintype.card V) → Bool) d :=
  binaryJointPOVM (Fintype.card V) (fun j b => (contextBranch S I j b).mat)
    (fun j b => (contextBranch S I j b).H) (contextBranch_idempotent S hS I)
    (contextBranch_commute S I) (contextBranch_sum S I)

def contextSign (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : V) (s : Fin (Fintype.card V) → Bool) : ℝ := if i∈I.val then binarySign (s (Fintype.equivFin V i)) else 0

omit [DecidableEq d] in

theorem contextSign_square (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : V) (s : Fin (Fintype.card V) → Bool) : (contextSign S I i s)^2=if i∈I.val then 1 else 0 := by
  unfold contextSign
  split_ifs <;> simp [binarySign_sq]

theorem contextPOVM_marginal (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (i : V) :
    (∑ s,contextSign S I i s • (contextPOVM S hS I).mats s)=if i∈I.val then S i else 0 := by
  apply HermitianMat.ext
  by_cases hi : i∈I.val
  · simp only [contextSign,hi,ite_true,HermitianMat.mat_finset_sum,HermitianMat.mat_smul]
    change (∑ s,binarySign (s (Fintype.equivFin V i)) • binaryProduct (Fintype.card V)
      (fun j b => (contextBranch S I j b).mat) s)=(S i).mat
    rw [binaryProduct_marginal _ _ (contextBranch_sum S I)]
    simp only [contextBranch,Equiv.symm_apply_apply,hi,ite_true]
    exact congrArg HermitianMat.mat (involutionProjector_difference (S i))
  · simp [contextSign,hi]

theorem contextPOVM_eigen_action (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (i : V) (s : Fin (Fintype.card V) → Bool) :
    (if i∈I.val then (S i).mat else 0)*((contextPOVM S hS I).mats s).mat =
      contextSign S I i s • ((contextPOVM S hS I).mats s).mat := by
  by_cases hi : i∈I.val
  · have h := binaryProduct_coordinate_action (Fintype.card V) (fun j b => (contextBranch S I j b).mat)
      (contextBranch_idempotent S hS I) (contextBranch_commute S I) (contextBranch_sum S I) (Fintype.equivFin V i) s
    have hd : (contextBranch S I (Fintype.equivFin V i) false).mat-
        (contextBranch S I (Fintype.equivFin V i) true).mat=(S i).mat := by
      simp only [contextBranch,Equiv.symm_apply_apply,hi,ite_true]
      exact congrArg HermitianMat.mat (involutionProjector_difference (S i))
    rw [hd] at h
    simpa only [hi,ite_true,contextSign] using! h
  · simp [contextSign,hi]

def commutingJointScheme (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1) :
    JointScheme (K:=Context (commutationGraph S)) (Ω:=Fin (Fintype.card V) → Bool) S where
  context I := I.val
  measurement I := contextPOVM S hS I
  sign I i s := contextSign S I i s
  sign_sq := contextSign_square S
  marginal := contextPOVM_marginal S hS

end Qatlib.Foundations.FiniteStats.BornEstimator
