/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.InvolutionProj
import Qatlib.Foundations.GraphFraction.CoverLP.WeightedCover

/-!
# Joint apparatus for commuting observable contexts

This module defines `commutationGraph`, whose edges join noncommuting observables, and
constructs binary measurement branches for each independent-set context. For Hermitian
involutions, `contextPOVM` is a joint POVM with explicit signed marginals and branch eigenvalue
actions.

The construction `commutingJointScheme` packages the apparatus as a `JointScheme`. It realizes
the joint-measurement component of context-based strategies considered in [XuEtAl2026].

## Main statements

* `commutationGraph`: The simple graph whose edges join pairs of observables that do not
  commute.
* `contextPOVM_marginal`: The signed marginal of the context POVM equals the observable inside
  the context and zero outside it, implementing the joint-measurement marginal used in
  [XuEtAl2026].
* `commutingJointScheme`: The joint scheme formed from the context POVMs and their outcome signs
  for a family of Hermitian involutions.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators ComplexOrder
open Qatlib.Foundations.GraphFraction.CoverLP
variable {V d : Type*} [Fintype V] [DecidableEq V] [Fintype d] [DecidableEq d]

/-- The simple graph whose edges join pairs of observables that do not commute. -/
def commutationGraph (S : V → HermitianMat d ℂ) : SimpleGraph V where
  Adj i j := ¬Commute (S i).mat (S j).mat
  symm := ⟨by intro i j hij hji;exact hij hji.symm⟩
  loopless := ⟨fun _ h => h (Commute.refl _)⟩

omit [Fintype V] [DecidableEq d] in

/-- Observables belonging to the same independent-set context of the noncommutation graph
commute. -/
theorem context_observables_commute (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i j : V) (hi : i∈I.val) (hj : j∈I.val) : Commute (S i).mat (S j).mat := by
  by_cases he : i=j
  · subst j
    exact Commute.refl _
  · exact not_not.mp (I.property hi hj he)

/-- The binary spectral branch for an observable in the context, using the identity and zero
branches outside the context. -/
def contextBranch (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (j : Fin (Fintype.card V)) (b : Bool) : HermitianMat d ℂ :=
  if (Fintype.equivFin V).symm j∈I.val then involutionProjector (S ((Fintype.equivFin V).symm j)) b
  else if b then 0 else 1

/-- If all observables are involutions, every context branch is idempotent. -/
theorem contextBranch_idempotent (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) (j : Fin (Fintype.card V)) (b : Bool) :
    (contextBranch S I j b).mat*(contextBranch S I j b).mat=(contextBranch S I j b).mat := by
  by_cases hi : (Fintype.equivFin V).symm j∈I.val
  · simpa only [contextBranch,if_pos hi] using involutionProjector_idempotent _ (hS _) b
  · cases b <;> simp [contextBranch,hi]

/-- The two context branches at any coordinate sum to the identity. -/
theorem contextBranch_sum (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S)) (j : Fin (Fintype.card V)) :
    (contextBranch S I j false).mat+(contextBranch S I j true).mat=1 := by
  by_cases hi : (Fintype.equivFin V).symm j∈I.val
  · simpa only [contextBranch,if_pos hi,HermitianMat.mat_add,HermitianMat.mat_one] using
      congrArg HermitianMat.mat (involutionProjector_sum (S ((Fintype.equivFin V).symm j)))
  · simp [contextBranch,hi]

/-- All context branches commute with one another. -/
theorem contextBranch_commute (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : Fin (Fintype.card V)) (a : Bool) (j : Fin (Fintype.card V)) (b : Bool) :
    Commute (contextBranch S I i a).mat (contextBranch S I j b).mat := by
  by_cases hi : (Fintype.equivFin V).symm i∈I.val
  · by_cases hj : (Fintype.equivFin V).symm j∈I.val
    · simpa only [contextBranch,if_pos hi,if_pos hj] using
        involutionProjector_commute _ _ (context_observables_commute S I _ _ hi hj) a b
    · cases b <;> simp [contextBranch,hi,hj,Commute,SemiconjBy]
  · cases a <;> simp [contextBranch,hi,Commute,SemiconjBy]

/-- The joint POVM obtained by multiplying the binary branches of the commuting involutions in
the context. -/
def contextPOVM (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1)
    (I : Context (commutationGraph S)) : POVM (Fin (Fintype.card V) → Bool) d :=
  binaryJointPOVM (Fintype.card V) (fun j b => (contextBranch S I j b).mat)
    (fun j b => (contextBranch S I j b).H) (contextBranch_idempotent S hS I)
    (contextBranch_commute S I) (contextBranch_sum S I)

/-- The outcome sign for observable `i` inside the context, and zero outside the context. -/
def contextSign (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : V) (s : Fin (Fintype.card V) → Bool) : ℝ := if i∈I.val then binarySign (s (Fintype.equivFin V i)) else 0

omit [DecidableEq d] in

/-- The square of a context sign equals the indicator of context membership. -/
theorem contextSign_square (S : V → HermitianMat d ℂ) (I : Context (commutationGraph S))
    (i : V) (s : Fin (Fintype.card V) → Bool) : (contextSign S I i s)^2=if i∈I.val then 1 else 0 := by
  unfold contextSign
  split_ifs <;> simp [binarySign_sq]

/-- The signed marginal of the context POVM equals the observable inside the context and zero
outside it, implementing the joint-measurement marginal used in [XuEtAl2026]. -/
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

/-- An observable restricted to the context acts on each joint POVM effect by multiplication by
the corresponding context sign. -/
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

/-- The joint scheme formed from the context POVMs and their outcome signs for a family of
Hermitian involutions. -/
def commutingJointScheme (S : V → HermitianMat d ℂ) (hS : ∀ i,(S i).mat*(S i).mat=1) :
    JointScheme (K:=Context (commutationGraph S)) (Ω:=Fin (Fintype.card V) → Bool) S where
  context I := I.val
  measurement I := contextPOVM S hS I
  sign I i s := contextSign S I i s
  sign_sq := contextSign_square S
  marginal := contextPOVM_marginal S hS

end Qatlib.Foundations.FiniteStats.BornEstimator
