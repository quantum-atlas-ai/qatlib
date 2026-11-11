/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyRotationFigTwoDefs
import Qatlib.Concepts.RiskEstimation.PolyRotation.PolyControlledRotationCorrected
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Subset coefficients for polynomial rotation angles

This module defines the corrected Figure 2 program and finite-cube subset coefficients. Powerset
inversion and polynomial finite differences show that coefficients above the polynomial degree
vanish, and connect these coefficients to binary register evaluation.

The polynomial payoff-rotation setting is described in [WoernerEgger2019].

## Main statements

* `figCubeCoeff_inversion`: Summing all subset coefficients over the powerset of `S` recovers
  the original function at `S`.
* `figCubeCoeff_polynomial_vanish`: For a polynomial of degree at most `k`, the subset
  coefficient of its weighted subset-sum evaluation vanishes on sets of cardinality greater than
  `k`.

## References

* [Woerner and Egger, 2019][WoernerEgger2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PolyRotation
open Matrix Polynomial
open scoped Classical BigOperators

/-- The Figure 2 rotation word assembled using corrected subset rotations and subset-angle
coefficients. -/
def figTwoProgramCorrected {n : ℕ} (k : ℕ) (g : Reg n → ℝ) : List (ReflectionGate (n+1+(n-1))) :=
  figTwoRotationStepsCorrected (figTwoTargetWire n) (figTwoWorkWires n)
    ((figTwoTerms k).map fun l=>(l.map (figTwoDataWire n),figTwoAngle g l.toFinset))

/-- The alternating powerset coefficient of a real-valued function on finite sets. -/
def figCubeCoeff {α : Type} [DecidableEq α] (g : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ T∈S.powerset,(-1 : ℝ)^(S.card-T.card)*g T

/-- Inserting a new element into a subset coefficient equals taking the coefficient of the
corresponding first-difference function. -/
theorem figCubeCoeff_insert {α : Type} [DecidableEq α] (g : Finset α → ℝ)
    (S : Finset α) (a : α) (ha : a∉S) :
    figCubeCoeff g (insert a S)=figCubeCoeff (fun T=>g (insert a T)-g T) S := by
  unfold figCubeCoeff
  rw [Finset.sum_powerset_insert ha,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hsub : T⊆S := Finset.mem_powerset.mp hT
  have haT : a∉T := fun hh=>ha (hsub hh)
  have hc : T.card ≤ S.card := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem ha,Finset.card_insert_of_notMem haT]
  have he1 : S.card+1-T.card=(S.card-T.card)+1 := by omega
  have he2 : S.card+1-(T.card+1)=S.card-T.card := by omega
  rw [he1,he2,pow_succ]
  ring

/-- Summing all subset coefficients over the powerset of `S` recovers the original function at
`S`. -/
theorem figCubeCoeff_inversion {α : Type} [DecidableEq α] (S : Finset α)
    (g : Finset α → ℝ) : (∑ T∈S.powerset,figCubeCoeff g T)=g S := by
  induction S using Finset.induction_on generalizing g with
  | empty=>simp [figCubeCoeff]
  | @insert a S ha ih=>
    rw [Finset.sum_powerset_insert ha]
    have he : (∑ T∈S.powerset,figCubeCoeff g (insert a T))=
        ∑ T∈S.powerset,figCubeCoeff (fun U=>g (insert a U)-g U) T := by
      apply Finset.sum_congr rfl
      intro T hT
      exact figCubeCoeff_insert g T a (fun hh=>ha (Finset.mem_powerset.mp hT hh))
    rw [he,ih g,ih (fun T=>g (insert a T)-g T)]
    ring

/-- Subset coefficients agree when their underlying functions agree on every subset of `S`. -/
theorem figCubeCoeff_congr {α : Type} [DecidableEq α] (g h : Finset α → ℝ)
    (S : Finset α) (he : ∀ T,T⊆S → g T=h T) : figCubeCoeff g S=figCubeCoeff h S := by
  unfold figCubeCoeff
  exact Finset.sum_congr rfl fun T hT=>congrArg (fun z : ℝ=>(-1 : ℝ)^(S.card-T.card)*z)
    (he T (Finset.mem_powerset.mp hT))

/-- If a polynomial has degree at most `k + 1`, its translated difference has degree at most
`k`. -/
theorem figPolynomial_difference_degree (p : Polynomial ℝ) (h : ℝ) (k : ℕ)
    (hp : p.natDegree ≤ k+1) : (Polynomial.taylor h p-p).natDegree ≤ k := by
  by_cases hz : p=0
  · simp [hz]
  by_cases hd : Polynomial.taylor h p-p=0
  · simp [hd]
  have ht : Polynomial.taylor h p≠0 := (Polynomial.taylor_eq_zero h p).not.mpr hz
  have hl:=Polynomial.degree_sub_lt (Polynomial.degree_taylor p h) ht
    (Polynomial.leadingCoeff_taylor (r := h) (f := p))
  rw [Polynomial.degree_eq_natDegree hd,Polynomial.degree_taylor,Polynomial.degree_eq_natDegree hz] at hl
  have hn : (Polynomial.taylor h p-p).natDegree < p.natDegree := by exact_mod_cast hl
  omega

/-- For a polynomial of degree at most `k`, the subset coefficient of its weighted subset-sum
evaluation vanishes on sets of cardinality greater than `k`. -/
theorem figCubeCoeff_polynomial_vanish {α : Type} [DecidableEq α] (w : α → ℝ) :
    ∀ (k : ℕ) (p : Polynomial ℝ) (S : Finset α),p.natDegree ≤ k → k < S.card →
    figCubeCoeff (fun T=>p.eval (∑ i∈T,w i)) S=0 := by
  intro k
  induction k with
  | zero=>
    intro p S hp hcard
    obtain ⟨a,ha⟩:=Finset.card_pos.mp hcard
    have hpc : p=Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hp
    rw [← Finset.insert_erase ha,figCubeCoeff_insert _ _ _ (by simp)]
    have hev (y : ℝ) : p.eval y=p.coeff 0 := by
      simpa only [Polynomial.eval_C] using! congrArg (fun q : Polynomial ℝ=>q.eval y) hpc
    simp [figCubeCoeff,hev]
  | succ k ih=>
    intro p S hp hcard
    have hpos : 0 < S.card := by omega
    obtain ⟨a,ha⟩:=Finset.card_pos.mp hpos
    let q:=Polynomial.taylor (w a) p-p
    have hq : q.natDegree ≤ k := figPolynomial_difference_degree p (w a) k hp
    have hc : k < (S.erase a).card := by
      have he:=Finset.card_erase_add_one ha
      omega
    rw [← Finset.insert_erase ha,figCubeCoeff_insert _ _ _ (by simp)]
    have he : figCubeCoeff (fun T=>p.eval (∑ i∈insert a T,w i)-p.eval (∑ i∈T,w i)) (S.erase a)=
        figCubeCoeff (fun T=>q.eval (∑ i∈T,w i)) (S.erase a) := by
      apply figCubeCoeff_congr
      intro T hT
      have haT : a∉T := fun hh=>Finset.notMem_erase a S (hT hh)
      rw [Finset.sum_insert haT]
      simp [q,Polynomial.taylor_apply,Polynomial.eval_comp,add_comm]
    rw [he]
    exact ih q (S.erase a) hq hc

/-- The real cast of a register's binary value on a subset indicator equals the sum of its
binary weights. -/
theorem figTwoRegEval_indicator {n : ℕ} (S : Finset (Fin n)) :
    (figTwoRegEval (fun i=>decide (i∈S)) : ℝ)=∑ i∈S,(2 : ℝ)^i.val := by
  have hf : (Finset.univ.filter (fun i : Fin n=>decide (i∈S)=true))=S := by ext i;simp
  rw [figTwoRegEval,hf]
  push_cast
  rfl

/-- The polynomial register-angle coefficient equals the finite-cube coefficient of the
polynomial evaluated at weighted subset sums. -/
theorem figTwoAngle_polynomial_cube {n : ℕ} (p : Polynomial ℝ) (S : Finset (Fin n)) :
    figTwoAngle (fun x : Reg n=>p.eval (figTwoRegEval x : ℝ)) S=
      figCubeCoeff (fun T=>p.eval (∑ i∈T,(2 : ℝ)^i.val)) S := by
  unfold figTwoAngle figCubeCoeff
  simp_rw [figTwoRegEval_indicator]

end Qatlib.Concepts.RiskEstimation.PolyRotation
