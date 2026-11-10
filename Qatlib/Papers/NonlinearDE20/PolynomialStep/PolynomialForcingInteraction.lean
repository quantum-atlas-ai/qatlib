/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinearDE20.PolynomialStep.Polynomial
import Mathlib.LinearAlgebra.Matrix.Kronecker
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open scoped BigOperators Classical ComplexOrder Kronecker
open Matrix
open Qatlib.Papers.NonlinearDE20.AffineLift.Model

open Qatlib.Concepts.TensorRegisters.RegisterModel.EnvironmentFrame

namespace Qatlib.Papers.NonlinearDE20.PolynomialStep.Model

def liftedInteraction {I E : Type} (B : Matrix (I×E) (I×E) ℂ) : Matrix (Option I×E) (Option I×E) ℂ
  | (some i,a),(some j,b)=>B (i,a) (j,b)
  | _,_=>0

def forcedInteraction {I E : Type} [DecidableEq I] [DecidableEq E] (A : Matrix I I ℂ)
    (B : Matrix (I×E) (I×E) ℂ) (b : I→ℂ) : Matrix (Option I×E) (Option I×E) ℂ :=
  (affineMatrix A b ⊗ₖ (1:Matrix E E ℂ))+liftedInteraction B

theorem targetGate_inflate {I E : Type} [Fintype I] [Fintype E] [DecidableEq E]
    (A : Matrix I I ℂ) (q : E→ℂ) (x : I→ℂ) :
    (A ⊗ₖ (1:Matrix E E ℂ))*ᵥ inflate q x=inflate q (A*ᵥ x) := by
  funext p
  rcases p with ⟨i,a⟩
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kroneckerMap_apply,Matrix.one_apply,
    inflate,mul_ite,ite_mul,Finset.sum_mul,mul_assoc]

theorem liftedInteraction_some {I E : Type} [Fintype I] [Fintype E]
    (B : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) (i : I) (a : E) :
    (liftedInteraction B*ᵥ inflate q (homogenize x)) (some i,a)=(B*ᵥ inflate q x) (i,a) := by
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Fintype.sum_option,liftedInteraction,inflate,homogenize]

theorem liftedInteraction_none {I E : Type} [Fintype I] [Fintype E]
    (B : Matrix (I×E) (I×E) ℂ) (q : E→ℂ) (x : I→ℂ) (a : E) :
    (liftedInteraction B*ᵥ inflate q (homogenize x)) (none,a)=0 := by
  simp [Matrix.mulVec,dotProduct,liftedInteraction]

theorem forcedInteraction_some {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (A : Matrix I I ℂ) (B : Matrix (I×E) (I×E) ℂ) (b x : I→ℂ) (q : E→ℂ) (i : I) (a : E) :
    (forcedInteraction A B b*ᵥ inflate q (homogenize x)) (some i,a)=
      inflate q (A*ᵥ x+b) (i,a)+(B*ᵥ inflate q x) (i,a) := by
  rw [forcedInteraction,Matrix.add_mulVec,targetGate_inflate]
  change (affineMatrix A b*ᵥ homogenize x) (some i)*q a+_= _
  rw [affineMatrix_some,liftedInteraction_some]
  rfl

theorem forcedInteraction_none {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (A : Matrix I I ℂ) (B : Matrix (I×E) (I×E) ℂ) (b x : I→ℂ) (q : E→ℂ) (a : E) :
    (forcedInteraction A B b*ᵥ inflate q (homogenize x)) (none,a)=0 := by
  rw [forcedInteraction,Matrix.add_mulVec,targetGate_inflate]
  simp [inflate,affineMatrix_none,liftedInteraction_none]

def originalTargetSelector {I E : Type} [DecidableEq I] [DecidableEq E] : Matrix (I×E) (Option I×E) ℂ :=
  fun p v=>if v=(some p.1,p.2) then 1 else 0

theorem originalTargetSelector_action {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (v : Option I×E→ℂ) (p : I×E) :
    (originalTargetSelector*ᵥ v) p=v (some p.1,p.2) := by
  simp [originalTargetSelector,Matrix.mulVec,dotProduct,ite_mul]

theorem originalTargetSelector_coisometry {I E : Type} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E] :
    (originalTargetSelector (I:=I) (E:=E))*(originalTargetSelector (I:=I) (E:=E))ᴴ=1 := by
  ext p q
  rcases p with ⟨i,a⟩
  rcases q with ⟨j,b⟩
  simp [originalTargetSelector,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_ite,Matrix.one_apply,
    Prod.mk.injEq,eq_comm]

theorem forced_polynomial_program {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (A : Matrix I I ℂ)
    (B : Matrix (I×(Fin m→I)) (I×(Fin m→I)) ℂ) (b x : I→ℂ) (dt : ℂ) :
    originalTargetSelector*ᵥ ((1+dt •forcedInteraction A B b)*ᵥ inflate (tensorPower m x) (homogenize x))=
      polynomialJointEuler m A B b x dt := by
  funext p
  rcases p with ⟨i,a⟩
  rw [originalTargetSelector_action,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  change x i*tensorPower m x a+dt*(forcedInteraction A B b*ᵥ inflate (tensorPower m x) (homogenize x)) (some i,a)=_
  rw [forcedInteraction_some]
  simp only [polynomialJointEuler,inflate,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

end Qatlib.Papers.NonlinearDE20.PolynomialStep.Model
