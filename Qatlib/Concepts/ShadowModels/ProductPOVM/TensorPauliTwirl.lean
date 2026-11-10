/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
import QuantumInfo.Measurements.POVM
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ProductPOVM
open scoped Classical BigOperators
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel

theorem one_qubit_completeness (r t u v : Bool) :
    (∑ p : Pauli1,P1 p r u*star (P1 p t v))=
      (2:ℂ)*(if r=t then 1 else 0)*(if u=v then 1 else 0) := by
  have hu : (Finset.univ : Finset Pauli1)={.I,.X,.Y,.Z} := by
    ext p
    cases p <;> simp
  rw [hu]
  cases r <;> cases t <;> cases u <;> cases v <;> simp [P1] <;> norm_num

theorem tensor_pauli_completeness (n : ℕ) (r t u v : Reg n) :
    (∑ w : PauliWord n,pauliWordOp n w r u*star (pauliWordOp n w t v))=
      (2:ℂ)^n*(if r=t then 1 else 0)*(if u=v then 1 else 0) := by
  have hp (w : PauliWord n) :
      pauliWordOp n w r u*star (pauliWordOp n w t v)=∏ i,P1 (w i) (r i) (u i)*star (P1 (w i) (t i) (v i)) := by
    simp only [pauliWordOp_eq,productMatrix,star_prod,Finset.prod_mul_distrib]
  simp_rw [hp]
  rw [show (∑ w : PauliWord n,∏ i,P1 (w i) (r i) (u i)*star (P1 (w i) (t i) (v i))) =
    ∏ i,∑ p : Pauli1,P1 p (r i) (u i)*star (P1 p (t i) (v i)) from
      (Fintype.prod_sum (fun i p => P1 p (r i) (u i)*star (P1 p (t i) (v i)))).symm]
  simp_rw [one_qubit_completeness]
  by_cases hrt : r=t
  · subst t
    by_cases huv : u=v
    · subst v
      simp
    · have he : ∃ i,u i≠v i := not_forall.mp (fun h => huv (funext h))
      obtain ⟨i,hi⟩ := he
      rw [if_pos rfl,if_neg huv,mul_zero]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  · have he : ∃ i,r i≠t i := not_forall.mp (fun h => hrt (funext h))
    obtain ⟨i,hi⟩ := he
    rw [if_neg hrt,mul_zero,zero_mul]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem tensor_pauli_twirl (n : ℕ) (A : Matrix (Reg n) (Reg n) ℂ) :
    (∑ w : PauliWord n,pauliWordOp n w*A*(pauliWordOp n w)ᴴ)=
      ((2:ℂ)^n*A.trace) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  ext r t
  simp only [Matrix.sum_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,Finset.sum_mul]
  calc (∑ w,∑ b,∑ a,pauliWordOp n w r a*A a b*star (pauliWordOp n w t b))=
      ∑ b,∑ a,∑ w,pauliWordOp n w r a*A a b*star (pauliWordOp n w t b) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
    _ = ∑ b,∑ a,A a b*((2:ℂ)^n*(if r=t then 1 else 0)*(if a=b then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      rw [← tensor_pauli_completeness]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by
      by_cases h : r=t
      · subst t
        simp [Matrix.trace,Finset.mul_sum,mul_comm,mul_left_comm]
      · simp [h]

end Qatlib.Concepts.ShadowModels.ProductPOVM
