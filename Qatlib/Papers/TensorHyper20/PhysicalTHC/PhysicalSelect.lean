/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalModes
import Qatlib.Papers.TensorHyper20.MainResults.LambdaTHC
import Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalSelect
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner.WeightedModes
open Qatlib.Concepts.LcuPostselect.ScaledLCU.OrientedSelect
open PhysicalModes
open Qatlib.Papers.TensorHyper20.MainResults

abbrev Term (N M : ℕ) := Sum (Fin N×Fin 2) ((Fin M×Fin M)×(Fin 2×Fin 2))

def coefficient {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) : Term N M→ℝ
  | .inl x => -(t x.1)/2
  | .inr x => zeta x.1.1 x.1.2/8

def termSelect {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ) :
    Term N M→Matrix (Sum (Reg (N*2)) (Reg (N*2))) (Sum (Reg (N*2)) (Reg (N*2))) ℂ
  | .inl x => select (reflection (spinVector (tau x.1) x.2)) 1
  | .inr x => select (reflection (spinVector (chi x.1.1) x.2.1))
      (reflection (spinVector (chi x.1.2) x.2.2))

theorem actual_term_unitary {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (ht : ∀k,∑p,tau k p^2=1) (hc : ∀mu,∑p,chi mu p^2=1) (j : Term N M) :
    termSelect tau chi j∈Matrix.unitaryGroup (Sum (Reg (N*2)) (Reg (N*2))) ℂ := by
  cases j with
  | inl x =>
    apply select_unitary _ _ (reflection_hermitian _) Matrix.isHermitian_one
      (physical_reflection _ _ (ht x.1)).2
    simp
  | inr x =>
    exact select_unitary _ _ (reflection_hermitian _) (reflection_hermitian _)
      (physical_reflection _ _ (hc x.1.1)).2 (physical_reflection _ _ (hc x.1.2)).2

theorem actual_term_square {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (ht : ∀k,∑p,tau k p^2=1) (hc : ∀mu,∑p,chi mu p^2=1) (j : Term N M) :
    termSelect tau chi j*termSelect tau chi j=1 := by
  cases j with
  | inl x => exact select_square _ _ (physical_reflection _ _ (ht x.1)).2 (by simp)
  | inr x =>
    exact select_square _ _ (physical_reflection _ _ (hc x.1.1)).2
      (physical_reflection _ _ (hc x.1.2)).2

theorem actual_one_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (k : Fin N) (spin : Fin 2) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*termSelect tau chi (.inl (k,spin))*
      plusEmbedding (I:=Reg (N*2))=reflection (spinVector (tau k) spin) :=
  plus_select_one _

theorem actual_two_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ) (chi : Fin M→Fin N→ℝ)
    (mu nu : Fin M) (spin spin' : Fin 2) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*termSelect tau chi (.inr ((mu,nu),(spin,spin')))*
      plusEmbedding (I:=Reg (N*2))=(1/2:ℂ) •
      (reflection (spinVector (chi mu) spin)*reflection (spinVector (chi nu) spin')+
       reflection (spinVector (chi nu) spin')*reflection (spinVector (chi mu) spin)) :=
  plus_select_compression _ _

theorem actual_coefficient_mass {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) :
    (∑j : Term N M,|coefficient t zeta j|)=LambdaTHC.lambdaTHC t zeta := by
  simp only [Term,Fintype.sum_sum_type,Fintype.sum_prod_type,coefficient,
    abs_div,abs_neg,LambdaTHC.lambdaTHC,LambdaTHC.lambdaZeta]
  simp only [Fin.sum_univ_two]
  norm_num only [abs_of_nonneg (show (0:ℝ)≤2 by norm_num),abs_of_nonneg (show (0:ℝ)≤8 by norm_num)]
  simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.sum_mul]
  ring

theorem actual_coefficient_domination {N M : ℕ} (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ)
    (C : ℝ) (h : ∑k,|t k|≤C*LambdaTHC.lambdaZeta zeta) :
    (∑j : Term N M,|coefficient t zeta j|)≤(C+1)*LambdaTHC.lambdaZeta zeta := by
  rw [actual_coefficient_mass]
  exact LambdaTHC.lambdaTHC_asymptotic t zeta C h

theorem actual_lcu_compression {N M : ℕ} (tau : Fin N→Fin N→ℝ)
    (chi : Fin M→Fin N→ℝ) (t : Fin N→ℝ) (zeta : Fin M→Fin M→ℝ) :
    (plusEmbedding (I:=Reg (N*2)))ᴴ*
      (∑j : Term N M,coefficient t zeta j • termSelect tau chi j)*
      plusEmbedding (I:=Reg (N*2))=
    (∑k : Fin N,∑spin : Fin 2,(-(t k)/2) • reflection (spinVector (tau k) spin))+
    ∑mu : Fin M,∑nu : Fin M,∑spin : Fin 2,∑spin' : Fin 2,
      (zeta mu nu/8) • ((1/2:ℂ) •
        (reflection (spinVector (chi mu) spin)*reflection (spinVector (chi nu) spin')+
         reflection (spinVector (chi nu) spin')*reflection (spinVector (chi mu) spin))) := by
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    Fintype.sum_sum_type,Fintype.sum_prod_type,coefficient,
    actual_one_compression,actual_two_compression]

end Qatlib.Papers.TensorHyper20.PhysicalTHC.PhysicalSelect
