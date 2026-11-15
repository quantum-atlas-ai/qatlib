/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.MatrixAlgebra.Permanent.PerturbedPermanentExpansionStat
public import Mathlib.GroupTheory.Perm.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.Permanent
open Matrix
open scoped Classical BigOperators

/-- Subtracting `r` from the upper-left matrix entry subtracts `r` times the permanent of the
complementary minor from the matrix permanent. -/
theorem perturbedPermanentExpansion : PerturbedPermanentExpansion := by
  intro n X r
  let Y : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => X i.succ j.succ
  let X' : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
      Matrix.of fun i j => if i=0 ∧ j=0 then X 0 0-r else X i j
  let P := fun σ : Equiv.Perm (Fin (n+1)) => ∏ i : Fin n, X (σ i.succ) i.succ
  have ht (σ : Equiv.Perm (Fin (n+1))) : (∏ i, X' (σ i) i) =
      (∏ i, X (σ i) i)-r*(if σ 0=0 then P σ else 0) := by
    have hrest : (∏ i : Fin n, X' (σ i.succ) i.succ)=P σ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [X',Fin.succ_ne_zero]
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ,hrest]
    change (if σ 0=0 ∧ (0 : Fin (n+1))=0 then X 0 0-r else X (σ 0) 0)*P σ =
      X (σ 0) 0*P σ-r*(if σ 0=0 then P σ else 0)
    by_cases h : σ 0=0 <;> simp [h]
    all_goals ring
  have hcoef : (∑ σ : Equiv.Perm (Fin (n+1)), if σ 0=0 then P σ else 0)=Matrix.permanent Y := by
    have he := Equiv.sum_comp (@Equiv.Perm.decomposeFin n).symm
      (fun σ : Equiv.Perm (Fin (n+1)) => if σ 0=0 then P σ else 0)
    rw [← he,Fintype.sum_prod_type]
    have hp (p : Fin (n+1)) : (∑ σ : Equiv.Perm (Fin n),
        if Equiv.Perm.decomposeFin.symm (p,σ) 0=0 then P (Equiv.Perm.decomposeFin.symm (p,σ)) else 0)=
          if p=0 then Matrix.permanent Y else 0 := by
      by_cases h : p=0
      · subst p
        unfold P Matrix.permanent Y
        apply Finset.sum_congr rfl
        intro σ _
        simp [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
      · simp [Equiv.Perm.decomposeFin_symm_apply_zero,h]
    simp only [hp,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change Matrix.permanent X'=Matrix.permanent X-r*Matrix.permanent Y
  unfold Matrix.permanent
  simp only [ht,Finset.sum_sub_distrib,← Finset.mul_sum]
  exact congrArg (fun a => (∑ σ : Equiv.Perm (Fin (n+1)), ∏ i, X (σ i) i)-r*a) hcoef

end Qatlib.Foundations.MatrixAlgebra.Permanent
