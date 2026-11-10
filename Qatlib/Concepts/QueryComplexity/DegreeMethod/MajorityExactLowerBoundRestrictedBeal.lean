/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityExactLowerBoundRestrictedStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open MvPolynomial

private theorem fixedFalse_degree {K J : Type} [Fintype K] [DecidableEq K]
    [Fintype J] [DecidableEq J] (p : MvPolynomial (K ⊕ J) ℝ) :
    (killCompl (Sum.inl_injective : Function.Injective (Sum.inl : K → K ⊕ J)) p).totalDegree ≤
      p.totalDegree := by
  classical
  let h : Function.Injective (Sum.inl : K → K ⊕ J) := Sum.inl_injective
  change ((killCompl h p).support.sup (fun d => d.sum (fun _ k => k))) ≤ p.totalDegree
  apply Finset.sup_le
  intro d hd
  have hc : p.coeff (d.mapDomain (Sum.inl : K → K ⊕ J)) ≠ 0 := by
    rw [← coeff_killCompl h]
    exact mem_support_iff.mp hd
  have ht := le_totalDegree (mem_support_iff.mpr hc)
  have hsum : (d.mapDomain (Sum.inl : K → K ⊕ J)).sum (fun _ k => k)=d.sum (fun _ k => k) :=
    Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)
  rw [hsum] at ht
  exact ht

private theorem fixedFalse_eval {K J : Type} [Fintype K] [DecidableEq K]
    [Fintype J] [DecidableEq J] (p : MvPolynomial (K ⊕ J) ℝ) (g : K → Bool) :
    eval (boolPoint g) (killCompl (Sum.inl_injective : Function.Injective (Sum.inl : K → K ⊕ J)) p)=
      eval (boolPoint (Sum.elim g (fun _ : J => false))) p := by
  classical
  let h : Function.Injective (Sum.inl : K → K ⊕ J) := Sum.inl_injective
  have hinl (k : K) : killCompl h (X (Sum.inl k))=(X k : MvPolynomial K ℝ) := by
    simpa only [rename_X] using killCompl_rename_app h (X k : MvPolynomial K ℝ)
  have hinr (j : J) : killCompl h (X (Sum.inr j))=(0 : MvPolynomial K ℝ) := by
    simp [killCompl]
  have he : (aeval (R := ℝ) (boolPoint g)).comp (killCompl h)=
      aeval (R := ℝ) (boolPoint (Sum.elim g (fun _ : J => false))) := by
    apply algHom_ext
    intro i
    cases i with
    | inl k => simp [AlgHom.comp_apply,hinl,boolPoint]
    | inr j => simp [AlgHom.comp_apply,hinr,boolPoint]
  simpa only [AlgHom.comp_apply,aeval_eq_eval] using AlgHom.congr_fun he p

theorem majorityExactQueryLowerBoundRestricted : MajorityExactQueryLowerBoundRestricted := by
  classical
  intro K J W _ _ _ _ _ _ C ψ E1 _ hs
  let P := booleanAcceptancePolynomial C ψ E1
  let pK := killCompl (Sum.inl_injective : Function.Injective (Sum.inl : K → K ⊕ J)) P
  obtain ⟨hdegree,_,heval⟩ := acceptance_boolean_multilinearization_preserves_run C ψ E1
  have hrep : ∀ g : K → Bool, eval (fun k => if g k then (1 : ℝ) else 0) pK=
      if (∀ k, g k=true) then 1 else 0 := by
    intro g
    exact (fixedFalse_eval P g).trans ((heval _).trans (hs g))
  exact ((boolean_multilinear_and_totalDegree pK hrep).trans (fixedFalse_degree P)).trans hdegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
