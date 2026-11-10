/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryWordCore.QueryMachinery.AcceptancePolynomial
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open MvPolynomial
open scoped BigOperators

private noncomputable def cubeComplementSign {I : Type} [Fintype I] (g : I → Bool) : ℝ :=
  ∏ i, if g i then 1 else -1

private theorem cube_monomial_top_sum {I : Type} [Fintype I] [DecidableEq I]
    (d : I →₀ ℕ) :
    (∑ g : I → Bool, cubeComplementSign g * ∏ i, (boolPoint g i)^d i)=
      if (∀ i, d i ≠ 0) then (1 : ℝ) else 0 := by
  classical
  have hp : (∑ g : I → Bool, cubeComplementSign g * ∏ i, (boolPoint g i)^d i)=
      ∏ i, ∑ b : Bool, (if b then (1 : ℝ) else -1)*(if b then (1 : ℝ) else 0)^d i := by
    simp_rw [cubeComplementSign,← Finset.prod_mul_distrib]
    simpa only [boolPoint] using!
      (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
        (fun i b => (if b then (1 : ℝ) else -1)*(if b then (1 : ℝ) else 0)^d i)).symm
  rw [hp]
  by_cases h : ∀ i, d i ≠ 0
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i _
    simp [h i]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    have hdi : d i=0 := not_ne_iff.mp hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hdi])

private theorem cube_top_coefficient {I : Type} [Fintype I] [DecidableEq I]
    (q : MvPolynomial I ℝ)
    (hml : ∀ d : I →₀ ℕ, q.coeff d ≠ 0 → ∀ i, d i ≤ 1) :
    q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)=
      ∑ g : I → Bool, cubeComplementSign g * eval (boolPoint g) q := by
  classical
  let top : I →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => 1
  symm
  simp only [eval_eq',Finset.mul_sum]
  rw [Finset.sum_comm]
  have ht (d : I →₀ ℕ) :
      (∑ g : I → Bool, cubeComplementSign g * (q.coeff d * ∏ i, (boolPoint g i)^d i))=
      q.coeff d * (if ∀ i, d i ≠ 0 then (1 : ℝ) else 0) := by
    rw [← cube_monomial_top_sum d,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    ring
  simp_rw [ht]
  rw [Finset.sum_eq_single top]
  · simp [top]
  · intro d hd hdt
    have hn : ¬ ∀ i, d i ≠ 0 := by
      intro h
      apply hdt
      ext i
      have hdi := hml d (mem_support_iff.mp hd) i
      have hn := h i
      have ht : top i=1 := by simp [top]
      rw [ht]
      omega
    simp [hn]
  · intro hn
    simp [top,mem_support_iff] at hn ⊢
    exact hn

private noncomputable def cubeFinsetEquiv {I : Type} [Fintype I] [DecidableEq I] :
    (I → Bool) ≃ Finset I where
  toFun := boolSupp
  invFun S := fun i => decide (i ∈ S)
  left_inv g := by
    ext i
    simp only [boolSupp,Finset.mem_filter,Finset.mem_univ,true_and]
    cases g i <;> rfl
  right_inv S := boolSupp_decide S

private theorem complementSign_support {I : Type} [Fintype I] [DecidableEq I] (g : I → Bool) :
    cubeComplementSign g=(-1 : ℝ)^((Finset.univ \ boolSupp g).card) := by
  classical
  simp [cubeComplementSign,Finset.prod_ite,boolSupp,Finset.sdiff_eq_filter]

private theorem cube_subset_sum {I : Type} [Fintype I] [DecidableEq I]
    (q : MvPolynomial I ℝ) :
    (∑ g : I → Bool, cubeComplementSign g * eval (boolPoint g) q)=
      ∑ S ∈ Finset.univ.powerset, (-1 : ℝ)^((Finset.univ \ S).card)*
        eval (fun i => if i ∈ S then (1 : ℝ) else 0) q := by
  classical
  have he (g : I → Bool) :
      cubeComplementSign g * eval (boolPoint g) q=
      (-1 : ℝ)^((Finset.univ \ cubeFinsetEquiv g).card)*
        eval (fun i => if i ∈ cubeFinsetEquiv g then (1 : ℝ) else 0) q := by
    rw [complementSign_support]
    congr 1
    apply congrArg (fun x => eval x q)
    ext i
    change boolPoint g i=(if i ∈ boolSupp g then (1 : ℝ) else 0)
    simp [boolPoint,boolSupp]
  simp_rw [he]
  simpa only [Finset.powerset_univ] using cubeFinsetEquiv.sum_comp
    (fun S : Finset I => (-1 : ℝ)^((Finset.univ \ S).card)*
      eval (fun i => if i ∈ S then (1 : ℝ) else 0) q)

theorem mobius_top_coefficient {I : Type} [Fintype I] [DecidableEq I]
    (q : MvPolynomial I ℝ)
    (hml : ∀ d : I →₀ ℕ, q.coeff d ≠ 0 → ∀ i : I, d i ≤ 1) :
    q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1)
      = ∑ S ∈ Finset.univ.powerset,
          (-1 : ℝ) ^ ((Finset.univ \ S).card)
            * MvPolynomial.eval (fun i => if i ∈ S then (1 : ℝ) else 0) q :=
  (cube_top_coefficient q hml).trans (cube_subset_sum q)

private theorem full_coefficient_degree {I : Type} [Fintype I] [DecidableEq I]
    (q : MvPolynomial I ℝ) (hq : q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) ≠ 0) :
    Fintype.card I ≤ q.totalDegree := by
  have h := le_totalDegree (mem_support_iff.mpr hq)
  have ht : (Finsupp.equivFunOnFinite.symm (fun _ : I => 1)).sum (fun _ k => k)=Fintype.card I := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp
  simpa only [ht] using h

theorem boolean_multilinear_and_totalDegree {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ)
    (hp : ∀ g : I → Bool,
        MvPolynomial.eval (fun i => if g i then (1 : ℝ) else 0) p
          = if (∀ i : I, g i = true) then (1 : ℝ) else 0) :
    Fintype.card I ≤ p.totalDegree := by
  classical
  let q := multilinearize p
  have hq (g : I → Bool) : eval (boolPoint g) q=if (∀ i, g i=true) then 1 else 0 := by
    rw [multilinearize_eval]
    · exact hp g
    · intro i
      cases g i <;> simp [boolPoint]
  have htop := (mobius_top_coefficient q (multilinearize_coeff_multilinear p)).trans
    (cube_subset_sum q).symm
  have hsum : (∑ g : I → Bool, cubeComplementSign g * eval (boolPoint g) q)=1 := by
    rw [Finset.sum_eq_single (fun _ => true)]
    · simp [hq,cubeComplementSign]
    · intro g _ hg
      have hfalse : ¬ ∀ i, g i=true := fun h => hg (funext h)
      simp [hq,hfalse]
    · simp
  have hcoef : q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) ≠ 0 := by
    rw [htop,hsum]
    norm_num
  exact (full_coefficient_degree q hcoef).trans (multilinearize_totalDegree_le p)

theorem boolean_multilinear_or_totalDegree {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (hn : 0 < Fintype.card I)
    (hp : ∀ g : I → Bool, eval (fun i => if g i then (1 : ℝ) else 0) p=
      if (∃ i, g i=true) then 1 else 0) : Fintype.card I ≤ p.totalDegree := by
  classical
  let q := multilinearize p
  have hq (g : I → Bool) : eval (boolPoint g) q=if (∃ i, g i=true) then 1 else 0 := by
    rw [multilinearize_eval]
    · exact hp g
    · intro i
      cases g i <;> simp [boolPoint]
  have hsum : (∑ g : I → Bool, cubeComplementSign g)=0 := by
    have he : (∑ g : I → Bool, cubeComplementSign g)=
        ∏ i : I, ∑ b : Bool, if b then (1 : ℝ) else -1 := by
      simpa only [cubeComplementSign] using!
        (Finset.prod_univ_sum (fun _ : I => (Finset.univ : Finset Bool))
          (fun _ b => if b then (1 : ℝ) else -1)).symm
    rw [he]
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hterm (g : I → Bool) : cubeComplementSign g * eval (boolPoint g) q=
      cubeComplementSign g - if g=(fun _ => false) then cubeComplementSign (fun _ : I => false) else 0 := by
    by_cases hg : g=(fun _ => false)
    · subst g
      simp [hq]
    · have hex : ∃ i, g i=true := by
        by_contra he
        apply hg
        ext i
        cases hi : g i
        · rfl
        · exact (he ⟨i,hi⟩).elim
      simp [hq,hex,hg]
  have htop := (mobius_top_coefficient q (multilinearize_coeff_multilinear p)).trans
    (cube_subset_sum q).symm
  have hcoef : q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) ≠ 0 := by
    rw [htop]
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib,hsum]
    simp [cubeComplementSign]
  exact (full_coefficient_degree q hcoef).trans (multilinearize_totalDegree_le p)

end Qatlib.Concepts.QueryComplexity.DegreeMethod
