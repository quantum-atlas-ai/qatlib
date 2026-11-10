/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeAndOr
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib MvPolynomial
open scoped BigOperators Classical
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

private theorem full_coefficient_degree {I : Type} [Fintype I] [DecidableEq I]
    (q : MvPolynomial I ℝ) (hq : q.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) ≠ 0) :
    Fintype.card I ≤ q.totalDegree := by
  have h := le_totalDegree (mem_support_iff.mpr hq)
  have ht : (Finsupp.equivFunOnFinite.symm (fun _ : I => 1)).sum (fun _ k => k)=Fintype.card I := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp
  simpa only [ht] using h

theorem sameCircuit_and_lower {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W))
    (hbad : ∀ g : I → Bool, (∃ i, g i = false) →
      MeasureProb (Run (TensorGate (BitOracleOn g) 1) C ψ) E = 0)
    (hgood : 0 < MeasureProb
      (Run (TensorGate (BitOracleOn (fun _ : I => true)) 1) C ψ) E) :
    Fintype.card I ≤ QueryCount C := by
  let run := fun g : I → Bool => Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) C ψ
  change 0 < ∑ q ∈ E, ‖run (fun _ => true) q‖^2 at hgood
  obtain ⟨q,hqE,hqpos⟩ : ∃ q ∈ E, 0 < ‖run (fun _ => true) q‖^2 := by
    by_contra he
    have hs : (∑ q ∈ E, ‖run (fun _ => true) q‖^2) ≤ 0 :=
      Finset.sum_nonpos (fun q hq => not_lt.mp (fun h => he ⟨q,hq,h⟩))
    exact (not_le_of_gt hgood) hs
  let a : ℂ := run (fun _ => true) q
  have ha : a ≠ 0 := by
    intro he
    change 0 < ‖a‖^2 at hqpos
    rw [he,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hqpos
    norm_num at hqpos
  let P := amplitudePolynomial C ψ q
  let R : MvPolynomial I ℂ := MvPolynomial.C a⁻¹*P
  let p := realPart R
  have hP : P.totalDegree ≤ QueryCount C := amplitude_polynomial_actual_query_degree C ψ q
  have hR : R.totalDegree ≤ P.totalDegree := by
    simpa only [R,totalDegree_C,zero_add] using totalDegree_mul (MvPolynomial.C a⁻¹) P
  have hpdegree : p.totalDegree ≤ QueryCount C :=
    (realPart_totalDegree_le R).trans (hR.trans hP)
  have hPeval (g : I → Bool) : eval (fun i => (boolPoint g i : ℂ)) P=run g q := by
    have hcast : (fun i : I => (boolPoint g i : ℂ))=(fun i => if g i then (1 : ℂ) else 0) := by
      ext i
      cases hi : g i <;> simp [boolPoint,hi]
    rw [hcast]
    exact amplitude_polynomial_boolean_run_evaluation C ψ g q
  have hp : ∀ g : I → Bool, eval (fun i => if g i then (1 : ℝ) else 0) p=
      if (∀ i, g i=true) then 1 else 0 := by
    intro g
    change eval (boolPoint g) (realPart R)=_
    rw [realPart_eval]
    change (eval (fun i => (boolPoint g i : ℂ)) (MvPolynomial.C a⁻¹*P)).re=_
    rw [eval_mul,eval_C,hPeval]
    by_cases hg : ∀ i, g i=true
    · have htrue : g=(fun _ => true) := funext hg
      rw [htrue]
      change (a⁻¹*a).re=if (∀ _ : I, true=true) then 1 else 0
      simp [ha]
    · have hf : ∃ i, g i=false := by
        obtain ⟨i,hi⟩ := not_forall.mp hg
        exact ⟨i,Bool.eq_false_of_not_eq_true hi⟩
      have hsum : (∑ r ∈ E, ‖run g r‖^2)=0 := hbad g hf
      have hle : ‖run g q‖^2 ≤ 0 :=
        (Finset.single_le_sum (fun r _ => sq_nonneg ‖run g r‖) hqE).trans hsum.le
      have ham : run g q=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (run g q)])
      simp [hg,ham]
  exact (boolean_multilinear_and_totalDegree p hp).trans hpdegree

end Qatlib.Concepts.QueryComplexity.DegreeMethod
