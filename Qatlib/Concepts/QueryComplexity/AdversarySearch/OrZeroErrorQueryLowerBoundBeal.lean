/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.OrZeroErrorQueryLowerBoundStat
import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrExactDegreeSubgoalBeal

/-!
# Zero error OR query lower bound

This module proves `orZeroErrorQueryLowerBound` by extracting a nonzero output amplitude on the
all false input and constructing an exact polynomial for OR. On a nonempty index type, an event
that occurs with positive probability only on the all false input forces at least one query per
input position, following the polynomial method of [BealsEtAl2001].

## Main statements

* `orZeroErrorQueryLowerBound`: a conclusive zero event for OR forces at least N queries.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Concepts.QueryComplexity.AdversarySearch
open MvPolynomial

/-- Any circuit with a conclusive zero event that has positive probability on the all false
input and zero probability on every nonzero input requires at least as many queries as input
positions, provided the index type is nonempty. This is the OR lower bound underlying [Beals
et al., Proposition 6.1 and Corollary 6.2][BealsEtAl2001]. -/
theorem orZeroErrorQueryLowerBound : OrZeroErrorQueryLowerBound := by
  classical
  intro I W _ _ _ _ C ψ E0 hn hno hpos
  let run := fun g : I → Bool => Run (TensorGate (BitOracleOn g) (1 : Matrix W W ℂ)) C ψ
  change 0 < ∑ q ∈ E0, ‖run (fun _ => false) q‖^2 at hpos
  obtain ⟨q,hqE,hqpos⟩ : ∃ q ∈ E0, 0 < ‖run (fun _ => false) q‖^2 := by
    by_contra he
    have hs : (∑ q ∈ E0, ‖run (fun _ => false) q‖^2) ≤ 0 :=
      Finset.sum_nonpos (fun q hq => not_lt.mp (fun h => he ⟨q,hq,h⟩))
    exact (not_le_of_gt hpos) hs
  let a : ℂ := run (fun _ => false) q
  have ha : a ≠ 0 := by
    intro he
    change 0 < ‖a‖^2 at hqpos
    rw [he,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hqpos
    norm_num at hqpos
  let P := amplitudePolynomial C ψ q
  let R : MvPolynomial I ℂ := MvPolynomial.C (1 : ℂ)-MvPolynomial.C a⁻¹*P
  let p := realPart R
  have hP : P.totalDegree ≤ QueryCount C := amplitude_polynomial_actual_query_degree C ψ q
  have hR : R.totalDegree ≤ P.totalDegree := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · simp
    · simpa only [totalDegree_C,zero_add] using totalDegree_mul (MvPolynomial.C a⁻¹) P
  have hpdegree : p.totalDegree ≤ QueryCount C :=
    (realPart_totalDegree_le R).trans (hR.trans hP)
  have hPeval (g : I → Bool) : eval (fun i => (boolPoint g i : ℂ)) P=run g q := by
    have hcast : (fun i : I => (boolPoint g i : ℂ))=(fun i => if g i then (1 : ℂ) else 0) := by
      ext i
      cases hi : g i <;> simp [boolPoint,hi]
    rw [hcast]
    exact amplitude_polynomial_boolean_run_evaluation C ψ g q
  have hp : ∀ g : I → Bool, eval (fun i => if g i then (1 : ℝ) else 0) p=
      if (∃ i, g i=true) then 1 else 0 := by
    intro g
    change eval (boolPoint g) (realPart R)=_
    rw [realPart_eval]
    change (eval (fun i => (boolPoint g i : ℂ)) (MvPolynomial.C (1 : ℂ)-MvPolynomial.C a⁻¹*P)).re=_
    rw [eval_sub,eval_C,eval_mul,eval_C,hPeval]
    by_cases hg : ∃ i, g i=true
    · have hsum : (∑ r ∈ E0, ‖run g r‖^2)=0 := hno g hg
      have hle : ‖run g q‖^2 ≤ 0 :=
        (Finset.single_le_sum (fun r _ => sq_nonneg ‖run g r‖) hqE).trans hsum.le
      have ham : run g q=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (run g q)])
      simp [hg,ham]
    · have hfalse : g=(fun _ => false) := by
        ext i
        cases hi : g i
        · rfl
        · exact (hg ⟨i,hi⟩).elim
      rw [hfalse]
      change (1-a⁻¹*a).re=if (∃ i : I, false=true) then 1 else 0
      simp [ha]
  exact (orExactDegreeSubgoal I p hn hp).trans hpdegree

end Qatlib.Concepts.QueryComplexity.AdversarySearch
