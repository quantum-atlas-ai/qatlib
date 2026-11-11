/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteInformationDivergence
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences

/-!
# Pinsker bounds for finite distributions

This module proves the variational lower bound for finite relative entropy and derives `pinsker`
for strictly positive probability masses. It then bounds the sum of testing errors for one
observation and for independent sample records. Relative entropy and distinguishability are
treated in [Watrous2018].

## Main statements

* `pinsker`: twice the squared total variation is bounded by relative entropy.
* `records_testing`: relative entropy controls testing errors for independent records.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinitePinsker
open FiniteInformationDivergence
open scoped BigOperators Classical
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in

/-- For strictly positive finite laws, an exponential-moment bound under `q` gives the lower
bound `p.expect g - c` on their relative entropy. -/
theorem variational_lower (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) (g : X → ℝ) (c : ℝ)
    (hmgf : q.expect (fun x => Real.exp (g x)) ≤ Real.exp c) :
    p.expect g - c ≤ kl p q := by
  have hpoint (x : X) :
      p.prob x*g x-c*p.prob x-p.prob x*(Real.log (p.prob x)-Real.log (q.prob x)) ≤
        Real.exp (-c)*(q.prob x*Real.exp (g x))-p.prob x := by
    have hr := mul_pos (hq x) (Real.exp_pos (g x-c))
    have hl := Real.log_le_sub_one_of_pos (div_pos hr (hp x))
    rw [Real.log_div hr.ne' (hp x).ne', Real.log_mul (hq x).ne'
      (Real.exp_ne_zero _), Real.log_exp] at hl
    have hm := mul_le_mul_of_nonneg_left hl (hp x).le
    have he : p.prob x*(q.prob x*Real.exp (g x-c)/p.prob x-1) =
        Real.exp (-c)*(q.prob x*Real.exp (g x))-p.prob x := by
      rw [sub_eq_add_neg (g x) c, Real.exp_add]
      field_simp [(hp x).ne']
    rw [he] at hm
    nlinarith
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_one, mul_one] at hs
  have hbound := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (-c)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hbound
  change p.expect g-c-kl p q ≤ Real.exp (-c)*q.expect (fun x => Real.exp (g x))-1 at hs
  linarith

omit [DecidableEq X] in

/-- The difference of the two masses on the event where `p` dominates `q` equals their total
variation distance. -/
theorem positive_event_tv (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) :
    (∑ x with q.prob x ≤ p.prob x, p.prob x) -
      (∑ x with q.prob x ≤ p.prob x, q.prob x) = tv p q := by
  have hpoint (x : X) : |p.prob x-q.prob x| =
      2*(if q.prob x ≤ p.prob x then p.prob x-q.prob x else 0) -
        (p.prob x-q.prob x) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]; ring
  have ha : (∑ x, |p.prob x-q.prob x|) =
      2*(∑ x, if q.prob x ≤ p.prob x then p.prob x-q.prob x else 0) := by
    simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum,
      p.sum_one, q.sum_one, sub_self, sub_zero]
  have he : (∑ x, if q.prob x ≤ p.prob x then p.prob x else 0) -
      (∑ x, if q.prob x ≤ p.prob x then q.prob x else 0) =
      ∑ x, if q.prob x ≤ p.prob x then p.prob x-q.prob x else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  simp only [Finset.sum_filter, he, tv, ha]
  ring

/-- Pinsker inequality for strictly positive finite distributions: twice the squared total
variation distance is at most their relative entropy. -/
theorem pinsker (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) : 2*tv p q^2 ≤ kl p q := by
  let f : X → ℝ := fun x => if q.prob x ≤ p.prob x then 1 else 0
  have hf (x : X) : f x ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [f]; split_ifs <;> constructor <;> norm_num
  have hm : p.expect f-q.expect f = tv p q := by
    simpa [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, f, mul_ite,
        Finset.sum_filter] using positive_event_tv p q
  let t := 4*tv p q
  have hg :=
      Qatlib.Concepts.SketchArith.SketchBuild.finite_hoeffding_centered_mgf X q f 0 1 t
      (by norm_num) hf
  simp only [sub_zero, one_pow, mul_one] at hg
  have hv := variational_lower p q hp hq (fun x => t*(f x-q.expect f)) (t^2/8) hg
  have he : p.expect (fun x => t*(f x-q.expect f)) = t*(p.expect f-q.expect f) := by
    change (∑ x, p.prob x*(t*(f x-q.expect f))) = _
    have hpoint (x : X) : p.prob x*(t*(f x-q.expect f)) =
        t*(p.prob x*f x)-(t*q.expect f)*p.prob x := by ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      p.sum_one, mul_one]
    change t*p.expect f-t*q.expect f = _
    ring
  rw [he, hm] at hv
  dsimp [t] at hv
  nlinarith

/-- For strictly positive finite laws, every Boolean test has error sum at least one minus the
square root of half their relative entropy. -/
theorem testing_lower (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) (f : X → Bool) :
    1-Real.sqrt (kl p q/2) ≤ errorSum p q f := by
  have hk := kl_nonneg p q hp hq
  have hs := Real.sq_sqrt (div_nonneg hk (by norm_num : (0 : ℝ) ≤ 2))
  have ht := pinsker p q hp hq
  have htv : tv p q ≤ Real.sqrt (kl p q/2) := by nlinarith [Real.sqrt_nonneg (kl p q/2)]
  linarith [errorSum_lower p q f]

/-- Every Boolean test on `n` independent observations has error sum at least one minus the
square root of `n` times half the single-observation relative entropy. -/
theorem records_testing (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (hp : ∀ x, 0 < p.prob x)
    (hq : ∀ x, 0 < q.prob x) (n : ℕ) (f : (Fin n → X) → Bool) :
    1-Real.sqrt ((n : ℝ)*kl p q/2) ≤ errorSum (records p n) (records q n) f := by
  have hp' (w : Fin n → X) : 0 < (records p n).prob w := by
    change 0 < ∏ i, p.prob (w i)
    exact Finset.prod_pos fun i _ => hp (w i)
  have hq' (w : Fin n → X) : 0 < (records q n).prob w := by
    change 0 < ∏ i, q.prob (w i)
    exact Finset.prod_pos fun i _ => hq (w i)
  simpa only [kl_records p q hp hq n] using
    testing_lower (records p n) (records q n) hp' hq' f

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinitePinsker
