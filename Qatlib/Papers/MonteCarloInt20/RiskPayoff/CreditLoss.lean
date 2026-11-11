/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# One-factor credit portfolio losses

`factor` combines common and idiosyncratic inputs with the one-factor credit coefficients, and
`loss` sums exposure-weighted strict default indicators. The module bounds the loss by total
exposure and by the number of obligors for normalized exposures.

For independent finite input laws with zero means and unit second moments,
`independent_factor_variance` proves unit variance of the combined factor when the loading has
absolute value at most one. See [KanekoEtAl2020].

## Main statements

* `loss_exposure_bound` and `loss_bounds`: deterministic credit-loss bounds.
* `independent_factor_variance`: variance normalization under independent finite laws.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss

/-- The strict comparison indicator, equal to one when `x < y` and zero otherwise. -/
def theta (x y : ℝ) : ℝ := if x<y then 1 else 0

/-- The one-factor combination `a*common+sqrt (1-a^2)*idio`. -/
def factor (a common idio : ℝ) : ℝ := a*common+Real.sqrt (1-a^2)*idio

/-- When `|a| ≤ 1`, the squared common and idiosyncratic factor coefficients sum to one. -/
theorem factor_coefficients (a : ℝ) (ha : |a|≤1) : a^2+(Real.sqrt (1-a^2))^2=1 := by
  obtain ⟨ha₀,ha₁⟩ := abs_le.mp ha
  have h : 0≤1-a^2 := by
    have hm := mul_nonneg (show 0≤1+a by linarith) (show 0≤1-a by linarith)
    nlinarith
  rw [Real.sq_sqrt h]
  ring

/-- The portfolio loss obtained by summing exposures times strict default indicators across `D`
obligors. -/
def loss (D : ℕ) (E a threshold : Fin D → ℝ) (common : ℝ) (idio : Fin D → ℝ) : ℝ :=
  ∑ i : Fin D,E i*theta (factor (a i) common (idio i)) (threshold i)

/-- For nonnegative exposure, an exposure-weighted default indicator lies between zero and that
exposure. -/
theorem default_term_bounds (E a common idio threshold : ℝ) (hE : 0≤E) :
    0≤E*theta (factor a common idio) threshold ∧ E*theta (factor a common idio) threshold≤E := by
  by_cases h : factor a common idio<threshold <;> simp [theta,h,hE]

/-- With nonnegative exposures, portfolio loss lies between zero and the total exposure. -/
theorem loss_exposure_bound (D : ℕ) (E a threshold : Fin D → ℝ) (common : ℝ) (idio : Fin D → ℝ)
    (hE : ∀ i,0≤E i) : 0≤loss D E a threshold common idio ∧ loss D E a threshold common idio≤∑ i,E i := by
  exact ⟨Finset.sum_nonneg (fun i _ => (default_term_bounds (E i) (a i) common (idio i) (threshold i) (hE i)).1),
    Finset.sum_le_sum (fun i _ => (default_term_bounds (E i) (a i) common (idio i) (threshold i) (hE i)).2)⟩

/-- With every exposure in `[0,1]`, the portfolio loss lies in `[0,D]`. See [KanekoEtAl2020]. -/
theorem loss_bounds (D : ℕ) (E a threshold : Fin D → ℝ) (common : ℝ) (idio : Fin D → ℝ)
    (hE : ∀ i,E i ∈ Set.Icc (0:ℝ) 1) : loss D E a threshold common idio ∈ Set.Icc (0:ℝ) D := by
  refine ⟨(loss_exposure_bound D E a threshold common idio (fun i => (hE i).1)).1,?_⟩
  apply (loss_exposure_bound D E a threshold common idio (fun i => (hE i).1)).2.trans
  calc
    (∑ i : Fin D,E i) ≤ ∑ _i : Fin D,(1:ℝ) := Finset.sum_le_sum (fun i _ => (hE i).2)
    _ = D := by simp

/-- Under the independent product law, the expectation of a product of separate coordinate
functions factors into their expectations. -/
theorem pair_expect_mul {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : FinDist X) (q : FinDist Y) (f : X → ℝ) (g : Y → ℝ) :
    (p.independentPair q).expect (fun z => f z.1*g z.2)=p.expect f*q.expect g := by
  unfold FinDist.expect
  simp only [FinDist.independentPair_prob,Fintype.sum_prod_type]
  simp_rw [show ∀ x y,p.prob x*q.prob y*(f x*g y)=(p.prob x*f x)*(q.prob y*g y) by intros; ring]
  rw [Finset.sum_mul_sum]

/-- Expectation under a finite distribution preserves addition of real-valued functions. -/
theorem expect_add {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (f g : X → ℝ) :
    p.expect (fun x => f x+g x)=p.expect f+p.expect g := by
  simp only [FinDist.expect,mul_add,Finset.sum_add_distrib]

/-- Expectation under a finite distribution commutes with multiplication by a real constant. -/
theorem expect_scale {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (c : ℝ) (f : X → ℝ) :
    p.expect (fun x => c*f x)=c*p.expect f := by
  simp only [FinDist.expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The expectation of the constant-one function under a finite distribution is one. -/
theorem expect_one {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) : p.expect (fun _ => 1)=1 := by
  simpa only [FinDist.expect,mul_one] using p.sum_one

/-- Independent zero-mean inputs with unit second moments produce a unit-variance factor when
`|a| ≤ 1`. See [KanekoEtAl2020]. -/
theorem independent_factor_variance {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (p : FinDist X) (q : FinDist Y) (common : X → ℝ) (idio : Y → ℝ)
    (hc : p.expect common=0) (hi : q.expect idio=0)
    (hc₂ : p.expect (fun x => common x^2)=1) (hi₂ : q.expect (fun y => idio y^2)=1)
    (a : ℝ) (ha : |a|≤1) :
    (p.independentPair q).variance (fun z => factor a (common z.1) (idio z.2))=1 := by
  let β := Real.sqrt (1-a^2)
  have hleft : (p.independentPair q).expect (fun z => common z.1)=0 := by
    have h := pair_expect_mul p q common (fun _ => 1)
    simpa only [mul_one,hc,zero_mul] using h
  have hright : (p.independentPair q).expect (fun z => idio z.2)=0 := by
    have h := pair_expect_mul p q (fun _ => 1) idio
    simpa only [one_mul,hi,mul_zero] using h
  have hsleft : (p.independentPair q).expect (fun z => common z.1^2)=1 := by
    have h := pair_expect_mul p q (fun x => common x^2) (fun _ => 1)
    simpa only [mul_one,hc₂,expect_one,one_mul] using h
  have hsright : (p.independentPair q).expect (fun z => idio z.2^2)=1 := by
    have h := pair_expect_mul p q (fun _ => 1) (fun y => idio y^2)
    simpa only [one_mul,hi₂,expect_one,mul_one] using h
  have hcross : (p.independentPair q).expect (fun z => common z.1*idio z.2)=0 := by
    rw [pair_expect_mul,hc,zero_mul]
  have hm : (p.independentPair q).expect (fun z => factor a (common z.1) (idio z.2))=0 := by
    change (p.independentPair q).expect (fun z => a*common z.1+β*idio z.2)=0
    rw [expect_add,expect_scale,expect_scale,hleft,hright]
    ring
  rw [FinDist.variance_eq_expect_sq_sub,hm,zero_pow (by norm_num : 2≠0),sub_zero]
  have hpoly : (fun z : X × Y => factor a (common z.1) (idio z.2)^2)=
      fun z => a^2*common z.1^2+(2*a*β)*(common z.1*idio z.2)+β^2*idio z.2^2 := by
    funext z
    change (a*common z.1+β*idio z.2)^2=_
    ring
  rw [hpoly,expect_add,expect_add,expect_scale,expect_scale,expect_scale,hsleft,hsright,hcross]
  simpa only [mul_one,mul_zero,add_zero] using factor_coefficients a ha

end Qatlib.Papers.MonteCarloInt20.RiskPayoff.CreditLoss
