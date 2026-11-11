/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.PayoffError

/-!
# Smooth nonlinear QAE payoff bounds

This module bounds the first-order Taylor remainder of a differentiable payoff whose derivative
is Lipschitz. Combining this quadratic remainder with the QAE bias and second moment gives
`smooth_payoff_error`, an explicit `1/M` bound for the scaled nonlinear payoff. See
[KanekoEtAl2020].

## Main statements

* `quadratic_remainder`: a quadratic Taylor-remainder estimate.
* `smooth_payoff_error`: raw-law payoff error bounded by derivative and curvature terms.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Smooth

/-- For a differentiable function with `K`-Lipschitz derivative, the absolute first-order Taylor
remainder at `a` is at most `K*(x-a)^2`. See [KanekoEtAl2020]. -/
theorem quadratic_remainder (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) (a x : ℝ) :
    |g x-g a-gp a*(x-a)| ≤ (K:ℝ)*(x-a)^2 := by
  let R : ℝ → ℝ := fun u => g u-g a-gp a*(u-a)
  have hd (u : ℝ) : HasDerivAt R (gp u-gp a) u := by
    have h := ((hg u).sub_const (g a)).sub
      (((hasDerivAt_id u).sub_const a).const_mul (gp a))
    simpa only [R,mul_one] using! h
  have hb (u : ℝ) (hu : u ∈ Set.uIcc a x) : ‖gp u-gp a‖ ≤ (K:ℝ)*|x-a| := by
    have hl := hgp.dist_le_mul u a
    rw [Real.dist_eq,Real.dist_eq] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hu) K.coe_nonneg)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Set.uIcc a x) => (hd u).hasDerivWithinAt) hb
    (convex_Icc (min a x) (max a x)) (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have he : (K:ℝ)*|x-a| *|x-a|=(K:ℝ)*(x-a)^2 := by
    rw [mul_assoc,← pow_two,sq_abs]
  simpa only [R,sub_self,mul_zero,sub_zero,Real.norm_eq_abs,he] using! h

/-- Subtracting a constant from a phase-law expectation equals the expectation of the centered
readout. -/
theorem centered_expectation (M : ℕ) (θ : ℝ) (hM : 0 < M) (h : Fin M → ℝ) (a : ℝ) :
    (∑ k,phaseMass M θ k*h k)-a=∑ k,phaseMass M θ k*(h k-a) := by
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,phaseMass_sum_one M θ hM,one_mul]

/-- A payoff with `K`-Lipschitz derivative has raw QAE error at most `(|gp (D*target
θ)|*|D|+K*D^2)/M` for positive `M`. -/
theorem smooth_payoff_error (M : ℕ) (θ D : ℝ) (hM : 0 < M)
    (g gp : ℝ → ℝ) (K : NNReal)
    (hg : ∀ x,HasDerivAt g (gp x) x) (hgp : LipschitzWith K gp) :
    |(∑ k,rawMass M θ k*g (D*estimate M k))-g (D*target θ)| ≤
      (|gp (D*target θ)| *|D|+(K:ℝ)*D^2)/(M:ℝ) := by
  rw [show (∑ k,rawMass M θ k*g (D*estimate M k))=
    ∑ k,phaseMass M θ k*g (D*estimate M k) from nonlinear_payoff_expectation M θ D hM g,
    centered_expectation M θ hM]
  let R : Fin M → ℝ := fun k => g (D*estimate M k)-g (D*target θ)-
    gp (D*target θ)*(D*estimate M k-D*target θ)
  have he : (∑ k,phaseMass M θ k*(g (D*estimate M k)-g (D*target θ)))=
    gp (D*target θ)*D*(∑ k,phaseMass M θ k*(estimate M k-target θ))+
      ∑ k,phaseMass M θ k*R k := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [R]
    ring
  rw [he]
  have hR (k : Fin M) : |R k| ≤ (K:ℝ)*D^2*(estimate M k-target θ)^2 := by
    have h := quadratic_remainder g gp K hg hgp (D*target θ) (D*estimate M k)
    convert! h using 1; (try dsimp only [R]); ring
  calc
    _ ≤ |gp (D*target θ)*D*(∑ k,phaseMass M θ k*(estimate M k-target θ))|+
      |∑ k,phaseMass M θ k*R k| := abs_add_le _ _
    _ ≤ |gp (D*target θ)| *|D| *(1/(M:ℝ))+
      ∑ k,phaseMass M θ k*((K:ℝ)*D^2*(estimate M k-target θ)^2) := by
      apply add_le_add
      · rw [abs_mul,abs_mul]
        exact mul_le_mul_of_nonneg_left (physical_bias_bound M θ hM)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul,abs_of_nonneg (show 0 ≤ phaseMass M θ k from sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hR k) (sq_nonneg _)
    _ = |gp (D*target θ)| *|D| *(1/(M:ℝ))+
      (K:ℝ)*D^2*(∑ k,phaseMass M θ k*(estimate M k-target θ)^2) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ |gp (D*target θ)| *|D| *(1/(M:ℝ))+(K:ℝ)*D^2*(1/(M:ℝ)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (second_moment_bound M θ hM)
        (mul_nonneg K.coe_nonneg (sq_nonneg D)))
    _ = _ := by ring

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Smooth
