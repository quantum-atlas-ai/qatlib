/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.FourierLaw
import Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias
import Qatlib.Papers.MonteCarloInt20.QaeLaw.PayoffError

/-!
# Variance of the finite Fourier QAE estimator

Reuses the normalized phase law and its target-centered second moment to bound
the actual estimator variance by one over the phase-register size.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier
open Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff

open Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff

/-! The centered variance is no larger than the second moment around the
    physical target.  This is the finite-law variance consumer needed before
    attaching independent-shot concentration bounds. -/

/-- The actual QAE estimate has variance at most the physical one-over-M
second-moment budget. -/
theorem phaseLaw_estimate_variance_le (M : ℕ) (θ : ℝ) (hM : 0 < M) :
    (phaseLaw M θ hM).variance (fun k => estimate M k) ≤ 1/(M:ℝ) := by
  let p := phaseLaw M θ hM
  let f : Fin M → ℝ := fun k => estimate M k
  let a : ℝ := target θ
  have hnorm : ∑ k, p.prob k = 1 := p.sum_one
  have hrewrite : p.expect (fun k => (f k-a)^2) =
      p.expect (fun k => f k^2) - 2*a*p.expect f + a^2 := by
    unfold FinDist.expect
    calc
      (∑ k, p.prob k * (f k-a)^2) =
          ∑ k, p.prob k * (f k^2 - 2*a*f k + a^2) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        ring
      _ = (∑ k, p.prob k * f k^2) -
          2*a*(∑ k, p.prob k * f k) + a^2 := by
        simp only [mul_sub, mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have hmul (c : ℝ) (g : Fin M → ℝ) :
            (∑ k, p.prob k * (c * g k)) =
              c * (∑ k, p.prob k * g k) := by
          calc
            (∑ k, p.prob k * (c * g k)) =
                ∑ k, c * (p.prob k * g k) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
            _ = c * (∑ k, p.prob k * g k) := by rw [Finset.mul_sum]
        rw [hmul (2*a) f]
        have hconst : (∑ k, p.prob k * a^2) = a^2 := by
          rw [← Finset.sum_mul, hnorm, one_mul]
        rw [hconst]
  have hmin : p.variance f ≤ p.expect (fun k => (f k-a)^2) := by
    rw [p.variance_eq_expect_sq_sub, hrewrite]
    nlinarith [sq_nonneg (p.expect f-a)]
  calc
    (phaseLaw M θ hM).variance (fun k => estimate M k) = p.variance f := by
      rfl
    _ ≤ p.expect (fun k => (f k-a)^2) := hmin
    _ = ∑ k, phaseMass M θ k * (estimate M k-target θ)^2 := by
      simp [p, f, a, phaseLaw, FinDist.expect]
    _ ≤ 1/(M:ℝ) := second_moment_bound M θ hM

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
