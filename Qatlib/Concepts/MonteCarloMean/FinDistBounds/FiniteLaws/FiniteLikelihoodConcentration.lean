/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteLikelihood
import Qatlib.Concepts.SketchArith.SketchBuild.FiniteBoundedDifferences

/-!
# Concentration for finite likelihood comparisons

This module bounds upper deviations of bounded sample averages and applies the bound to log
likelihood ratios. `log_likelihood_bound` gives an exponential comparison error bound from a
positive mean gap and a bounded log ratio, while `repeated_success` computes the probability of
at least one success exactly. The finite sampling context is that of Monte Carlo estimation
[Montanaro2015].

## Main statements

* `average_upper`: For `n > 0`, `u > 0`, and `f` valued in `[a, b]` with `a < b`, the upper
  sample mean tail is at most `exp (-2 * n * u ^ 2 / (b - a) ^ 2)`.
* `log_likelihood_bound`: For strictly positive laws, a log likelihood ratio in `[a, b]` with
  mean `-d < 0` bounds the probability that `q` likelihood exceeds or equals `p` likelihood by
  `exp (-2 * n * d ^ 2 / (b - a) ^ 2)` for `n > 0`.
* `repeated_success`: The probability that `A` occurs in at least one of `n` independent samples
  is one minus the `n`th power of its failure probability.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLikelihoodConcentration
open scoped Classical BigOperators
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in

/-- Inclusion of decidable sample record events implies monotonicity of their probabilities. -/
private theorem event_mono (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) {n : ℕ}
    (E F : (Fin n → X) → Prop) [DecidablePred E] [DecidablePred F]
    (h : ∀ w, E w → F w) : p.probEvent E ≤ p.probEvent F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h w (Finset.mem_filter.mp hw).2⟩
  · intro w _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg _

/-- For `n > 0`, `u > 0`, and `f` valued in `[a, b]` with `a < b`, the upper sample mean tail is
at most `exp (-2 * n * u ^ 2 / (b - a) ^ 2)`. -/
theorem average_upper (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → ℝ) (n : ℕ)
    (a b u : ℝ) (hn : 0 < n) (hab : a < b) (hu : 0 < u)
    (hf : ∀ x, f x ∈ Set.Icc a b) :
    p.probEvent (fun w : Fin n → X => p.expect f + u ≤ Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f w) ≤
      Real.exp (-2 * (n : ℝ) * u ^ 2 / (b-a) ^ 2) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : (∑ i : Fin n, ((b-a)/(n : ℝ))^2) = (b-a)^2/(n : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hd : ∀ i (w t : Fin n → X), (∀ j, j ≠ i → w j = t j) →
      |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f w-Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f t| ≤ (b-a)/(n : ℝ) := by
    intro i w t h
    rw [Qatlib.Concepts.SketchArith.SketchBuild.finite_avg_coordinate_difference n f w t i h,
        abs_div, abs_of_pos hnR]
    apply div_le_div_of_nonneg_right _ hnR.le
    apply abs_le.mpr
    constructor <;> linarith [(hf (w i)).1, (hf (w i)).2, (hf (t i)).1, (hf (t i)).2]
  have ht := (Qatlib.Concepts.SketchArith.SketchBuild.finite_product_bounded_differences_tail X n (fun _ => p)
    (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f) (fun _ => (b-a)/(n : ℝ)) u
    (fun _ => by positivity) (by rw [hs]; positivity) hu hd).1
  have hm : (Qatlib.Concepts.MonteCarloMean.FinDistBounds.independentSampleLaw (fun _ : Fin n => p)).expect (Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg f) =
      p.expect f := p.expect_avg f hn
  rw [hm, hs] at ht
  have he : -2*u^2/((b-a)^2/(n : ℝ)) = -2*(n : ℝ)*u^2/(b-a)^2 := by
    field_simp
  rw [he] at ht
  exact ht

/-- For strictly positive laws, a log likelihood ratio in `[a, b]` with mean `-d < 0` bounds the
probability that `q` likelihood exceeds or equals `p` likelihood by `exp (-2 * n * d ^ 2 /
(b - a) ^ 2)` for `n > 0`. -/
theorem log_likelihood_bound (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (a b d : ℝ)
    (hp : ∀ x, 0 < p.prob x) (hq : ∀ x, 0 < q.prob x)
    (hn : 0 < n) (hab : a < b) (hd : 0 < d)
    (hrange : ∀ x, Real.log (q.prob x)-Real.log (p.prob x) ∈ Set.Icc a b)
    (hmean : p.expect (fun x => Real.log (q.prob x)-Real.log (p.prob x)) = -d) :
    p.probEvent (fun w : Fin n → X => p.probOf w ≤ q.probOf w) ≤
      Real.exp (-2*(n : ℝ)*d^2/(b-a)^2) := by
  let f := fun x => Real.log (q.prob x)-Real.log (p.prob x)
  have ht := average_upper p f n a b d hn hab hd hrange
  apply le_trans (event_mono p _ _ ?_) ht
  intro w hw
  have hpw : 0 < p.probOf w := Finset.prod_pos fun i _ => hp _
  have hlog := Real.log_le_log hpw hw
  have hpl : Real.log (p.probOf w) = ∑ i, Real.log (p.prob (w i)) :=
    Real.log_prod (fun i _ => (hp _).ne')
  have hql : Real.log (q.probOf w) = ∑ i, Real.log (q.prob (w i)) :=
    Real.log_prod (fun i _ => (hq _).ne')
  rw [hpl, hql] at hlog
  have hsum : 0 ≤ ∑ i, f (w i) := by
    dsimp [f]
    rw [Finset.sum_sub_distrib]
    linarith
  rw [show p.expect f = -d from hmean]
  simp only [neg_add_cancel]
  exact div_nonneg hsum (Nat.cast_nonneg n)

/-- The probability that `A` occurs in at least one of `n` independent samples is one minus the
`n`th power of its failure probability. -/
theorem repeated_success (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (n : ℕ) (A : X → Prop) [DecidablePred A] :
    p.probEvent (fun w : Fin n → X => ∃ i, A (w i)) =
      1 - (1 - ∑ x with A x, p.prob x)^n := by
  have hc := FiniteLikelihood.all_samples_mass p n (fun x => ¬ A x)
  have hm : (∑ x with ¬ A x, p.prob x) = 1-∑ x with A x, p.prob x := by
    have hs := p.sum_one
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ A p.prob] at hs
    linarith
  rw [hm] at hc
  have htotal : p.probEvent (fun w : Fin n → X => ∃ i, A (w i)) +
      p.probEvent (fun w : Fin n → X => ∀ i, ¬ A (w i)) = 1 := by
    rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ w : Fin n → X, p.probOf w := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : ∃ i, A (w i)
        · obtain ⟨i, hi⟩ := h
          simp [show ∃ i, A (w i) from ⟨i, hi⟩, show ¬ (∀ j, ¬ A (w j)) from fun hh => hh i hi]
        · have hall : ∀ i, ¬ A (w i) := fun i hi => h ⟨i, hi⟩
          simp [hall]
      _ = 1 := p.sum_probOf n
  linarith

end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLikelihoodConcentration
