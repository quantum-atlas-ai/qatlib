/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Bernoulli variance and sampling tails

`boolIndicator` turns Boolean outcomes into real observations. The module computes its
expectation and variance and proves Chebyshev bounds for finite independent sample averages,
including a bound proportional to the probability of a rare true outcome. See
[NielsenChuang2010] for background.

## Main statements

* `variance_boolIndicator`: The variance of the Boolean indicator is its mean times one minus
  its mean.
* `chebyshev_avg_boolIndicator`: For a positive sample count, the probability that the Boolean
  sample average differs from its mean by more than positive `ε` is at most `1 / (4 * L * ε^2)`.
* `chebyshev_avg_boolIndicator_rare`: If the true outcome has probability at most `r`, the
  probability of sample mean error greater than positive `ε` is at most `r / (L * ε^2)`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

variable {X : Type*} [Fintype X]

/-- The real indicator of a Boolean value, equal to one on `true` and zero on `false`. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Pointwise equivalent events have the same product sampling probability. -/
theorem probEvent_congr {L : ℕ} (p : FinDist X) (E F : (Fin L → X) → Prop)
    [DecidablePred E] [DecidablePred F] (h : ∀ ω, E ω ↔ F ω) :
    p.probEvent E = p.probEvent F := by
  simp only [probEvent]
  rw [Finset.filter_congr fun ω _ => h ω]

/-- The probabilities of an event and its complement sum to one. -/
theorem probEvent_compl {L : ℕ} (p : FinDist X) (E : (Fin L → X) → Prop)
    [DecidablePred E] :
    p.probEvent E + p.probEvent (fun ω => ¬E ω) = 1 := by
  classical
  simp only [probEvent, Finset.sum_filter]
  have hsplit : ∀ ω : Fin L → X,
      (if E ω then p.probOf ω else 0) + (if ¬E ω then p.probOf ω else 0)
        = p.probOf ω := by
    intro ω
    by_cases hE : E ω <;> simp [hE]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun ω _ => hsplit ω), sum_probOf]

/-- The expectation of the Boolean indicator is the probability of `true`. -/
theorem expect_boolIndicator (p : FinDist Bool) :
    p.expect boolIndicator = p.prob true := by
  simp [expect, boolIndicator]

/-- The variance of the Boolean indicator is its mean times one minus its mean. -/
theorem variance_boolIndicator (p : FinDist Bool) :
    p.variance boolIndicator = p.expect boolIndicator * (1 - p.expect boolIndicator) := by
  have hsum : ∀ g : Bool → ℝ, ∑ b : Bool, g b = g false + g true := fun g => by
    simp
    ring
  have hq : p.expect boolIndicator = p.prob true := expect_boolIndicator p
  have hsplit : p.prob false + p.prob true = 1 := by
    rw [← hsum]
    exact p.sum_one
  have hpf : p.prob false = 1 - p.prob true := by linarith
  show ∑ b : Bool, p.prob b * (boolIndicator b - p.expect boolIndicator) ^ 2
      = p.expect boolIndicator * (1 - p.expect boolIndicator)
  rw [hsum, hq]
  simp only [show boolIndicator false = 0 from rfl, show boolIndicator true = 1 from rfl]
  rw [hpf]
  ring

/-- The variance of the Boolean indicator is at most `1 / 4`. -/
theorem variance_boolIndicator_le (p : FinDist Bool) :
    p.variance boolIndicator ≤ 1 / 4 := by
  rw [variance_boolIndicator]
  have hq : p.expect boolIndicator = p.prob true := expect_boolIndicator p
  have hsum : ∀ g : Bool → ℝ, ∑ b : Bool, g b = g false + g true := fun g => by
    simp
    ring
  have hsplit : p.prob false + p.prob true = 1 := by
    rw [← hsum]
    exact p.sum_one
  have hpt : 0 ≤ p.prob true := p.nonneg true
  have hpf : 0 ≤ p.prob false := p.nonneg false
  rw [hq]
  nlinarith [sq_nonneg (2 * p.prob true - 1), hsplit, hpt, hpf]

/-- For a positive sample count, the probability that the Boolean sample average differs from
its mean by more than positive `ε` is at most `1 / (4 * L * ε^2)`. -/
theorem chebyshev_avg_boolIndicator {L : ℕ} (p : FinDist Bool) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) :
    p.probEvent (fun ω : Fin L → Bool =>
        ε < |avg boolIndicator ω - p.expect boolIndicator|) ≤ 1 / (4 * L * ε ^ 2) := by
  have hcheb := chebyshev_avg p boolIndicator hL ε hε
  have hvar := variance_boolIndicator_le p
  have hnn : 0 ≤ L * ε ^ 2 := by positivity
  calc p.probEvent (fun ω : Fin L → Bool =>
          ε < |avg boolIndicator ω - p.expect boolIndicator|)
      ≤ p.variance boolIndicator / (L * ε ^ 2) := hcheb
    _ ≤ (1 / 4) / (L * ε ^ 2) := by
        rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < L * ε ^ 2)]
        exact hvar
    _ = 1 / (4 * L * ε ^ 2) := by ring

/-- The variance of the Boolean indicator is at most the probability of `true`. -/
theorem variance_boolIndicator_le_true (p : FinDist Bool) :
    p.variance boolIndicator ≤ p.prob true := by
  rw [variance_boolIndicator, expect_boolIndicator]
  nlinarith [sq_nonneg (p.prob true)]

/-- If the true outcome has probability at most `r`, the probability of sample mean error
greater than positive `ε` is at most `r / (L * ε^2)`. -/
theorem chebyshev_avg_boolIndicator_rare {L : ℕ} (p : FinDist Bool) (hL : 0 < L)
    (ε r : ℝ) (hε : 0 < ε) (hr : p.prob true ≤ r) :
    p.probEvent (fun ω : Fin L → Bool =>
      ε < |avg boolIndicator ω - p.prob true|) ≤ r / (L * ε ^ 2) := by
  have hc := p.chebyshev_avg boolIndicator hL ε hε
  rw [expect_boolIndicator] at hc
  exact hc.trans (div_le_div_of_nonneg_right
    ((variance_boolIndicator_le_true p).trans hr) (by positivity))

end Qatlib.Concepts.AmplitudeCore.InvFreeSampling
