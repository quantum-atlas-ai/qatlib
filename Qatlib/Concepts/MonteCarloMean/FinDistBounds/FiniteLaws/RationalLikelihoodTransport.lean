/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteRationalLikelihood
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.SampleEventVariation

/-!
# Transporting rational likelihood risk

This module transfers decoding risk from a normalized rational model to an actual finite
sampling law within total variation `eps`. For `n` observations, the support and log-likelihood
risk bounds each acquire an additive n·eps term, while the rational gate bound remains
available. Total variation as a measure of distinguishability is discussed in [Watrous2018].

## Main statements

* `support_risk`: support-based decoding risk transfers to a nearby law.
* `log_risk`: exponential log-likelihood bounds transfer with an additive sampling error.
* `support_and_gates`: transported support risk is paired with a gate bound.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.RationalLikelihoodTransport

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open FiniteRationalLikelihood FiniteInformationDivergence
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open FiniteSelection
open scoped BigOperators Classical

variable {X : Type} [Fintype X] {m n : ℕ}

/-- If the actual law is within total variation `eps` of the true rational table, its decoding
risk is at most the model support bound plus n·eps. -/
theorem support_risk (actual : FinDist X) (q : Fin (m + 1) → X → ℚ)
    (hq : ∀ c x, 0 ≤ q c x) (hsum : ∀ c, ∑ x, q c x = 1)
    (truth : Fin (m + 1)) (eps : ℝ)
    (happrox : tv actual (distribution (q truth) (hq truth) (hsum truth)) ≤ eps) :
    actual.probEvent (fun w : Fin n → X => (decode q w).candidate ≠ truth) ≤
      (∑ c with c ≠ truth,
        (∑ x with (distribution (q c) (hq c) (hsum c)).prob x ≠ 0,
          (distribution (q truth) (hq truth) (hsum truth)).prob x) ^ n) + (n : ℝ) * eps := by
  exact SampleEventVariation.risk_transfer actual (distribution (q truth) (hq truth) (hsum truth))
    n _ _ eps (FiniteRationalLikelihood.support_error_bound q hq hsum truth) happrox

/-- Under the stated positive-table log-likelihood hypotheses, total variation approximation by
`eps` transfers the exponential decoding risk bound with additive error n·eps. -/
theorem log_risk (actual : FinDist X) (q : Fin (m + 1) → X → ℚ)
    (hq : ∀ c x, 0 ≤ q c x) (hsum : ∀ c, ∑ x, q c x = 1)
    (truth : Fin (m + 1)) (a b d : Fin (m + 1) → ℝ)
    (hpos : ∀ c x, 0 < (q c x : ℝ)) (hn : 0 < n)
    (hab : ∀ c, c ≠ truth → a c < b c) (hd : ∀ c, c ≠ truth → 0 < d c)
    (hrange : ∀ c, c ≠ truth → ∀ x,
      Real.log (q c x : ℝ) - Real.log (q truth x : ℝ) ∈ Set.Icc (a c) (b c))
    (hmean : ∀ c, c ≠ truth → (distribution (q truth) (hq truth) (hsum truth)).expect
      (fun x => Real.log (q c x : ℝ) - Real.log (q truth x : ℝ)) = -d c)
    (eps : ℝ) (happrox : tv actual (distribution (q truth) (hq truth) (hsum truth)) ≤ eps) :
    actual.probEvent (fun w : Fin n → X => (decode q w).candidate ≠ truth) ≤
      (∑ c with c ≠ truth, Real.exp (-2 * (n : ℝ) * (d c) ^ 2 / (b c - a c) ^ 2)) +
        (n : ℝ) * eps := by
  exact SampleEventVariation.risk_transfer actual (distribution (q truth) (hq truth) (hsum truth))
    n _ _ eps (FiniteRationalLikelihood.log_error_bound q hq hsum truth a b d
      hpos hn hab hd hrange hmean) happrox

/-- Total variation approximation gives the support-based decoding risk plus n·eps, together
with a uniform gate bound from the rational table widths. -/
theorem support_and_gates (actual : FinDist X) (q : Fin (m + 1) → X → ℚ)
    (hq : ∀ c x, 0 ≤ q c x) (hsum : ∀ c, ∑ x, q c x = 1)
    (truth : Fin (m + 1)) (eps : ℝ)
    (happrox : tv actual (distribution (q truth) (hq truth) (hsum truth)) ≤ eps)
    (B : ℕ) (hB : ∀ c x, width (q c x) ≤ B) :
    actual.probEvent (fun w : Fin n → X => (decode q w).candidate ≠ truth) ≤
      (∑ c with c ≠ truth,
        (∑ x with (distribution (q c) (hq c) (hsum c)).prob x ≠ 0,
          (distribution (q truth) (hq truth) (hsum truth)).prob x) ^ n) + (n : ℝ) * eps ∧
    ∀ w : Fin n → X, (decode q w).gates ≤ (m + 1) *
      (2 * (n * binomialRatOpGateCap (1 + n * B)) +
        24 * (1 + n * B) ^ 2 + 20 * (1 + n * B)) :=
  ⟨support_risk actual q hq hsum truth eps happrox,
    fun w => decode_gates q w B hB⟩

end Qatlib.Concepts.MonteCarloMean.FinDistBounds.RationalLikelihoodTransport
