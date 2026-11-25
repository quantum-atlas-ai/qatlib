/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

@[expose] public section

/-!
# One-shot variance-to-success wrapper

The shared finite-law library proves Chebyshev's inequality for sample averages of length `L`
(`Qatlib.Concepts.MonteCarloMean.FinDistBounds.chebyshev_avg`) and the one-shot Chebyshev tail
bound `Qatlib.Concepts.ProbabilityCore.Concentration.chebyshev`, which bounds the mass of the
deviation event by `variance / ε²`. Paper-layer estimators, however, are usually stated as a
*variance hypothesis*: the variance of the statistic is at most `ε² / 3`, and the conclusion is a
`2 / 3` success guarantee for the single-shot event `|f x - μ| ≤ ε`.

This module records that passage once, in the single canonical home for the one-shot wrapper:

* `eventMass_compl`: the mass of an event and of its complement add up to one.
* `eventMass_good_ge_two_thirds_of_variance`: a variance bound `ε² / 3` gives mass at least
  `2 / 3` to the good event `|f x - μ| ≤ ε`.
* `probEvent_single_abs_le_of_variance`: the same statement in the pointwise `if`-sum form used
  by the paper-layer success probabilities.

The statement is the finite, one-shot specialization only: no independence, no repeated
sampling and no asymptotic amplification is included.

Paper: [arXiv:2606.13638v2](https://arxiv.org/abs/2606.13638v2), §4.1.2 p. 13, lines 861-866,
where `Var[f] ≤ ε² / 3` and Chebyshev give the `2 / 3` guarantee of Problem 2.1, eq. (1).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- The masses of a decidable event and of its complement add up to one. -/
theorem eventMass_compl (p : FinDist X) (E : X → Prop) [DecidablePred E] :
    eventMass p E + eventMass p (fun x => ¬ E x) = 1 := by
  classical
  rw [eventMass, eventMass]
  rw [Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X)]
  exact p.sum_one

/-- One-shot Chebyshev in success form: if `f` has mean `μ` and variance at most `ε² / 3`, then
the good event `|f x - μ| ≤ ε` carries probability at least `2 / 3`. -/
theorem eventMass_good_ge_two_thirds_of_variance (p : FinDist X) (f : X → ℝ) (μ ε : ℝ)
    (hε : 0 < ε) (hmean : p.expect f = μ) (hvar : p.variance f ≤ ε ^ 2 / 3) :
    (2 / 3 : ℝ) ≤ eventMass p (fun x => |f x - μ| ≤ ε) := by
  classical
  have hbad : eventMass p (fun x => ¬ |f x - μ| ≤ ε) ≤ 1 / 3 := by
    have hcheb : eventMass p (fun x => ε < |f x - μ|) ≤ p.variance f / ε ^ 2 := by
      have h := chebyshev_strict p f ε hε
      rwa [hmean] at h
    have hsame : eventMass p (fun x => ¬ |f x - μ| ≤ ε) = eventMass p (fun x => ε < |f x - μ|) := by
      simp only [eventMass, not_le]
    rw [hsame]
    have hdiv : p.variance f / ε ^ 2 ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
      linarith
    exact hcheb.trans hdiv
  have hsum := eventMass_compl p (fun x => |f x - μ| ≤ ε)
  linarith [hbad, hsum]

/-- The paper-layer form of the one-shot Chebyshev guarantee: the pointwise success mass of
`|f x - μ| ≤ ε` is at least `2 / 3` once the variance of `f` is at most `ε² / 3`. -/
theorem probEvent_single_abs_le_of_variance (p : FinDist X) (f : X → ℝ) (μ ε : ℝ)
    (hε : 0 < ε) (hmean : p.expect f = μ) (hvar : p.variance f ≤ ε ^ 2 / 3) :
    (2 / 3 : ℝ) ≤ ∑ x, if |f x - μ| ≤ ε then p.prob x else 0 := by
  classical
  have h := eventMass_good_ge_two_thirds_of_variance p f μ ε hε hmean hvar
  rw [eventMass] at h
  rw [← Finset.sum_filter]
  exact h

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
