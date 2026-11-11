/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.EventProbability
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Measurement bounds from injective images

Proves a finite measurement inequality: an event containing an injective image has probability
at least the image cardinality times a uniform lower bound on its point probabilities. The
result `measureProb_ge_card_image` supports the good-outcome estimates for the
discrete-logarithm analysis associated with [Shor1997].

## Main statements

* `measureProb_ge_card_image`: Sums a pointwise Born-probability lower bound over an injective
  image.

## References

* [Shor, 1997][Shor1997]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.DlogGoodProb
open scoped BigOperators

/-- If an event contains the injective image of a finite set `S` and every image point has Born
probability at least `L`, then its measurement probability is at least `(S.card : ℝ) * L`. -/
theorem measureProb_ge_card_image {I J : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq J] (ψ : QState I) (S : Finset J) (E : Finset I) (f : J → I)
    (hf : Function.Injective f) (hsub : S.image f ⊆ E) (L : ℝ)
    (hL : ∀ j ∈ S, L ≤ BornProb ψ (f j)) :
    (S.card : ℝ)*L ≤ MeasureProb ψ E := by
  calc
    (S.card : ℝ)*L = ∑ _j ∈ S, L := by simp
    _ ≤ ∑ j ∈ S, BornProb ψ (f j) := Finset.sum_le_sum hL
    _ = MeasureProb ψ (S.image f) := by
      unfold MeasureProb
      rw [Finset.sum_image]
      intro a _ b _ h
      exact hf h
    _ ≤ MeasureProb ψ E := measureProb_mono ψ hsub
end Qatlib.Concepts.PeriodSampling.DlogGoodProb
