/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteDistributionVariation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FinitePinsker

/-!
# Distinguishability of finite output laws

The absolute acceptance gap `testGap` compares two finite distributions using a Boolean test.
The maximal gap `advantage` equals total variation, and the test selecting points where the
first mass dominates the second attains this maximum. For background on statistical
distinguishability, see [Watrous2018].

## Main statements

* `positive_test_attains`: the positive mass-difference event attains total variation.
* `advantage_eq_tv`: optimal Boolean testing advantage equals total variation.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability
open scoped BigOperators Classical
open FiniteInformationDivergence
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The absolute difference between the probabilities that a Boolean test returns true under two
finite distributions. -/
def testGap (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → Bool) : ℝ :=
  |(∑ x with f x=true, p.prob x)-(∑ x with f x=true, q.prob x)|

/-- The maximum absolute acceptance gap over all Boolean tests on the finite outcome space. -/
def advantage (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (testGap p q)

/-- Every Boolean test has absolute acceptance gap at most the total variation distance. -/
theorem testGap_le (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → Bool) : testGap p q f ≤ tv p q :=
  FiniteDistributionVariation.event_distance p q (Finset.univ.filter fun x => f x=true)

/-- The test accepting exactly where the mass of `p` is at least the mass of `q` attains their
total variation distance. -/
theorem positive_test_attains (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) :
    testGap p q (fun x => decide (q.prob x ≤ p.prob x)) = tv p q := by
  have h := FinitePinsker.positive_event_tv p q
  have ht : 0 ≤ tv p q := div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)
  unfold testGap
  simp only [decide_eq_true_eq]
  rw [h, abs_of_nonneg ht]

/-- The optimal Boolean testing advantage between two finite distributions equals their total
variation distance. -/
theorem advantage_eq_tv (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : advantage p q = tv p q := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => testGap_le p q f
  · rw [← positive_test_attains p q]
    exact Finset.le_sup' (testGap p q) (Finset.mem_univ _)
end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability
