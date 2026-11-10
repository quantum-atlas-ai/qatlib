/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FiniteDistributionVariation
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.FinitePinsker
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability
open scoped BigOperators Classical
open FiniteInformationDivergence
noncomputable section
variable {X : Type} [Fintype X] [DecidableEq X]

def testGap (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → Bool) : ℝ :=
  |(∑ x with f x=true, p.prob x)-(∑ x with f x=true, q.prob x)|

def advantage (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (testGap p q)

theorem testGap_le (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) (f : X → Bool) : testGap p q f ≤ tv p q :=
  FiniteDistributionVariation.event_distance p q (Finset.univ.filter fun x => f x=true)

theorem positive_test_attains (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) :
    testGap p q (fun x => decide (q.prob x ≤ p.prob x)) = tv p q := by
  have h := FinitePinsker.positive_event_tv p q
  have ht : 0 ≤ tv p q := div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)
  unfold testGap
  simp only [decide_eq_true_eq]
  rw [h, abs_of_nonneg ht]

theorem advantage_eq_tv (p q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist X) : advantage p q = tv p q := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun f _ => testGap_le p q f
  · rw [← positive_test_attains p q]
    exact Finset.le_sup' (testGap p q) (Finset.mem_univ _)
end
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteOutputDistinguishability
