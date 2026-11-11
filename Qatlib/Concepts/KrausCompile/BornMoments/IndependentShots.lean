/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesDefs

/-!
# Independent measurement records and sample moments

`iidLaw` and `iidPMF` model a fixed number of independent outcomes from a finite distribution.
For a positive sample count, the empirical average has the original mean and variance divided by
the sample count. The constructions relate to finite Kraus implementations in [CaiEtAl2026].

## Main statements

* `iidPMF_mass`: the product probability of a sample record.
* `iid_average_mean`: unbiasedness of the sample average.
* `iid_average_variance`: variance reduction by the sample count.

## References

* [Cai et al., 2026][CaiEtAl2026]
* [Kraus, 1983][Kraus1983]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.KrausCompile.BornMoments
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open scoped BigOperators

/-- The finite distribution of `M` independent samples from `p`, assigning each record the
product of its entry probabilities. -/
def iidLaw {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) : FinDist (Fin M → X) where
  prob := p.probOf
  nonneg ω := Finset.prod_nonneg (fun i _ => p.nonneg (ω i))
  sum_one := p.sum_probOf M

/-- The probability mass function associated with the finite independent-sample distribution
`iidLaw p M`. -/
def iidPMF {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) : PMF (Fin M → X) :=
  toPMF (iidLaw p M)

/-- The real mass of an independent sample record is the product of the probabilities of its
entries. -/
theorem iidPMF_mass {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X) (M : ℕ) (ω : Fin M → X) :
    (iidPMF p M ω).toReal = ∏ i, p.prob (ω i) := by
  exact ENNReal.toReal_ofReal ((iidLaw p M).nonneg ω)

/-- For positive `M`, the mean of the average of `M` independent evaluations of `f` equals
`p.expect f`. -/
theorem iid_average_mean {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (M : ℕ) (f : X → ℝ) (hM : 0 < M) :
    (iidLaw p M).expect (FinDist.avg f) = p.expect f := by
  exact p.expect_avg f hM

/-- For positive `M`, the variance of the average of `M` independent evaluations of `f` is
`p.variance f / M`. -/
theorem iid_average_variance {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (M : ℕ) (f : X → ℝ) (hM : 0 < M) :
    (iidLaw p M).variance (FinDist.avg f) = p.variance f / M := by
  change (∑ ω, p.probOf ω *
    (FinDist.avg f ω - (iidLaw p M).expect (FinDist.avg f)) ^ 2) = _
  rw [iid_average_mean p M f hM]
  exact p.expect_avg_sub_sq f hM

end Qatlib.Concepts.KrausCompile.BornMoments
