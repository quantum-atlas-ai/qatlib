/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean

/-!
# Payoff-value distance for estimator transport

`payoffValueL1Dist` defines the unhalved L1 distance between measurement masses obtained by
applying two matrices to a basis ket and grouping outcomes with the same rational payoff. This
is the distributional input used to transport the restricted signed estimator in Lemma 18 of
[Montanaro2015].

## Main statements

* `payoffValueL1Dist` sums absolute differences of measurement masses over the finite image of
  the payoff.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

namespace Qatlib.Concepts.EstimatorLaws.MergedEstimator

open Qatlib

/-- The unhalved L1 distance between measurement masses after grouping basis outcomes by their
rational payoff value. No unitarity assumption is imposed in this definition. -/
noncomputable def payoffValueL1Dist {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) : ℝ :=
  ∑ v ∈ Finset.image f Finset.univ,
    |∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₁ (Ket j)) i
      - ∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₂ (Ket j)) i|

end Qatlib.Concepts.EstimatorLaws.MergedEstimator
