/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Born probabilities as probability mass functions

The construction `bornDistribution` packages the computational-basis Born probabilities of a
normalized finite state as a PMF. It identifies basis-state distributions with point masses and
relates finite-event sums to `MeasureProb`, connecting the vector and probabilistic formulations
of measurement [NielsenChuang2010].

## Main statements

* `bornDistribution_apply`: The PMF mass is the extended nonnegative Born probability.
* `bornDistribution_ket`: A basis ket produces a point mass.
* `bornDistribution_event`: Finite-event mass agrees with the existing measurement probability.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.PureStateMath.BornBridge

section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The computational-basis measurement PMF of a normalized finite quantum state, with masses
given by its Born probabilities. -/
noncomputable def bornDistribution (ψ : QState I) (hψ : Normalized ψ) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (BornProb ψ i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg ψ i)]
    have h : (∑ i, BornProb ψ i) = 1 := by simpa [MeasureProb] using measureProb_univ hψ
    rw [h, ENNReal.ofReal_one])

/-- The mass of `bornDistribution ψ hψ` at `i` is `ENNReal.ofReal (BornProb ψ i)`. -/
@[simp] theorem bornDistribution_apply (ψ : QState I) (hψ : Normalized ψ) (i : I) :
    bornDistribution ψ hψ i = ENNReal.ofReal (BornProb ψ i) := rfl

/-- The Born distribution of the basis ket at `i` is the point mass `PMF.pure i`. -/
@[simp] theorem bornDistribution_ket (i : I) :
    bornDistribution (Ket i) (normalized_ket i) = PMF.pure i := by
  ext j
  by_cases h : i = j <;> simp [bornDistribution_apply, bornProb_ket, PMF.pure_apply, h, eq_comm]

/-- The sum of Born-distribution masses over a finite event equals its `MeasureProb` converted
to `ℝ≥0∞`. -/
theorem bornDistribution_event (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) :
    (∑ i ∈ S, bornDistribution ψ hψ i) = ENNReal.ofReal (MeasureProb ψ S) := by
  simp only [bornDistribution_apply, MeasureProb]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg ψ i)).symm

end
end Qatlib.Foundations.PureStateMath.BornBridge
