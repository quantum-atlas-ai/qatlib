/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.EventProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Foundations.PureStateMath.BornBridge

section
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def bornDistribution (ψ : QState I) (hψ : Normalized ψ) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (BornProb ψ i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg ψ i)]
    have h : (∑ i, BornProb ψ i) = 1 := by simpa [MeasureProb] using measureProb_univ hψ
    rw [h, ENNReal.ofReal_one])

@[simp] theorem bornDistribution_apply (ψ : QState I) (hψ : Normalized ψ) (i : I) :
    bornDistribution ψ hψ i = ENNReal.ofReal (BornProb ψ i) := rfl

@[simp] theorem bornDistribution_ket (i : I) :
    bornDistribution (Ket i) (normalized_ket i) = PMF.pure i := by
  ext j
  by_cases h : i = j <;> simp [bornDistribution_apply, bornProb_ket, PMF.pure_apply, h, eq_comm]

theorem bornDistribution_event (ψ : QState I) (hψ : Normalized ψ) (S : Finset I) :
    (∑ i ∈ S, bornDistribution ψ hψ i) = ENNReal.ofReal (MeasureProb ψ S) := by
  simp only [bornDistribution_apply, MeasureProb]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg ψ i)).symm

end
end Qatlib.Foundations.PureStateMath.BornBridge
