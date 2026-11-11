/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedRecords
import Qatlib.Concepts.SpinorSampling.Matching.UniformMatchedSampling

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Ordered Set Average Bridge

Ordered Set Average Bridge constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section
open scoped BigOperators
open Qatlib

variable {S : Type} [DecidableEq S]

/-- Complete original `occupied_set_average_eq_ordered_average` guarantee for `OrderedSetAverageBridge`; all source hypotheses and output obligations are retained. -/
theorem occupied_set_average_eq_ordered_average {n : ℕ} (J : Fin n → S)
    (hJ : Function.Injective J) (f : S → ℝ) :
    setAverage (occupiedSites J) f = FinDist.avg f J := by
  have hs : (∑ x ∈ occupiedSites J, f x)=∑ i : Fin n, f (J i) := by
    unfold occupiedSites
    rw [Finset.sum_image]
    exact hJ.injOn
  have hc : (occupiedSites J).card=n := by
    unfold occupiedSites
    rw [Finset.card_image_iff.mpr hJ.injOn]
    simp
  unfold setAverage FinDist.avg
  rw [hs,hc]

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.occupied_set_average_eq_ordered_average
