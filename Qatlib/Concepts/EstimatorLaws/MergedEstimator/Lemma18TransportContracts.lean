/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

namespace Qatlib.Concepts.EstimatorLaws.MergedEstimator

open Qatlib

noncomputable def payoffValueL1Dist {I : Type} [Fintype I] [DecidableEq I]
    (A₁ A₂ : Matrix I I ℂ) (j : I) (f : I → ℚ) : ℝ :=
  ∑ v ∈ Finset.image f Finset.univ,
    |∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₁ (Ket j)) i
      - ∑ i ∈ Finset.univ.filter (fun i => f i = v), BornProb (ApplyGate A₂ (Ket j)) i|

end Qatlib.Concepts.EstimatorLaws.MergedEstimator
