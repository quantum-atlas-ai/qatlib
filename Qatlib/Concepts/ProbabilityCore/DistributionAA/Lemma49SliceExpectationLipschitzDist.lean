/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma49SliceExpectationLipschitzStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceContinuity

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the slice expectation Lipschitz result of Lemma 4.9. -/
theorem lemma49SliceExpectationLipschitz : Lemma49SliceExpectationLipschitz := by
  intro n d f hb hd t u ht hu
  apply (cube_slice_expectation_lipschitz hb hd t u ht hu).trans
  have hn : 0 ≤ (4*(d : ℝ)^2/(n : ℝ))*|(t : ℝ)-(u : ℝ)| := by positivity
  rw [show (8*(d : ℝ)^2/(n : ℝ))*|(t : ℝ)-(u : ℝ)| =
    2*((4*(d : ℝ)^2/(n : ℝ))*|(t : ℝ)-(u : ℝ)|) by ring]
  linarith only [hn]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
