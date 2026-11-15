/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma410SliceExpectationClosenessStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceCloseness

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the product-slice expectation closeness result of Lemma 4.10. -/
theorem lemma410ProductSliceExpectationCloseness : Lemma410ProductSliceExpectationCloseness := by
  intro p hp0 hp1 n d f hb hd
  apply (cube_product_slice_expectation_error hp0 hp1 hb hd).trans
  have hn : 0 ≤ 8*(d : ℝ)^2/Real.sqrt (n : ℝ) := by positivity
  rw [show 16*(d : ℝ)^2/Real.sqrt (n : ℝ) = 2*(8*(d : ℝ)^2/Real.sqrt (n : ℝ)) by ring]
  linarith only [hn]

end Qatlib.Concepts.ProbabilityCore.DistributionAA
