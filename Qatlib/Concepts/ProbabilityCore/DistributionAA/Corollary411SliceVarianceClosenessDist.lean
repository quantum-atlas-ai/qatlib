/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Corollary411SliceVarianceClosenessStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductSliceMoments

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the product-slice variance and influence closeness result of Corollary 4.11. -/
theorem corollary411ProductSliceVarianceInfluenceCloseness : Corollary411ProductSliceVarianceInfluenceCloseness := by
  intro p hp0 hp1 n d f hb hd
  have h := cube_product_slice_moment_error hp0 hp1 hb hd
  have hc : 48*(d : ℝ)^2/Real.sqrt (n : ℝ) ≤ 96*(d : ℝ)^2/Real.sqrt (n : ℝ) := by
    have hn : 0 ≤ 48*(d : ℝ)^2/Real.sqrt (n : ℝ) := by positivity
    rw [show 96*(d : ℝ)^2/Real.sqrt (n : ℝ) = 2*(48*(d : ℝ)^2/Real.sqrt (n : ℝ)) by ring]
    linarith only [hn]
  exact ⟨h.1.trans hc,fun i => (h.2 i).trans hc⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
