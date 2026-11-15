/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma46BiasContinuityStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeBiasContinuity

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the bias continuity result of Lemma 4.6. -/
theorem lemma46BiasContinuity : Lemma46BiasContinuity := by
  intro n d f hb hd q r hq0 hq1 hr0 hr1
  refine ⟨(cube_mu_variance_bias_lipschitz hb hd ⟨hq0,hq1⟩ ⟨hr0,hr1⟩).trans ?_, ?_⟩
  · nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (abs_nonneg (q-r))]
  · intro i
    exact cube_mu_influence_bias_lipschitz hb hd i ⟨hq0,hq1⟩ ⟨hr0,hr1⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
