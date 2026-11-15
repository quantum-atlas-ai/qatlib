/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma37BiasGadgetStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeGadget

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Establishes the bias gadget result of Lemma 3.7. -/
theorem lemma37BiasGadget : Lemma37BiasGadget := by
  intro p q hp0 hp1 hq0 hq1 m
  let δ := (2 : ℝ)^(-(min p (1-p)*m))
  have hw := muWeight_cubeWeight hp0.le hp1.le m
  obtain ⟨S,hSlo,hShi⟩ := finite_weight_subset_overshoot (muWeight p m) hw.1 hw.2
    q δ hq0 hq1 (Real.rpow_nonneg (by norm_num) _) (muWeight_atom_bound hp0 hp1 m)
  refine ⟨fun z => decide (z ∈ S), ?_, ?_⟩
  · simpa [cubeExpect, Finset.sum_filter] using hSlo
  · simpa [cubeExpect, Finset.sum_filter, δ] using hShi

end Qatlib.Concepts.ProbabilityCore.DistributionAA
