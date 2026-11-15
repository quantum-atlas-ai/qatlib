/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Theorem43DistAAEquivalenceStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Corollary48BiasedProductAAEquivDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition412ProductSliceTransferDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeAAWitness

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the distributional AA equivalence of Theorem 4.3. -/
theorem theorem43DistributionalAAEquivalence : Theorem43DistributionalAAEquivalence := by
  intro p q hp0 hp1 hq0 hq1
  have hμ := corollary48BiasedProductAAEquivalence p q hp0 hp1 hq0 hq1
  constructor
  · intro h
    exact cube_aa_holds_from_slice_transfer (muFamily q) (nuFamily q)
      (nuWeight_cubeWeight hq0 hq1)
      (fun S hS => (proposition412ProductSliceTransfer q hq0 hq1 S hS).1) (hμ.1 h)
  · intro h
    apply hμ.2
    exact cube_aa_holds_from_slice_transfer (nuFamily q) (muFamily q)
      (muWeight_cubeWeight hq0.le hq1.le)
      (fun S hS => (proposition412ProductSliceTransfer q hq0 hq1 S hS).2) h

end Qatlib.Concepts.ProbabilityCore.DistributionAA
