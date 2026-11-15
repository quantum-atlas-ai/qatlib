/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Corollary48BiasedProductAAEquivStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition47ProductBiasTransferDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeBiasEquivalence

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the biased product AA equivalence of Corollary 4.8. -/
theorem corollary48BiasedProductAAEquivalence : Corollary48BiasedProductAAEquivalence := by
  intro p q hp0 hp1 hq0 hq1
  let a := min (min p (1-p)) (min q (1-q))
  have ha : 0 < a := lt_min (lt_min hp0 (sub_pos.2 hp1)) (lt_min hq0 (sub_pos.2 hq1))
  constructor
  · exact cube_aa_holds_from_bias_transfer (muFamily p) (muFamily q)
      (muWeight_cubeWeight hq0.le hq1.le) a ha
      (proposition47ProductBiasTransfer p q hp0 hp1 hq0 hq1)
  · apply cube_aa_holds_from_bias_transfer (muFamily q) (muFamily p)
      (muWeight_cubeWeight hp0.le hp1.le) a ha
    intro S hS D hD
    have h := proposition47ProductBiasTransfer q p hq0 hq1 hp0 hp1 S hS D hD
    simpa only [min_comm] using h

end Qatlib.Concepts.ProbabilityCore.DistributionAA
