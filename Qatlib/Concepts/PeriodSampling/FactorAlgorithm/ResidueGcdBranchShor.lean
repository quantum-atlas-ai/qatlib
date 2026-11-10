/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueAuxiliary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

theorem residueGcdBranch : ResidueGcdBranch := by
  intro N _ _
  refine ⟨residue_classical_factor_sound N, ?_, ?_, residue_coprime_card N⟩
  · intro y hy
    refine ⟨ZMod.unitOfCoprime y.val hy, ?_, ?_⟩
    · unfold residueCoprimeUnit
      rw [dif_pos hy]
    · rw [ZMod.coe_unitOfCoprime]
      simp
  · intro u
    have h := ZMod.val_coe_unit_coprime u
    unfold residueCoprimeUnit
    rw [dif_pos h]
    congr 1
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    simp
end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
