/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueGcdBranchStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.ResidueAuxiliary

/-!
# Correctness of the residue gcd branch

Proves `residueGcdBranch`, combining factor soundness with the correspondence between coprime
residues and units. These facts justify the classical-versus-unit split in residue-based
factoring attempts associated with [Shor1997].

## Main statements

* `residueGcdBranch`: Establishes gcd-factor soundness and the coprime-residue/unit
  correspondence.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.RiskEstimation.PopulationGap
set_option autoImplicit false
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

/-- Establishes classical residue factor soundness, successful conversion of coprime residues to
their units, the unit round trip, and the equality of coprime-residue and unit counts in the
framework of [Shor1997]. -/
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
