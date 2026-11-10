/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MolEnergySim06.MainResults.ResourceScaling
import Qatlib.Papers.MolEnergySim06.MainResults.RecursivePhaseEstimation
import Qatlib.Papers.MolEnergySim06.MainResults.ChemicalPrecision
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

def modestQubitBudget : ℕ := 100

def ccpVTZH2OQubits : ℕ := 47

def ccpVTZLiHQubits : ℕ := 22

theorem main_result_modest_qubits_match_fci :
    compactQubits 196 ≤ modestQubitBudget ∧
    compactQubits 1210 ≤ modestQubitBudget ∧
    |h2oPEAEnergy - h2oDiagonalizationEnergy| < tenthKcalPerMolInAu ∧
    |lihPEAEnergy - lihDiagonalizationEnergy| < tenthKcalPerMolInAu := by
  refine ⟨?_, ?_, reported_errors_below_reaction_scale.1,
    reported_errors_below_reaction_scale.2⟩
  · rw [compactQubits_196]
    unfold modestQubitBudget
    norm_num
  · rw [compactQubits_1210]
    unfold modestQubitBudget
    norm_num

theorem reported_registers_within_budget :
    compactQubits 196 = 8 ∧ compactQubits 1210 = 11 ∧
    recursiveReadoutQubits = 4 ∧
    compactQubits 196 ≤ modestQubitBudget ∧
    compactQubits 1210 ≤ modestQubitBudget := by
  refine ⟨compactQubits_196, compactQubits_1210, rfl, ?_, ?_⟩
  · rw [compactQubits_196]
    unfold modestQubitBudget
    norm_num
  · rw [compactQubits_1210]
    unfold modestQubitBudget
    norm_num

theorem ccpVTZ_extrapolation_within_budget :
    ccpVTZLiHQubits = 22 ∧ ccpVTZH2OQubits = 47 ∧
    30 ≤ ccpVTZH2OQubits ∧ ccpVTZH2OQubits ≤ modestQubitBudget := by
  unfold ccpVTZLiHQubits ccpVTZH2OQubits modestQubitBudget
  norm_num

theorem compact_representation_exponential_compression (n configs : ℕ)
    (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n ∧ 2 ^ (2 * n) = 4 ^ n := by
  refine ⟨compactQubits_le_two_mul n configs h, ?_⟩
  rw [pow_mul]
  norm_num

theorem recursive_readout_and_energy_precision :
    recursiveReadoutQubits = 4 ∧
    residualWidth 16 ≤ 1 / 1000000 ∧
    |h2oPEAEnergy - h2oDiagonalizationEnergy| < tenthKcalPerMolInAu ∧
    |lihPEAEnergy - lihDiagonalizationEnergy| < tenthKcalPerMolInAu := by
  exact ⟨recursive_readout_reduction.1, recursive_readout_reduction.2.2,
    reported_errors_below_reaction_scale.1, reported_errors_below_reaction_scale.2⟩

end Qatlib.Papers.MolEnergySim06.MainResults
