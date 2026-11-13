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

/-!
# Molecular simulation precision and register summaries

This module collects numerical precision and register-size statements for the molecular examples
of [AspuruGuzikEtAl2005]. It combines the stored water and lithium-hydride energy comparisons
with compact encodings, a four-qubit recursive readout model, and a qubit budget of one hundred.

Additional statements record the cc-pVTZ register estimates and a conditional compact-encoding
bound when the number of configurations is at most `2^(2 * n)`.

## Main statements

* `main_result_modest_qubits_match_fci`: Combine the two compact-register budget checks with the
  stored energy comparisons.
* `reported_registers_within_budget`: Record the eight-, eleven-, and four-qubit counts.
* `compact_representation_exponential_compression`: Bound the compact encoding under a
  configuration-count hypothesis.

## References

* [Aspuru-Guzik et al., 2005][AspuruGuzikEtAl2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

/-- The fixed numerical qubit budget of one hundred. -/
def modestQubitBudget : ℕ := 100

/-- The stored cc-pVTZ water register estimate of 47 qubits. -/
def ccpVTZH2OQubits : ℕ := 47

/-- The stored cc-pVTZ lithium-hydride register estimate of 22 qubits. -/
def ccpVTZLiHQubits : ℕ := 22

/-- The compact encodings of 196 and 1210 configurations fit the stored qubit budget, and both
stored molecular energy discrepancies lie below the specified reaction-energy scale; see
[AspuruGuzikEtAl2005]. -/
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

/-- The two compact register sizes are eight and eleven, the recursive readout size is four, and
both compact registers fit the stored budget; see [AspuruGuzikEtAl2005]. -/
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

/-- The stored cc-pVTZ counts are 22 for lithium hydride and 47 for water, with the water count
between 30 and the qubit budget; see [AspuruGuzikEtAl2005]. -/
theorem ccpVTZ_extrapolation_within_budget :
    ccpVTZLiHQubits = 22 ∧ ccpVTZH2OQubits = 47 ∧
    30 ≤ ccpVTZH2OQubits ∧ ccpVTZH2OQubits ≤ modestQubitBudget := by
  unfold ccpVTZLiHQubits ccpVTZH2OQubits modestQubitBudget
  norm_num

/-- If `configs ≤ 2^(2 * n)`, then `compactQubits configs ≤ 2 * n`, and the configuration bound
equals `4^n`; see [AspuruGuzikEtAl2005]. -/
theorem compact_representation_exponential_compression (n configs : ℕ)
    (h : configs ≤ 2 ^ (2 * n)) :
    compactQubits configs ≤ 2 * n ∧ 2 ^ (2 * n) = 4 ^ n := by
  refine ⟨compactQubits_le_two_mul n configs h, ?_⟩
  rw [pow_mul]
  norm_num

/-- The recursive readout size is four, its modeled residual width after sixteen refinements is
at most one millionth, and both stored energy discrepancies are below the reaction-energy
scale. -/
theorem recursive_readout_and_energy_precision :
    recursiveReadoutQubits = 4 ∧
    residualWidth 16 ≤ 1 / 1000000 ∧
    |h2oPEAEnergy - h2oDiagonalizationEnergy| < tenthKcalPerMolInAu ∧
    |lihPEAEnergy - lihDiagonalizationEnergy| < tenthKcalPerMolInAu := by
  exact ⟨recursive_readout_reduction.1, recursive_readout_reduction.2.2,
    reported_errors_below_reaction_scale.1, reported_errors_below_reaction_scale.2⟩

end Qatlib.Papers.MolEnergySim06.MainResults
