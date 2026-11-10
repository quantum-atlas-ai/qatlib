/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCryptanal15.MainResults.Complexity.Core
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential

open Complexity

noncomputable def truncatedMultiEpsilon (hT Δin : ℝ) : ℝ := pow2 (2 * Δin - hT - 1)

noncomputable def singleStructureCost (hT : ℝ) : ℝ := pow2 ((hT + 1) / 3)

noncomputable def multiStructureCost (hT Δin : ℝ) : ℝ :=
  pow2 ((hT + 1) / 2 - Δin / 3)

noncomputable def q2TruncatedDistinguisherCost (hT Δin : ℝ) : ℝ :=
  max (singleStructureCost hT) (multiStructureCost hT Δin)

theorem single_structure_ambainis_cost (hT : ℝ) :
    pow2 ((hT + 1) / 2) ^ (2 / 3 : ℝ) = pow2 ((hT + 1) / 3) := by
  rw [← pow2_mul]
  congr 1
  ring

theorem multi_structure_success_epsilon (hT Δin : ℝ) :
    truncatedMultiEpsilon hT Δin = pow2 (2 * Δin - hT - 1) := rfl

theorem multi_structure_grover_iterations (hT Δin : ℝ) :
    (Real.sqrt (truncatedMultiEpsilon hT Δin))⁻¹ = pow2 ((hT + 1) / 2 - Δin) := by
  unfold truncatedMultiEpsilon
  have hexp : 2 * Δin - hT - 1 = -(hT + 1 - 2 * Δin) := by ring
  rw [hexp, inv_sqrt_pow2_neg]
  congr 1
  ring

theorem multi_structure_check_cost (Δin : ℝ) :
    pow2 Δin ^ (2 / 3 : ℝ) = pow2 (2 * Δin / 3) := by
  rw [← pow2_mul]
  congr 1
  ring

theorem multi_structure_total_cost (hT Δin : ℝ) :
    pow2 ((hT + 1) / 2 - Δin) * pow2 (2 * Δin / 3) =
      pow2 ((hT + 1) / 2 - Δin / 3) := by
  rw [← pow2_add]
  congr 1
  ring

theorem q2_truncated_distinguisher_cost (hT Δin : ℝ) :
    q2TruncatedDistinguisherCost hT Δin =
      max (pow2 ((hT + 1) / 2) ^ (2 / 3 : ℝ))
        ((Real.sqrt (truncatedMultiEpsilon hT Δin))⁻¹ * pow2 Δin ^ (2 / 3 : ℝ)) := by
  unfold q2TruncatedDistinguisherCost singleStructureCost multiStructureCost
  rw [single_structure_ambainis_cost, multi_structure_grover_iterations,
    multi_structure_check_cost, multi_structure_total_cost]

end Qatlib.Papers.QCryptanal15.MainResults.TruncatedDifferential
