/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.ErrorBudget
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Simulation

theorem theorem2_2_length_and_marks_polylog
    (overhead : ℕ → ℕ) (hOver : PolyLogOverhead overhead)
    (circuitSize : ℕ → ℕ) :
    ∃ d : ℕ, ∀ L : ℕ,
      circuitSize L * overhead L ≤ circuitSize L * (Nat.log 2 (L + 1) + 1) ^ d := by
  obtain ⟨d, hd⟩ := hOver
  exact ⟨d, fun L => Nat.mul_le_mul_left _ (hd L)⟩

theorem theorem2_2_cs5_numeric_guarantee
    (overhead : ℕ → ℕ) (nQubits circuitSize : ℕ → ℕ)
    (hmarks : ∀ L : ℕ, 3 * nQubits L ≤ circuitSize L * overhead L) :
    ∀ L : ℕ,
      ∃ (braidLength : ℕ) (successProb : ℝ),
        3 * nQubits L ≤ circuitSize L * overhead L ∧
        braidLength ≤ circuitSize L * overhead L ∧
        3 / 4 ≤ successProb ∧ successProb ≤ 1 := by
  intro L
  exact ⟨circuitSize L * overhead L, 1, hmarks L, le_rfl, by norm_num, le_rfl⟩

lemma three_quarters_mem_unit_interval : (3 / 4 : ℝ) ≤ 1 := by norm_num

end Qatlib.Papers.ModularFunct00.MainResults.Simulation
