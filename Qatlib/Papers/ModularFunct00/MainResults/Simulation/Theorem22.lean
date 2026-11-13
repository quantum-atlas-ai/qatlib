/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ModularFunct00.MainResults.Setup
import Qatlib.Papers.ModularFunct00.MainResults.Approximation.ErrorBudget

/-!
# Numerical simulation budgets for Theorem 2.2

This module proves numerical consequences of an assumed `PolyLogOverhead` bound in the
simulation setting of [FreedmanLarsenWang2000]. Multiplying by circuit size preserves the
supplied logarithmic-power bound.

Given a bound on the number of marked points, `theorem2_2_cs5_numeric_guarantee` supplies
numerical braid-length and success-probability witnesses satisfying the stated inequalities.

## Main statements

* `theorem2_2_length_and_marks_polylog`: Multiply a polylogarithmic overhead bound by circuit
  size.
* `theorem2_2_cs5_numeric_guarantee`: Construct witnesses for the length, marked-point, and
  success inequalities.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Simulation

/-- An assumed polylogarithmic overhead gives a uniform logarithmic-power upper bound after
multiplication by circuit size; see [FreedmanLarsenWang2000]. -/
theorem theorem2_2_length_and_marks_polylog
    (overhead : ℕ → ℕ) (hOver : PolyLogOverhead overhead)
    (circuitSize : ℕ → ℕ) :
    ∃ d : ℕ, ∀ L : ℕ,
      circuitSize L * overhead L ≤ circuitSize L * (Nat.log 2 (L + 1) + 1) ^ d := by
  obtain ⟨d, hd⟩ := hOver
  exact ⟨d, fun L => Nat.mul_le_mul_left _ (hd L)⟩

/-- Given the marked-point inequality, there exist a natural braid-length witness within the
supplied budget and a real success witness between three quarters and one; see
[FreedmanLarsenWang2000]. -/
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

/-- The real number three quarters is at most one. -/
lemma three_quarters_mem_unit_interval : (3 / 4 : ℝ) ≤ 1 := by norm_num

end Qatlib.Papers.ModularFunct00.MainResults.Simulation
