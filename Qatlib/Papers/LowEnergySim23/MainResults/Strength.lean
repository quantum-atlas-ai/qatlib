/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowEnergySim23.MainResults.Framework.LowEnergyLeakage

@[expose] public section

/-!
# Strength of the noncommuting interactions

In Lemma 5 of arXiv:2312.08867v3, the scalar `R_A` is the total strength
over those interaction terms that fail to commute with the observable.
The finite sum supplies the scalar to the pinned commuting-observable bound.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator Classical
open Qatlib.Papers.LowEnergySim23.MainResults.Framework

namespace Qatlib.Papers.LowEnergySim23.MainResults

/-- The total norm of the terms whose commutator with the observable is nonzero. -/
def nonCommutingStrength {D L : ℕ} (terms : Fin L → Op D) (A : Op D) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => ¬Commute (terms j) A), ‖terms j‖

/-- The noncommuting interaction strength is nonnegative for every observable. -/
theorem nonCommutingStrength_nonneg {D L : ℕ} (terms : Fin L → Op D) (A : Op D) :
    0 ≤ nonCommutingStrength terms A :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Termwise commutation makes the noncommuting interaction strength zero. -/
theorem nonCommutingStrength_eq_zero {D L : ℕ} (terms : Fin L → Op D) (A : Op D)
    (h : ∀ j, Commute (terms j) A) : nonCommutingStrength terms A = 0 := by
  unfold nonCommutingStrength
  simp [h]

/-- Use the actual noncommuting interaction sum as the growth parameter in the
pinned case where the total Hamiltonian commutes with the observable. -/
theorem imaginary_time_growth_of_terms {D L : ℕ} (M : TwoLocalHamiltonian D)
    (terms : Fin L → Op D) (A : Op D) (hsum : (∑ j, terms j) = M.H)
    (h : Commute (∑ j, terms j) A)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1 / (2 * M.g)) :
    ‖imaginaryConjugate s M.H A‖ ≤
      ‖A‖ * Real.rpow (1 - 2 * M.g * s) (-(nonCommutingStrength terms A / (2 * M.g))) :=
  imaginary_time_growth_bound M A (nonCommutingStrength terms A)
    (nonCommutingStrength_nonneg terms A) (hsum ▸ h) hs0 hs1

end Qatlib.Papers.LowEnergySim23.MainResults
