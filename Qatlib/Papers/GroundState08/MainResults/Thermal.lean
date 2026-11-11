/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Gibbs weights and level probabilities

This module defines Gibbs weights, a degeneracy-weighted partition function, and energy-level
probabilities for the thermal-state discussion of [PoulinWocjan2009]. Positive degeneracies on a
nonempty set of levels yield a normalized distribution whose probability per state is the Gibbs
weight divided by the partition function.

## Main statements

* `thermal_state_preparation`: normalization and the per-state Gibbs formula.
* `temperature_bound`: an inverse-temperature bound from a temperature lower bound.

## References

* [Poulin and Wocjan, 2009][PoulinWocjan2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GroundState08.MainResults.Thermal

/-- The Gibbs weight `exp (-β * E)` at inverse temperature `β` and energy `E`. -/
def gibbsWeight (β E : ℝ) : ℝ := Real.exp (-β * E)

/-- The sum of the Gibbs weights of the energy levels, each multiplied by its degeneracy. -/
def partitionFunction {m : ℕ} (E : Fin m → ℝ) (D : Fin m → ℕ) (β : ℝ) : ℝ :=
  ∑ i, (D i : ℝ) * gibbsWeight β (E i)

/-- The degeneracy-weighted Gibbs weight of level `i`, divided by the partition function. -/
def levelProbability {m : ℕ} (E : Fin m → ℝ) (D : Fin m → ℕ) (β : ℝ)
    (i : Fin m) : ℝ :=
  ((D i : ℝ) * gibbsWeight β (E i)) / partitionFunction E D β

/-- Every real Gibbs weight is strictly positive. -/
lemma gibbsWeight_pos (β E : ℝ) : 0 < gibbsWeight β E := Real.exp_pos _

/-- The partition function is positive when the level set is nonempty and every degeneracy is
positive. -/
lemma partitionFunction_pos {m : ℕ} (hm : 0 < m) (E : Fin m → ℝ) (D : Fin m → ℕ)
    (β : ℝ) (hD : ∀ i, 0 < D i) :
    0 < partitionFunction E D β := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 < (D i : ℝ) * gibbsWeight β (E i) := by
    intro i _
    exact mul_pos (by exact_mod_cast hD i) (gibbsWeight_pos β (E i))
  exact Finset.sum_pos hterm ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- Every level probability is nonnegative when the level set is nonempty and all degeneracies
are positive. -/
lemma levelProbability_nonneg {m : ℕ} (hm : 0 < m) (E : Fin m → ℝ) (D : Fin m → ℕ)
    (β : ℝ) (hD : ∀ i, 0 < D i) (i : Fin m) :
    0 ≤ levelProbability E D β i := by
  have hZ := partitionFunction_pos hm E D β hD
  unfold levelProbability
  exact div_nonneg (mul_nonneg (by positivity) (gibbsWeight_pos β (E i)).le) hZ.le

/-- The level probabilities sum to one for a nonempty level set with positive degeneracies. -/
theorem levelProbability_sum_one {m : ℕ} (hm : 0 < m) (E : Fin m → ℝ) (D : Fin m → ℕ)
    (β : ℝ) (hD : ∀ i, 0 < D i) :
    (∑ i, levelProbability E D β i) = 1 := by
  have hZ : partitionFunction E D β ≠ 0 := (partitionFunction_pos hm E D β hD).ne'
  simp only [levelProbability]
  rw [← Finset.sum_div]
  have hnum : (∑ i, (D i : ℝ) * gibbsWeight β (E i)) = partitionFunction E D β := rfl
  rw [hnum, div_self hZ]

/-- With positive degeneracies, dividing a level probability by its degeneracy gives its Gibbs
weight divided by the partition function [PoulinWocjan2009]. -/
theorem perState_level_probability {m : ℕ} (hm : 0 < m) (E : Fin m → ℝ) (D : Fin m → ℕ)
    (β : ℝ) (hD : ∀ i, 0 < D i) (i : Fin m) :
    levelProbability E D β i / (D i : ℝ) =
      gibbsWeight β (E i) / partitionFunction E D β := by
  have hZ : partitionFunction E D β ≠ 0 := (partitionFunction_pos hm E D β hD).ne'
  have hDne : ((D i : ℝ)) ≠ 0 := by exact_mod_cast (hD i).ne'
  simp only [levelProbability]
  rw [div_div]
  field_simp

/-- For a nonempty level set with positive degeneracies, the level probabilities sum to one and
each probability per state equals the normalized Gibbs weight [PoulinWocjan2009]. -/
theorem thermal_state_preparation {m : ℕ} (hm : 0 < m) (E : Fin m → ℝ) (D : Fin m → ℕ)
    (β : ℝ) (hD : ∀ i, 0 < D i) :
    (∑ i, levelProbability E D β i) = 1 ∧
    (∀ i, levelProbability E D β i / (D i : ℝ) =
      gibbsWeight β (E i) / partitionFunction E D β) :=
  ⟨levelProbability_sum_one hm E D β hD,
   fun i => perState_level_probability hm E D β hD i⟩

/-- For positive `p` and `T`, the lower bound `1/p ≤ T` implies `1/T ≤ p` [PoulinWocjan2009]. -/
theorem temperature_bound (p T : ℝ) (hp : 0 < p) (hT : 0 < T)
    (hTp : 1 / p ≤ T) :
    1 / T ≤ p := by
  rw [div_le_iff₀ hT]
  have h1 : 1 ≤ T * p := by
    rw [div_le_iff₀ hp] at hTp
    linarith [mul_comm T p]
  linarith [mul_comm T p]

end Qatlib.Papers.GroundState08.MainResults.Thermal
