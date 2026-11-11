/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Chemical dynamics resource estimates

This module defines arithmetic cost polynomials and combines them into pairwise and total
Coulomb evaluation costs. It derives explicit cubic precision bounds, a separate bound under a
quadratic per-pair cost model, and qubit counts for the wavefunction and ancillary registers.

These constructions support the treatment in [KassalEtAl2008].

## Main statements

* `coulomb_pair_gate_count`: evaluates the pair cost as `(75/4)m³ + (51/2)m²`.
* `chem_qubit_count`: evaluates the total register size for at least two particles.

## References

* [Kassal et al., 2008][KassalEtAl2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.ChemDynamics08.MainResults.Resources

/-- The multiplication cost polynomial `(5/4)m³ + m²`. -/
noncomputable def multiplyCost (m : ℝ) : ℝ := 5 / 4 * m ^ 3 + m ^ 2

/-- The subtraction cost polynomial `(3/2)m²`. -/
noncomputable def subtractCost (m : ℝ) : ℝ := 3 / 2 * m ^ 2

/-- The squaring cost polynomial `(5/4)m³ + (5/2)m²`. -/
noncomputable def squaringCost (m : ℝ) : ℝ := 5 / 4 * m ^ 3 + 5 / 2 * m ^ 2

/-- The cost of one subtraction and three multiplications at precision parameter `m`. -/
noncomputable def newtonIterationCost (m : ℝ) : ℝ :=
  subtractCost m + 3 * multiplyCost m

/-- The cost of four Newton iterations at precision parameter `m`. -/
noncomputable def reciprocalCost (m : ℝ) : ℝ := 4 * newtonIterationCost m

/-- The cost of three squaring operations at precision parameter `m`. -/
noncomputable def distanceSquaredCost (m : ℝ) : ℝ := 3 * squaringCost m

/-- The sum of the squared-distance and reciprocal costs for a particle pair. -/
noncomputable def coulombPairCost (m : ℝ) : ℝ :=
  distanceSquaredCost m + reciprocalCost m

/-- The squared-distance cost equals `(15/4)m³ + (15/2)m²` [KassalEtAl2008]. -/
theorem distanceSquaredCost_eq (m : ℝ) :
    distanceSquaredCost m = 15 / 4 * m ^ 3 + 15 / 2 * m ^ 2 := by
  unfold distanceSquaredCost squaringCost
  ring

/-- The Newton iteration cost equals `(15/4)m³ + (9/2)m²`. -/
theorem newtonIterationCost_eq (m : ℝ) :
    newtonIterationCost m = 15 / 4 * m ^ 3 + 9 / 2 * m ^ 2 := by
  unfold newtonIterationCost subtractCost multiplyCost
  ring

/-- The reciprocal cost equals `15m³ + 18m²` [KassalEtAl2008]. -/
theorem reciprocalCost_eq (m : ℝ) :
    reciprocalCost m = 15 * m ^ 3 + 18 * m ^ 2 := by
  unfold reciprocalCost newtonIterationCost subtractCost multiplyCost
  ring

/-- The modeled Coulomb cost per particle pair equals `(75/4)m³ + (51/2)m²` [KassalEtAl2008]. -/
theorem coulomb_pair_gate_count (m : ℝ) :
    coulombPairCost m = 75 / 4 * m ^ 3 + 51 / 2 * m ^ 2 := by
  unfold coulombPairCost distanceSquaredCost squaringCost
    reciprocalCost newtonIterationCost subtractCost multiplyCost
  ring

/-- The real-valued pair count `B(B - 1)/2`. -/
noncomputable def pairCount (B : ℕ) : ℝ := (B : ℝ) * ((B : ℝ) - 1) / 2

/-- The modeled Coulomb step cost, obtained by multiplying the pair count by the per-pair cost. -/
noncomputable def coulombStepCost (B : ℕ) (m : ℝ) : ℝ :=
  pairCount B * coulombPairCost m

/-- For at least one particle, the pair count is at most `B² / 2`. -/
theorem pairCount_le (B : ℕ) (hB : 1 ≤ B) :
    pairCount B ≤ (B : ℝ) ^ 2 / 2 := by
  unfold pairCount
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
  nlinarith

/-- The pair count is nonnegative for at least one particle. -/
theorem pairCount_nonneg (B : ℕ) (hB : 1 ≤ B) : 0 ≤ pairCount B := by
  unfold pairCount
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hBc : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hB1 : (0 : ℝ) ≤ (B : ℝ) - 1 := by linarith
  have := mul_nonneg hB0 hB1
  linarith

/-- For `B ≥ 1` and `m ≥ 1`, the modeled Coulomb step cost is at most `(177/8)B²m³`
[KassalEtAl2008]. -/
theorem coulomb_step_cost_cubic (B : ℕ) (m : ℝ) (hB : 1 ≤ B) (hm : 1 ≤ m) :
    coulombStepCost B m ≤ (177 / 8) * (B : ℝ) ^ 2 * m ^ 3 := by
  rw [coulombStepCost, coulomb_pair_gate_count]
  have hpc := pairCount_le B hB
  have hpc0 := pairCount_nonneg B hB
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hm2 : m ^ 2 ≤ m ^ 3 := by
    have hfac : 0 ≤ m ^ 2 * (m - 1) := by
      exact mul_nonneg (sq_nonneg m) (by linarith)
    nlinarith
  have hbound : 75 / 4 * m ^ 3 + 51 / 2 * m ^ 2 ≤ 177 / 4 * m ^ 3 := by
    nlinarith
  calc
    pairCount B * (75 / 4 * m ^ 3 + 51 / 2 * m ^ 2)
        ≤ pairCount B * (177 / 4 * m ^ 3) :=
          mul_le_mul_of_nonneg_left hbound hpc0
    _ ≤ ((B : ℝ) ^ 2 / 2) * (177 / 4 * m ^ 3) :=
          mul_le_mul_of_nonneg_right hpc (by positivity)
    _ = 177 / 8 * (B : ℝ) ^ 2 * m ^ 3 := by ring

/-- The total pair cost under the alternative per-pair model `c * m²`. -/
noncomputable def coulombStepCost_m2 (B : ℕ) (m c : ℝ) : ℝ :=
  pairCount B * (c * m ^ 2)

/-- For nonnegative `m` and `c` and `B ≥ 1`, the quadratic per-pair model has total cost at most
`(c/2)B²m²` [KassalEtAl2008]. -/
theorem coulomb_step_cost_quadratic (B : ℕ) (m c : ℝ) (hB : 1 ≤ B)
    (_hm : 0 ≤ m) (hc : 0 ≤ c) :
    coulombStepCost_m2 B m c ≤ (c / 2) * (B : ℝ) ^ 2 * m ^ 2 := by
  unfold coulombStepCost_m2
  have hpc := pairCount_le B hB
  calc
    pairCount B * (c * m ^ 2) ≤ ((B : ℝ) ^ 2 / 2) * (c * m ^ 2) :=
          mul_le_mul_of_nonneg_right hpc (by positivity)
    _ = (c / 2) * (B : ℝ) ^ 2 * m ^ 2 := by ring

/-- The natural-number count `3 * B - 6`, using truncated subtraction. -/
def degreesOfFreedom (B : ℕ) : ℕ := 3 * B - 6

/-- The wavefunction register size with `n` qubits per degree of freedom. -/
def stateRegisterQubits (n B : ℕ) : ℕ := n * degreesOfFreedom B

/-- The ancillary register size `4 * m`. -/
def ancillaQubits (m : ℕ) : ℕ := 4 * m

/-- The sum of the wavefunction and ancillary register sizes. -/
def totalWavefunctionQubits (n B m : ℕ) : ℕ :=
  stateRegisterQubits n B + ancillaQubits m

/-- For `B ≥ 2`, the degree count `3 * B - 6` equals `3 * (B - 2)`. -/
theorem degreesOfFreedom_eq (B : ℕ) (hB : 2 ≤ B) :
    degreesOfFreedom B = 3 * (B - 2) := by
  unfold degreesOfFreedom
  omega

/-- For `B ≥ 2`, the total modeled register size is `n * (3 * (B - 2)) + 4 * m` qubits
[KassalEtAl2008]. -/
theorem chem_qubit_count (n B m : ℕ) (hB : 2 ≤ B) :
    totalWavefunctionQubits n B m = n * (3 * (B - 2)) + 4 * m := by
  unfold totalWavefunctionQubits stateRegisterQubits ancillaQubits
  rw [degreesOfFreedom_eq B hB]

end Qatlib.Papers.ChemDynamics08.MainResults.Resources
