/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.ChemDynamics08.MainResults.Resources

noncomputable def multiplyCost (m : ℝ) : ℝ := 5 / 4 * m ^ 3 + m ^ 2

noncomputable def subtractCost (m : ℝ) : ℝ := 3 / 2 * m ^ 2

noncomputable def squaringCost (m : ℝ) : ℝ := 5 / 4 * m ^ 3 + 5 / 2 * m ^ 2

noncomputable def newtonIterationCost (m : ℝ) : ℝ :=
  subtractCost m + 3 * multiplyCost m

noncomputable def reciprocalCost (m : ℝ) : ℝ := 4 * newtonIterationCost m

noncomputable def distanceSquaredCost (m : ℝ) : ℝ := 3 * squaringCost m

noncomputable def coulombPairCost (m : ℝ) : ℝ :=
  distanceSquaredCost m + reciprocalCost m

theorem distanceSquaredCost_eq (m : ℝ) :
    distanceSquaredCost m = 15 / 4 * m ^ 3 + 15 / 2 * m ^ 2 := by
  unfold distanceSquaredCost squaringCost
  ring

theorem newtonIterationCost_eq (m : ℝ) :
    newtonIterationCost m = 15 / 4 * m ^ 3 + 9 / 2 * m ^ 2 := by
  unfold newtonIterationCost subtractCost multiplyCost
  ring

theorem reciprocalCost_eq (m : ℝ) :
    reciprocalCost m = 15 * m ^ 3 + 18 * m ^ 2 := by
  unfold reciprocalCost newtonIterationCost subtractCost multiplyCost
  ring

theorem coulomb_pair_gate_count (m : ℝ) :
    coulombPairCost m = 75 / 4 * m ^ 3 + 51 / 2 * m ^ 2 := by
  unfold coulombPairCost distanceSquaredCost squaringCost
    reciprocalCost newtonIterationCost subtractCost multiplyCost
  ring

noncomputable def pairCount (B : ℕ) : ℝ := (B : ℝ) * ((B : ℝ) - 1) / 2

noncomputable def coulombStepCost (B : ℕ) (m : ℝ) : ℝ :=
  pairCount B * coulombPairCost m

theorem pairCount_le (B : ℕ) (hB : 1 ≤ B) :
    pairCount B ≤ (B : ℝ) ^ 2 / 2 := by
  unfold pairCount
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
  nlinarith

theorem pairCount_nonneg (B : ℕ) (hB : 1 ≤ B) : 0 ≤ pairCount B := by
  unfold pairCount
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
  have hBc : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hB1 : (0 : ℝ) ≤ (B : ℝ) - 1 := by linarith
  have := mul_nonneg hB0 hB1
  linarith

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

noncomputable def coulombStepCost_m2 (B : ℕ) (m c : ℝ) : ℝ :=
  pairCount B * (c * m ^ 2)

theorem coulomb_step_cost_quadratic (B : ℕ) (m c : ℝ) (hB : 1 ≤ B)
    (_hm : 0 ≤ m) (hc : 0 ≤ c) :
    coulombStepCost_m2 B m c ≤ (c / 2) * (B : ℝ) ^ 2 * m ^ 2 := by
  unfold coulombStepCost_m2
  have hpc := pairCount_le B hB
  calc
    pairCount B * (c * m ^ 2) ≤ ((B : ℝ) ^ 2 / 2) * (c * m ^ 2) :=
          mul_le_mul_of_nonneg_right hpc (by positivity)
    _ = (c / 2) * (B : ℝ) ^ 2 * m ^ 2 := by ring

def degreesOfFreedom (B : ℕ) : ℕ := 3 * B - 6

def stateRegisterQubits (n B : ℕ) : ℕ := n * degreesOfFreedom B

def ancillaQubits (m : ℕ) : ℕ := 4 * m

def totalWavefunctionQubits (n B m : ℕ) : ℕ :=
  stateRegisterQubits n B + ancillaQubits m

theorem degreesOfFreedom_eq (B : ℕ) (hB : 2 ≤ B) :
    degreesOfFreedom B = 3 * (B - 2) := by
  unfold degreesOfFreedom
  omega

theorem chem_qubit_count (n B m : ℕ) (hB : 2 ≤ B) :
    totalWavefunctionQubits n B m = n * (3 * (B - 2)) + 4 * m := by
  unfold totalWavefunctionQubits stateRegisterQubits ancillaQubits
  rw [degreesOfFreedom_eq B hB]

end Qatlib.Papers.ChemDynamics08.MainResults.Resources
