/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.PairingModel01.MainResults

open Qatlib.Concepts.ResourceBounds.AsymBounds

def pairingStepCount (N : ℕ) : ℚ :=
  (28 * (N : ℚ) ^ 4 - 47 * (N : ℚ) ^ 3 - 4 * (N : ℚ) ^ 2 + 32 * (N : ℚ)) / 3

theorem pairingStepCount_closed_form (N : ℕ) :
    pairingStepCount N = -(4 / 3) * (N : ℚ) ^ 2 + (32 / 3) * (N : ℚ) - (47 / 3) * (N : ℚ) ^ 3
      + (28 / 3) * (N : ℚ) ^ 4 := by
  unfold pairingStepCount
  ring

theorem pairingStepCount_le_ten (N : ℕ) (hN : 1 ≤ N) :
    pairingStepCount N ≤ 10 * (N : ℚ) ^ 4 := by
  have hNq : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hN0 : (0 : ℚ) ≤ (N : ℚ) := by linarith

  have hquad : (0 : ℚ) ≤ 2 * (N : ℚ) ^ 2 + 47 * (N : ℚ) - 49 := by
    nlinarith [sq_nonneg ((N : ℚ) - 1), hNq]
  have hprod : (0 : ℚ) ≤ (N : ℚ) ^ 2 * (2 * (N : ℚ) ^ 2 + 47 * (N : ℚ) - 49) :=
    mul_nonneg (sq_nonneg (N : ℚ)) hquad
  have hkey : (0 : ℚ) ≤ 2 * (N : ℚ) ^ 4 + 47 * (N : ℚ) ^ 3 - 49 * (N : ℚ) ^ 2 := by
    nlinarith [hprod]
  have h32 : (32 : ℚ) * (N : ℚ) ≤ 53 * (N : ℚ) ^ 2 := by
    have hfac : (0 : ℚ) ≤ (N : ℚ) * (53 * (N : ℚ) - 32) :=
      mul_nonneg hN0 (by linarith)
    nlinarith [hfac]
  unfold pairingStepCount
  nlinarith [hkey, h32]

theorem pairingStepCount_ge_nine (N : ℕ) (hN : 48 ≤ N) :
    9 * (N : ℚ) ^ 4 ≤ pairingStepCount N := by
  have hNq : (48 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have hN0 : (0 : ℚ) ≤ (N : ℚ) := by linarith

  have hA : 4 * (N : ℚ) + 32 ≤ (N : ℚ) ^ 2 := by
    have hfac : (0 : ℚ) ≤ ((N : ℚ) - 8) * ((N : ℚ) + 4) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hfac]

  have hB : (N : ℚ) ≤ (N : ℚ) ^ 2 - 47 * (N : ℚ) := by
    have hfac : (0 : ℚ) ≤ (N : ℚ) * ((N : ℚ) - 48) :=
      mul_nonneg hN0 (by linarith)
    nlinarith [hfac]
  have hmul : (4 * (N : ℚ) + 32) * (N : ℚ) ≤ (N : ℚ) ^ 2 * ((N : ℚ) ^ 2 - 47 * (N : ℚ)) := by
    exact mul_le_mul hA hB hN0 (by positivity)
  have hgoal : 4 * (N : ℚ) ^ 2 + 32 * (N : ℚ) ≤ (N : ℚ) ^ 4 - 47 * (N : ℚ) ^ 3 := by
    nlinarith [hmul]
  unfold pairingStepCount
  nlinarith [hgoal]

def pairingTotalSteps (k N : ℕ) : ℚ := (k : ℚ) * pairingStepCount N

theorem pairingTotalSteps_le (k : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    pairingTotalSteps k N ≤ (k : ℚ) * 10 * (N : ℚ) ^ 4 := by
  unfold pairingTotalSteps
  have h := pairingStepCount_le_ten N hN
  have hk : (0 : ℚ) ≤ (k : ℚ) := by positivity
  nlinarith [h, hk]

def pairingStepBudget (N : ℕ) : ℕ := 10 * (N + 1) ^ 4

theorem pairingStepCount_le_budget (N : ℕ) :
    pairingStepCount N ≤ (pairingStepBudget N : ℚ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    norm_num [pairingStepCount, pairingStepBudget]
  · have h := pairingStepCount_le_ten N hN
    have hle : (N : ℚ) ^ 4 ≤ ((N : ℚ) + 1) ^ 4 := by
      refine pow_le_pow_left₀ (by positivity) (by linarith) 4
    unfold pairingStepBudget
    push_cast
    nlinarith [h, hle]

theorem pairingTotalSteps_le_budget (k N : ℕ) :
    pairingTotalSteps k N ≤ (k : ℚ) * (pairingStepBudget N : ℚ) := by
  unfold pairingTotalSteps
  have h := pairingStepCount_le_budget N
  have hk : (0 : ℚ) ≤ (k : ℚ) := by positivity
  nlinarith [h, hk]

theorem pairingStepBudget_uniformUpperBound :
    uniformUpperBound pairingStepBudget 10 4 := by
  intro n
  unfold pairingStepBudget
  exact le_rfl

def beyondNearestNeighborSteps (D N : ℕ) : ℕ := N ^ 2 * (D * N ^ 3)

theorem beyondNearestNeighborSteps_eq (D N : ℕ) :
    beyondNearestNeighborSteps D N = D * N ^ 5 := by
  unfold beyondNearestNeighborSteps
  ring

theorem beyondNearestNeighborSteps_uniformUpperBound (D : ℕ) :
    uniformUpperBound (beyondNearestNeighborSteps D) D 5 := by
  intro N
  unfold beyondNearestNeighborSteps
  rw [show N ^ 2 * (D * N ^ 3) = D * N ^ 5 by ring]
  exact Nat.mul_le_mul_left D (pow_le_pow_left₀ (Nat.zero_le N) (Nat.le_succ N) 5)

end Qatlib.Papers.PairingModel01.MainResults
