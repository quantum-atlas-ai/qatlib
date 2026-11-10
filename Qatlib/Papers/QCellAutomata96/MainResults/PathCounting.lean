/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCellAutomata96.MainResults.PropagatorPathSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Papers.QCellAutomata96.MainResults

def rightBars (u k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 (u - 1)).powersetCard (k - 1)

def leftBars (v k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 v).powersetCard (k - 1)

def pathShapesOdd (u v k : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  rightBars u k ×ˢ leftBars v k

theorem pathShapesOdd_card (u v k : ℕ) :
    (pathShapesOdd u v k).card = (u - 1).choose (k - 1) * v.choose (k - 1) := by
  have h1 : (Finset.Icc 1 (u - 1)).card = u - 1 := by
    rw [Nat.card_Icc]; omega
  have h2 : (Finset.Icc 1 v).card = v := by
    rw [Nat.card_Icc]; omega
  rw [pathShapesOdd, Finset.card_product, rightBars, leftBars,
    Finset.card_powersetCard, Finset.card_powersetCard, h1, h2]

def pathShapesEven (u v k : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (Finset.Icc 1 u).powersetCard k ×ˢ (Finset.Icc 1 (v - 1)).powersetCard (k - 1)

theorem pathShapesEven_card (u v k : ℕ) :
    (pathShapesEven u v k).card = u.choose k * (v - 1).choose (k - 1) := by
  have h1 : (Finset.Icc 1 u).card = u := by
    rw [Nat.card_Icc]; omega
  have h2 : (Finset.Icc 1 (v - 1)).card = v - 1 := by
    rw [Nat.card_Icc]; omega
  rw [pathShapesEven, Finset.card_product, Finset.card_powersetCard,
    Finset.card_powersetCard, h1, h2]

theorem pathSumOdd_eq_pathCount (θ : ℝ) (u v : ℕ) :
    pathSumOdd θ u v =
      ∑ k ∈ Finset.range (min u (v + 1)),
        ((pathShapesOdd u v (k + 1)).card : ℂ) * oddAmp θ u v (k + 1) := by
  unfold pathSumOdd
  apply Finset.sum_congr rfl
  intro k _
  rw [pathShapesOdd_card]
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1]
  push_cast
  ring

theorem pathSumEven_eq_pathCount (θ : ℝ) (u v : ℕ) :
    pathSumEven θ u v =
      ∑ k ∈ Finset.range (min u v),
        ((pathShapesEven u v (k + 1)).card : ℂ) * evenAmp θ u v (k + 1) := by
  unfold pathSumEven
  apply Finset.sum_congr rfl
  intro k _
  rw [pathShapesEven_card]
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1]
  push_cast
  ring

def fullEvenAmp (θ : ℝ) (u v : ℕ) : ℂ :=
  (if v = 0 then (Real.cos θ : ℂ) ^ (u + v) else 0) + pathSumEven θ u v

theorem pathSumOdd_zero_theta (u v : ℕ) : pathSumOdd 0 u v = 0 := by
  unfold pathSumOdd
  apply Finset.sum_eq_zero
  intro k _
  have hexp : 2 * (k + 1) - 1 ≠ 0 := by omega
  have hsin : I * (Real.sin (0 : ℝ) : ℂ) = 0 := by simp
  simp [oddAmp, zero_pow hexp]

theorem fullEvenAmp_zero_theta (u v : ℕ) :
    fullEvenAmp 0 u v = if v = 0 then 1 else 0 := by
  unfold fullEvenAmp
  have hsum : pathSumEven 0 u v = 0 := by
    unfold pathSumEven
    apply Finset.sum_eq_zero
    intro k _
    have hexp : 2 * (k + 1) ≠ 0 := by omega
    have hsin : I * (Real.sin (0 : ℝ) : ℂ) = 0 := by simp
    simp [evenAmp, zero_pow hexp]
  rw [hsum, add_zero]
  simp

end Qatlib.Papers.QCellAutomata96.MainResults
