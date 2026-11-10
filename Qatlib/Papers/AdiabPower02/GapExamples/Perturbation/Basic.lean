/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Qatlib.Papers.AdiabPower02.GapExamples.QubitSpectrum

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Matrix

namespace Qatlib.Papers.AdiabPower02.GapExamples

def allOnes (n : ℕ) : Fin n → Bool := fun _ => true

def weightPot {n : ℕ} (z : Fin n → Bool) : ℝ := (boolWeight z : ℝ)

def perturbedPot {n : ℕ} (z : Fin n → Bool) : ℝ :=
  if z = allOnes n then -1 else (boolWeight z : ℝ)

@[simp] lemma perturbedPot_allOnes (n : ℕ) : perturbedPot (allOnes n) = -1 := by
  simp [perturbedPot]

lemma perturbedPot_of_ne {n : ℕ} {z : Fin n → Bool} (hz : z ≠ allOnes n) :
    perturbedPot z = weightPot z := by
  simp [perturbedPot, weightPot, hz]

lemma boolWeight_allOnes {n : ℕ} : boolWeight (allOnes n) = n := by
  simp [boolWeight, allOnes]

theorem ground_amplitude_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    amp1 s ^ n ≤ (1 / Real.sqrt 2) ^ n := by
  have h := amp_pow_le hs0 hs1 n
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    simp
  rwa [hsqrt] at h

theorem perturbation_amplitude_bound {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    c * amp1 s ^ n ≤ c * (1 / Real.sqrt 2) ^ n :=
  mul_le_mul_of_nonneg_left (ground_amplitude_bound hs0 hs1 n) hc

end Qatlib.Papers.AdiabPower02.GapExamples
