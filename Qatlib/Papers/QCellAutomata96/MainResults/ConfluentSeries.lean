/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.NhdsWithin

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Papers.QCellAutomata96.MainResults

def zeroFone1 (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((Nat.factorial n : ℂ) * (Nat.factorial n : ℂ))

def zeroFone2 (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((Nat.factorial (n + 1) : ℂ) * (Nat.factorial n : ℂ))

def besselJ0 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (z / 2) ^ (2 * n) / ((Nat.factorial n : ℂ) ^ 2)

def besselJ1 (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * (z / 2) ^ (2 * n + 1) /
    ((Nat.factorial n : ℂ) * (Nat.factorial (n + 1) : ℂ))

def tau (u v : ℝ) : ℝ := 2 * Real.sqrt (u * v)

def confluentOddAmp (θ u v ε : ℝ) : ℂ :=
  (I * Complex.ofReal (Real.tan (ε * θ))) *
    zeroFone1 (Complex.ofReal (-((u * v) / ε ^ 2 * (Real.tan (ε * θ)) ^ 2)))

def confluentEvenAmp (θ u v ε : ℝ) : ℂ :=
  Complex.ofReal (-((u / ε) * (Real.tan (ε * θ)) ^ 2)) *
    zeroFone2 (Complex.ofReal (-((u * v) / ε ^ 2 * (Real.tan (ε * θ)) ^ 2)))

theorem besselJ0_zeroFone (z : ℂ) : besselJ0 (2 * z) = zeroFone1 (-(z ^ 2)) := by
  unfold besselJ0 zeroFone1
  apply tsum_congr
  intro n
  have hp : (-(z ^ 2)) ^ n = (-1 : ℂ) ^ n * (z ^ 2) ^ n := by
    rw [neg_eq_neg_one_mul, mul_pow]
  simp only [show (2 * z) / 2 = z by ring, hp, pow_mul]
  ring

theorem besselJ1_zeroFone (z : ℂ) : besselJ1 (2 * z) = z * zeroFone2 (-(z ^ 2)) := by
  unfold besselJ1 zeroFone2
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [show (2 * z) / 2 = z by ring, pow_succ, pow_mul]
  ring

end Qatlib.Papers.QCellAutomata96.MainResults
