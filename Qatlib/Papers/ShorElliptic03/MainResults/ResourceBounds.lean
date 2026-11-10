/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.ShorElliptic03.MainResults.ResourceBounds

def paperLog2 (x : ℝ) : ℝ := Real.logb 2 x

def dlogQubitsNoSharing (n : ℕ) (ε : ℝ) : ℝ :=
  7 * (n : ℝ) + 4 * paperLog2 (n : ℝ) + ε

def dlogQubitsWithSharing (n : ℕ) (ε : ℝ) : ℝ :=
  5 * (n : ℝ) + 8 * Real.sqrt (n : ℝ) + 4 * paperLog2 (n : ℝ) + ε

def rsaQubits (n : ℕ) : ℝ := 2 * (n : ℝ)

theorem sqrt160_le_thirteen : Real.sqrt (160 : ℝ) ≤ 13 := by
  have h := Real.sqrt_le_sqrt (show (160 : ℝ) ≤ 169 by norm_num)
  have h169 : Real.sqrt (169 : ℝ) = 13 := by
    rw [show (169 : ℝ) = 13 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

theorem logb160_le_eight : paperLog2 (160 : ℝ) ≤ 8 := by
  unfold paperLog2
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
  norm_num

theorem ecc160_qubits_le_1000 (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 10) :
    dlogQubitsWithSharing 160 ε ≤ 1000 := by
  unfold dlogQubitsWithSharing
  have h1 := sqrt160_le_thirteen
  have h2 := logb160_le_eight
  norm_num at h1 h2 ⊢
  linarith

theorem rsa1024_qubits : rsaQubits 1024 = 2048 := by
  unfold rsaQubits
  norm_num

theorem ecc160_beats_rsa1024 (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 10) :
    dlogQubitsWithSharing 160 ε < rsaQubits 1024 := by
  have h := ecc160_qubits_le_1000 ε hε0 hε
  rw [rsa1024_qubits]
  linarith

theorem dlogQubitsNoSharing_le_linear (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 10) :
    dlogQubitsNoSharing n ε ≤ 21 * (n : ℝ) := by
  unfold dlogQubitsNoSharing
  have hl : paperLog2 (n : ℝ) ≤ (n : ℝ) := by
    unfold paperLog2
    rcases Nat.eq_zero_or_pos n with h | hpos
    · subst h
      simp
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
      rw [Real.rpow_natCast]
      exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem dlogQubitsWithSharing_le_linear (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 10) :
    dlogQubitsWithSharing n ε ≤ 27 * (n : ℝ) := by
  unfold dlogQubitsWithSharing
  have hl : paperLog2 (n : ℝ) ≤ (n : ℝ) := by
    unfold paperLog2
    rcases Nat.eq_zero_or_pos n with h | hpos
    · subst h
      simp
    · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
      rw [Real.rpow_natCast]
      exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hs : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ))
      (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

theorem dlogQubits_isO_linear (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      dlogQubitsNoSharing n ε ≤ C * (n : ℝ) ∧
      dlogQubitsWithSharing n ε ≤ C * (n : ℝ) := by
  refine ⟨27, by norm_num, ?_⟩
  intro n hn
  refine ⟨?_, dlogQubitsWithSharing_le_linear n hn ε hε0 hε⟩
  have h := dlogQubitsNoSharing_le_linear n hn ε hε0 hε
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

def totalAdditionsNoSharing (n : ℕ) : ℝ :=
  2 * (n : ℝ) *
    (5 + 3 * (n : ℝ) +
      2 * (6 * (n : ℝ) + 2 * (4.5 * (5 * (n : ℝ))))) * 1.7

def totalAdditionsWithSharing (n : ℕ) : ℝ :=
  2 * (n : ℝ) *
    (5 + 3 * (n : ℝ) +
      2 * (6 * (n : ℝ) +
        2 * (4.5 * 5 * ((n : ℝ) / 2 + 2 * Real.sqrt (n : ℝ))))) * 1.7

theorem totalAdditionsNoSharing_eq (n : ℕ) :
    totalAdditionsNoSharing n = 357 * (n : ℝ) ^ 2 + 17 * (n : ℝ) := by
  unfold totalAdditionsNoSharing
  ring

theorem totalAdditionsNoSharing_le (n : ℕ) (hn : 6 ≤ n) :
    totalAdditionsNoSharing n ≤ 360 * (n : ℝ) ^ 2 := by
  rw [totalAdditionsNoSharing_eq]
  have hn' : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))
    (by linarith : (0 : ℝ) ≤ 3 * (n : ℝ) - 17)]

theorem totalAdditionsWithSharing_eq (n : ℕ) :
    totalAdditionsWithSharing n =
      204 * (n : ℝ) ^ 2 + 612 * (n : ℝ) * Real.sqrt (n : ℝ) + 17 * (n : ℝ) := by
  unfold totalAdditionsWithSharing
  ring

theorem totalAdditionsWithSharing_le (n : ℕ) (hn : 9 ≤ n) :
    totalAdditionsWithSharing n ≤
      205 * (n : ℝ) ^ 2 + 615 * (n : ℝ) * Real.sqrt (n : ℝ) := by
  rw [totalAdditionsWithSharing_eq]
  have hn' : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h9]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))
    (by linarith : (0 : ℝ) ≤ (n : ℝ) + 3 * Real.sqrt (n : ℝ) - 17)]

theorem dlog_running_time_cubic_noSharing (k : ℝ) (hk : 0 < k) (n : ℕ)
    (hn : 6 ≤ n) :
    k * (n : ℝ) * totalAdditionsNoSharing n ≤
      360 * k * (n : ℝ) ^ 3 := by
  rw [totalAdditionsNoSharing_eq]
  have hn' : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := le_of_lt hk
  nlinarith [mul_nonneg (mul_nonneg hk0 (sq_nonneg (n : ℝ)))
    (by linarith : (0 : ℝ) ≤ 3 * (n : ℝ) - 17)]

theorem dlog_running_time_cubic_withSharing (k : ℝ) (hk : 0 < k) (n : ℕ)
    (hn : 9 ≤ n) :
    k * (n : ℝ) * totalAdditionsWithSharing n ≤
      205 * k * (n : ℝ) ^ 3 + 615 * k * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) := by
  rw [totalAdditionsWithSharing_eq]
  have hn' : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : (3 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h9 : Real.sqrt (9 : ℝ) = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h9]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hk0 : (0 : ℝ) ≤ k := le_of_lt hk
  nlinarith [mul_nonneg (mul_nonneg hk0 (sq_nonneg (n : ℝ)))
    (by linarith : (0 : ℝ) ≤ (n : ℝ) + 3 * Real.sqrt (n : ℝ) - 17)]

def euclidCycleCost (n w : ℕ) : ℝ := 4.5 * (n : ℝ) * (5 * (w : ℝ))

theorem euclidCycleCost_le_sq (n w : ℕ) (hw : w ≤ n) :
    euclidCycleCost n w ≤ 22.5 * (n : ℝ) ^ 2 := by
  unfold euclidCycleCost
  have hw' : (w : ℝ) ≤ (n : ℝ) := by exact_mod_cast hw
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

theorem euclid_runtime_isO_quadratic :
    ∃ C : ℝ, 0 < C ∧ ∀ n w : ℕ, w ≤ n →
      euclidCycleCost n w ≤ C * (n : ℝ) ^ 2 :=
  ⟨22.5, by norm_num, euclidCycleCost_le_sq⟩

end Qatlib.Papers.ShorElliptic03.MainResults.ResourceBounds
