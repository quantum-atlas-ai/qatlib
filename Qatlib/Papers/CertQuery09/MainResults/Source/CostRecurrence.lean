/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CertQuery09.MainResults.Source

structure QueryCostModel (d : ℕ) (a b c₁ : ℝ) where

  E0 : ℕ → ℝ

  E1 : ℕ → ℝ
  base0 : E0 1 = (d : ℝ)
  base1 : E1 1 = c₁ * Real.sqrt (d : ℝ)

  step1 : ∀ k : ℕ, 2 ≤ k →
    E1 k ≤ a * Real.sqrt ((d : ℝ) ^ k)
      + b * (k : ℝ) * Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))
      + E0 (k - 1)

  step0 : ∀ k : ℕ, 2 ≤ k → E0 k = (d : ℝ) * E1 (k - 1)

private lemma sqrt_pow_mul_sqrt (d k : ℕ) :
    Real.sqrt ((d : ℝ) ^ k) * Real.sqrt (d : ℝ) = Real.sqrt ((d : ℝ) ^ (k + 1)) := by
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ (d : ℝ) ^ k by positivity)]
  congr 1

private lemma sqrt_mul_sqrt_pow_pred (d k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) = Real.sqrt ((d : ℝ) ^ k) := by
  rw [← Real.sqrt_mul (show (0 : ℝ) ≤ (d : ℝ) by positivity)]
  congr 1
  conv_rhs => rw [← Nat.sub_add_cancel hk, pow_succ]
  ring

private lemma log_mul_sqrt_pred (d k : ℕ) (hd : 0 < d) (hk : 1 ≤ k) :
    Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) =
      (Real.log (d : ℝ) / Real.sqrt (d : ℝ)) * Real.sqrt ((d : ℝ) ^ k) := by
  have hsd : Real.sqrt (d : ℝ) ≠ 0 := by
    have hpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact ne_of_gt hpos
  have hs := sqrt_mul_sqrt_pow_pred d k hk
  calc Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))
      = ((Real.log (d : ℝ) / Real.sqrt (d : ℝ)) * Real.sqrt (d : ℝ)) *
          Real.sqrt ((d : ℝ) ^ (k - 1)) := by
        rw [div_mul_cancel₀ (Real.log (d : ℝ)) hsd]
    _ = (Real.log (d : ℝ) / Real.sqrt (d : ℝ)) *
          (Real.sqrt (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))) := by ring
    _ = (Real.log (d : ℝ) / Real.sqrt (d : ℝ)) * Real.sqrt ((d : ℝ) ^ k) := by rw [hs]

theorem lemma2_expected_query_cost (d : ℕ) (hd : 2 ≤ d)
    (a b c₁ : ℝ) (M : QueryCostModel d a b c₁) :
    let C := max (max a b) (max c₁ 1)
    let L := Real.log (d : ℝ) / Real.sqrt (d : ℝ)
    0 < C ∧
      ∀ k : ℕ, 1 ≤ k →
        M.E0 k ≤ C * (k : ℝ) * (1 + (k : ℝ) * L) * Real.sqrt ((d : ℝ) ^ (k + 1)) ∧
        M.E1 k ≤ C * (k : ℝ) * (1 + (k : ℝ) * L) * Real.sqrt ((d : ℝ) ^ k) := by
  intro C L
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdR : (0 : ℝ) ≤ (d : ℝ) := le_of_lt hd0
  have hL : 0 ≤ L := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
    · positivity
  have hC1 : (1 : ℝ) ≤ C := by
    have h1 : (1 : ℝ) ≤ max c₁ 1 := le_max_right _ _
    exact le_trans h1 (le_max_right _ _)
  have hC0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have hCa : a ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCb : b ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCc : c₁ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hL1 : (1 : ℝ) ≤ 1 + L := by linarith
  have hCL1 : (1 : ℝ) ≤ C * (1 + L) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (1 + L) := mul_le_mul hC1 hL1 zero_le_one hC0
  have hCLc : c₁ ≤ C * (1 + L) := by
    calc c₁ ≤ C := hCc
      _ = C * 1 := by ring
      _ ≤ C * (1 + L) := mul_le_mul_of_nonneg_left hL1 hC0
  refine ⟨lt_of_lt_of_le zero_lt_one hC1, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_or_lt_of_le hk with hk1 | hk2
    · subst hk1
      constructor
      · rw [M.base0]
        have hsq : Real.sqrt ((d : ℝ) ^ (1 + 1)) = (d : ℝ) := by
          rw [show (1 : ℕ) + 1 = 2 by norm_num, Real.sqrt_sq hdR]
        have hCL1' : (1 : ℝ) ≤ C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L) := by
          simpa using hCL1
        calc (d : ℝ) = 1 * (d : ℝ) := by ring
          _ ≤ (C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L)) * (d : ℝ) :=
              mul_le_mul_of_nonneg_right hCL1' hdR
          _ = C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L) *
                Real.sqrt ((d : ℝ) ^ (1 + 1)) := by rw [hsq]
      · rw [M.base1]
        have hsq1 : Real.sqrt ((d : ℝ) ^ (1 : ℕ)) = Real.sqrt (d : ℝ) := by norm_num
        have hCLc' : c₁ ≤ C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L) := by
          simpa using hCLc
        calc c₁ * Real.sqrt (d : ℝ)
            ≤ (C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L)) * Real.sqrt (d : ℝ) :=
              mul_le_mul_of_nonneg_right hCLc' (by positivity)
          _ = C * ((1 : ℕ) : ℝ) * (1 + ((1 : ℕ) : ℝ) * L) *
                Real.sqrt ((d : ℝ) ^ 1) := by rw [hsq1]
    · have hk2' : 2 ≤ k := hk2
      have hkm : 1 ≤ k - 1 := by omega
      have hcastsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k)]
        norm_num
      have ihp := ih (k - 1) (by omega) hkm
      obtain ⟨ihE0, ihE1⟩ := ihp
      have ihE0' : M.E0 (k - 1) ≤
          C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) *
            Real.sqrt ((d : ℝ) ^ k) := by
        have h := ihE0
        rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
        exact h

      have hdS : (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) = Real.sqrt ((d : ℝ) ^ (k + 1)) := by
        calc (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))
            = Real.sqrt ((d : ℝ) ^ 2) * Real.sqrt ((d : ℝ) ^ (k - 1)) := by rw [Real.sqrt_sq hdR]
          _ = Real.sqrt (((d : ℝ) ^ 2) * ((d : ℝ) ^ (k - 1))) :=
                (Real.sqrt_mul (show (0 : ℝ) ≤ (d : ℝ) ^ 2 by positivity) _).symm
          _ = Real.sqrt ((d : ℝ) ^ (k + 1)) := by
                congr 1
                rw [← pow_add]
                congr 1
                omega

      have hlog : Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) =
          L * Real.sqrt ((d : ℝ) ^ k) := log_mul_sqrt_pred d k (by omega : 0 < d) (by omega : 1 ≤ k)
      have hterm2 : b * (k : ℝ) * Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) =
          b * (k : ℝ) * L * Real.sqrt ((d : ℝ) ^ k) := by
        calc b * (k : ℝ) * Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))
            = b * (k : ℝ) * (Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1))) := by ring
          _ = b * (k : ℝ) * (L * Real.sqrt ((d : ℝ) ^ k)) := by rw [hlog]
          _ = b * (k : ℝ) * L * Real.sqrt ((d : ℝ) ^ k) := by ring

      have hK1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      have hKm0 : (0 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by positivity
      have hKmK : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 ≤ k)
      have hbKL : b * (k : ℝ) * L ≤ C * (k : ℝ) * L := by
        calc b * (k : ℝ) * L = b * ((k : ℝ) * L) := by ring
          _ ≤ C * ((k : ℝ) * L) :=
              mul_le_mul_of_nonneg_right hCb (mul_nonneg (by positivity) hL)
          _ = C * (k : ℝ) * L := by ring
      have hthird : C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) ≤
          C * ((k : ℝ) - 1) * (1 + (k : ℝ) * L) := by
        have hKmK1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) - 1 := le_of_eq hcastsub
        have hfac : 1 + ((k - 1 : ℕ) : ℝ) * L ≤ 1 + (k : ℝ) * L := by
          have h := mul_le_mul_of_nonneg_right hKmK hL
          linarith
        have hpre : C * ((k - 1 : ℕ) : ℝ) ≤ C * ((k : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hKmK1 hC0
        have hb0 : (0 : ℝ) ≤ 1 + ((k - 1 : ℕ) : ℝ) * L := by
          have := mul_nonneg hKm0 hL
          linarith
        have hc0 : (0 : ℝ) ≤ C * ((k : ℝ) - 1) := by
          apply mul_nonneg hC0
          linarith
        exact mul_le_mul hpre hfac hb0 hc0
      have hcoef : a + b * (k : ℝ) * L + C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) ≤
          C * (k : ℝ) * (1 + (k : ℝ) * L) := by
        have hsum : a + b * (k : ℝ) * L +
            C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) ≤
            C + C * (k : ℝ) * L + C * ((k : ℝ) - 1) * (1 + (k : ℝ) * L) := by
          linarith [hCa, hbKL, hthird]
        have hEq : C + C * (k : ℝ) * L + C * ((k : ℝ) - 1) * (1 + (k : ℝ) * L) =
            C * (k : ℝ) * (1 + (k : ℝ) * L) := by ring
        linarith

      have hmono : C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) ≤
          C * (k : ℝ) * (1 + (k : ℝ) * L) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hKmK hC0
        · have h := mul_le_mul_of_nonneg_right hKmK hL
          linarith
        · have h := mul_nonneg hKm0 hL
          linarith
        · exact mul_nonneg hC0 (by positivity)
      have hS0 : (0 : ℝ) ≤ Real.sqrt ((d : ℝ) ^ k) := by positivity
      constructor
      · calc M.E0 k = (d : ℝ) * M.E1 (k - 1) := M.step0 k hk2'
          _ ≤ (d : ℝ) * (C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) *
                Real.sqrt ((d : ℝ) ^ (k - 1))) := mul_le_mul_of_nonneg_left ihE1 hdR
          _ = C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) *
                Real.sqrt ((d : ℝ) ^ (k + 1)) := by rw [← hdS]; ring
          _ ≤ C * (k : ℝ) * (1 + (k : ℝ) * L) * Real.sqrt ((d : ℝ) ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right hmono (by positivity)
      · calc M.E1 k
            ≤ a * Real.sqrt ((d : ℝ) ^ k) +
                b * (k : ℝ) * Real.log (d : ℝ) * Real.sqrt ((d : ℝ) ^ (k - 1)) + M.E0 (k - 1) :=
              M.step1 k hk2'
          _ = a * Real.sqrt ((d : ℝ) ^ k) + (b * (k : ℝ) * L * Real.sqrt ((d : ℝ) ^ k)) +
                M.E0 (k - 1) := by rw [hterm2]
          _ ≤ a * Real.sqrt ((d : ℝ) ^ k) + (b * (k : ℝ) * L * Real.sqrt ((d : ℝ) ^ k)) +
                (C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L) *
                  Real.sqrt ((d : ℝ) ^ k)) := by linarith [ihE0']
          _ = (a + b * (k : ℝ) * L +
                C * ((k - 1 : ℕ) : ℝ) * (1 + ((k - 1 : ℕ) : ℝ) * L)) *
                Real.sqrt ((d : ℝ) ^ k) := by ring
          _ ≤ (C * (k : ℝ) * (1 + (k : ℝ) * L)) * Real.sqrt ((d : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_right hcoef hS0
          _ = C * (k : ℝ) * (1 + (k : ℝ) * L) * Real.sqrt ((d : ℝ) ^ k) := by ring

end Qatlib.Papers.CertQuery09.MainResults.Source
