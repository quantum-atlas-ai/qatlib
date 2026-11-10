/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
namespace Qatlib.Papers.CommutingLLL13.NativeFix
noncomputable section

def logBits (x : ℝ) : ℝ := Real.logb 2 x

def slackBits (k : ℕ) (g r : ℝ) : ℝ := k - logBits (g * r * Real.exp 1)

def etaBits (δ : ℝ) (k : ℕ) (g r : ℝ) : ℝ := 1 / (δ * slackBits k g r)

def thresholdBits (m : ℕ) (η : ℝ) : ℕ := Nat.ceil (4 * (m : ℝ) * η * logBits (η + 2))

theorem slackBits_pos (k : ℕ) (g r : ℝ) (hg : 0 < g) (hr : 0 < r)
    (h : g < (2 : ℝ) ^ (k : ℝ) / (r * Real.exp 1)) :
    0 < slackBits k g r := by
  have hx : 0 < g * r * Real.exp 1 := by positivity
  have hpow : g * r * Real.exp 1 < (2 : ℝ) ^ (k : ℝ) := by
    have h' := (lt_div_iff₀ (show 0 < r * Real.exp 1 by positivity)).mp h
    nlinarith
  exact sub_pos.mpr ((Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hx).mpr hpow)

theorem etaBits_pos (δ : ℝ) (k : ℕ) (g r : ℝ) (hδ : 0 < δ)
    (hs : 0 < slackBits k g r) : 0 < etaBits δ k g r := by
  exact one_div_pos.mpr (mul_pos hδ hs)

theorem failureCount_card (T : ℕ) : Fintype.card (Fin (T + 1)) = T + 1 := Fintype.card_fin _

theorem support_log_distinction :
    logBits (Fintype.card (Fin (1 + 1))) = 1 ∧ logBits 1 = 0 := by
  norm_num [logBits, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Real.logb_one]

end
end Qatlib.Papers.CommutingLLL13.NativeFix
