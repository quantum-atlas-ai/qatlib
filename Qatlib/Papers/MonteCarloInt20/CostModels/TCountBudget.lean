/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

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
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MonteCarloInt20.CostModels.Reported

def tcountSelfUpdate (n_prn : ℕ) : ℕ := 140 * n_prn ^ 2

def tcountConversion (n_dig n_icdf : ℕ) : ℕ := 105 * n_dig ^ 2 + 28 * n_dig * n_icdf

def tcountJump (n_samp n_obl n_prn : ℕ) : ℕ := 140 * (n_samp + n_obl) * n_prn ^ 2

def tcountPrev (n_prn n_dig n_icdf : ℕ) : ℕ :=
  tcountSelfUpdate n_prn + 2 * tcountConversion n_dig n_icdf

def tcountNew (n_samp n_obl n_prn n_dig n_icdf : ℕ) : ℕ :=
  2 * tcountJump n_samp n_obl n_prn + 2 * tcountConversion n_dig n_icdf

theorem tcount_prev_eq (n_prn n_dig n_icdf : ℕ) :
    tcountPrev n_prn n_dig n_icdf =
      140 * n_prn ^ 2 + 210 * n_dig ^ 2 + 56 * n_dig * n_icdf := by
  unfold tcountPrev tcountSelfUpdate tcountConversion
  ring

theorem tcount_new_eq (n_samp n_obl n_prn n_dig n_icdf : ℕ) :
    tcountNew n_samp n_obl n_prn n_dig n_icdf =
      280 * (n_samp + n_obl) * n_prn ^ 2 + 210 * n_dig ^ 2 + 56 * n_dig * n_icdf := by
  unfold tcountNew tcountJump tcountConversion
  ring

def tcountPrevTypical : ℕ := tcountPrev 64 16 109

def tcountNewTypical : ℕ := tcountNew 20 20 64 16 109

theorem tcount_prev_typical : tcountPrevTypical = 724864 := by
  unfold tcountPrevTypical tcountPrev tcountSelfUpdate tcountConversion
  norm_num

theorem tcount_new_typical : tcountNewTypical = 46026624 := by
  unfold tcountNewTypical tcountNew tcountJump tcountConversion
  norm_num

theorem tcount_prev_typical_magnitude :
    (710000 : ℝ) < (tcountPrevTypical : ℝ) ∧ (tcountPrevTypical : ℝ) < 730000 := by
  rw [tcount_prev_typical]; norm_num

theorem tcount_new_typical_magnitude :
    (46000000 : ℝ) < (tcountNewTypical : ℝ) ∧ (tcountNewTypical : ℝ) < 47000000 := by
  rw [tcount_new_typical]; norm_num

theorem perf_ratio_typical :
    (63 : ℚ) < (tcountNewTypical : ℚ) / (tcountPrevTypical : ℚ) ∧
      (tcountNewTypical : ℚ) / (tcountPrevTypical : ℚ) < 64 := by
  rw [tcount_new_typical, tcount_prev_typical]
  norm_num

def totalRatio (l δrel D : ℝ) : ℝ := 64 * ((l * δrel)⁻¹ / D)

theorem total_ratio_beneficial_iff (l δrel D : ℝ) : totalRatio l δrel D < 1 ↔ (l * δrel)⁻¹ / D < 1 / 64 := by
  unfold totalRatio
  constructor <;> intro h <;> nlinarith

theorem total_ratio_typical :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) = 625 / 1024 := by
  unfold totalRatio
  norm_num

theorem total_ratio_typical_lt_one :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) < 1 := by
  rw [total_ratio_typical]; norm_num

theorem total_ratio_typical_le_064 :
    totalRatio (1 / 100) (1 / 100) (2 ^ 20 : ℝ) ≤ 0.64 := by
  rw [total_ratio_typical]; norm_num

end Qatlib.Papers.MonteCarloInt20.CostModels.Reported
