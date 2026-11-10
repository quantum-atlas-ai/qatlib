/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Filter
namespace Qatlib.Papers.DecisionTrees97.MainResults

theorem exact_agreement_transfers_time_witness
    (a af : ℕ → ℝ → ℝ) (A B A0 : ℝ) (hAA0 : A ≤ A0)
    (hev : ∀ᶠ n : ℕ in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t < (n : ℝ) ^ A ∧ (1 / (n : ℝ)) ^ B < a n t)
    (hagree : ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, 0 ≤ t → t < (n : ℝ) ^ A0 → af n t = a n t) :
    ∀ᶠ n : ℕ in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t < (n : ℝ) ^ A0 ∧ (1 / (n : ℝ)) ^ B < af n t := by
  filter_upwards [hev, hagree, eventually_ge_atTop (1 : ℕ)] with n hn hg hn1
  obtain ⟨t, ht0, htA, hlt⟩ := hn
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have htA0 : t < (n : ℝ) ^ A0 :=
    lt_of_lt_of_le htA (Real.rpow_le_rpow_of_exponent_le hn1R hAA0)
  refine ⟨t, ht0, htA0, ?_⟩
  rw [hg t ht0 htA0]
  exact hlt

end Qatlib.Papers.DecisionTrees97.MainResults
