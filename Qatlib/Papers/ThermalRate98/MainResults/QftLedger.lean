/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.PhysicalSplitOperator
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults

def qftOpCount (ν : ℕ) : ℕ := ν * (ν - 1) / 2

def classicalFftCount (ν : ℕ) : ℕ := ν * 2 ^ ν

theorem qftOpCount_le_square (ν : ℕ) : qftOpCount ν ≤ ν * ν := by
  unfold qftOpCount
  calc ν * (ν - 1) / 2 ≤ ν * ν / 2 :=
        Nat.div_le_div_right (Nat.mul_le_mul_left ν (Nat.sub_le ν 1))
    _ ≤ ν * ν := Nat.div_le_self _ _

theorem qftOpCount_lt_classical (ν : ℕ) (hν : 0 < ν) :
    qftOpCount ν < classicalFftCount ν := by
  have h1 : qftOpCount ν ≤ ν * ν := qftOpCount_le_square ν
  have h2 : ν < 2 ^ ν := Nat.lt_two_pow_self
  have h3 : ν * ν < ν * 2 ^ ν := Nat.mul_lt_mul_of_pos_left h2 hν
  exact lt_of_le_of_lt h1 h3

theorem qftOpCount_le_classical (ν : ℕ) : qftOpCount ν ≤ classicalFftCount ν := by
  rcases Nat.eq_zero_or_pos ν with hν | hν
  · subst hν
    simp [qftOpCount, classicalFftCount]
  · exact le_of_lt (qftOpCount_lt_classical ν hν)

theorem classicalFftCount_ge_pow (ν : ℕ) (hν : 0 < ν) :
    2 ^ ν ≤ classicalFftCount ν := by
  unfold classicalFftCount
  exact Nat.le_mul_of_pos_left (2 ^ ν) hν

end Qatlib.Papers.ThermalRate98.MainResults
