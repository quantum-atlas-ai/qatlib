/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

set_option autoImplicit false
namespace Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.HadamardGram

def andPenalty (x y a : Bool) : ℝ :=
  3*bit a+bit x*bit y-2*bit x*bit a-2*bit y*bit a

def rowLinear (x y a : Bool) : ℝ := 1-2*bit x-2*bit y+4*bit a

theorem andPenalty_nonneg (x y a : Bool) : 0 ≤ andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit]

theorem andPenalty_wrong (x y a : Bool) (h : a ≠ (x && y)) :
    1 ≤ andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit] at *

theorem andPenalty_correct (x y : Bool) : andPenalty x y (x && y) = 0 := by
  cases x <;> cases y <;> norm_num [andPenalty,bit]

theorem andPenalty_zero_iff (x y a : Bool) : andPenalty x y a = 0 ↔ a = (x && y) := by
  cases x <;> cases y <;> cases a <;> norm_num [andPenalty,bit]

theorem rowLinear_correct (x y : Bool) : rowLinear x y (x && y) = spin x*spin y := by
  cases x <;> cases y <;> norm_num [rowLinear,spin,bit]

theorem rowLinear_square (x y a : Bool) :
    rowLinear x y a ^ 2 = 1+8*andPenalty x y a := by
  cases x <;> cases y <;> cases a <;> norm_num [rowLinear,andPenalty,bit]

end Qatlib.Foundations.BooleanEnergy.PenaltyExact
