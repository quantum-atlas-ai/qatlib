/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor

set_option autoImplicit false
namespace Qatlib.Foundations.IntervalArith.IntervalOps

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Valid (a : Interval) : Prop := a.lo ≤ a.hi
instance (a : Interval) : Decidable (Valid a) := inferInstanceAs (Decidable (a.lo ≤ a.hi))
def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)
def width (a : Interval) : ℚ := a.hi-a.lo
def radius (a : Interval) : ℚ := max |a.lo| |a.hi|
def unit (k : ℕ) : ℚ := 1/(2:ℚ)^k
def roundDown (q : ℚ) (k : ℕ) : ℚ := (⌊q*(2:ℚ)^k⌋ : ℤ)/(2:ℚ)^k
def rounded (q : ℚ) (k : ℕ) : Interval := ⟨roundDown q k, roundDown q k+unit k⟩
def add (a b : Interval) : Interval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def divPositive (a b : Interval) (gap : ℚ) : Option Interval :=
  if 0 < gap ∧ gap ≤ b.lo ∧ Valid a ∧ Valid b then some (mul a ⟨1/b.hi,1/b.lo⟩) else none

end Qatlib.Foundations.IntervalArith.IntervalOps
