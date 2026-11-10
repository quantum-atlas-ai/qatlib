/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic

set_option autoImplicit false
open Asymptotics Filter
namespace Qatlib.Papers.PrimalityOrd17.MainResults

theorem operation_count_bigO
    (iter cost : ℕ → ℝ)
    (hiter : IsBigO atTop iter (fun n : ℕ => Real.log n))
    (hcost : IsBigO atTop cost (fun n : ℕ => Real.log n * (n : ℝ) ^ 3)) :
    IsBigO atTop (fun n : ℕ => iter n * cost n)
      (fun n : ℕ => (Real.log n) ^ 2 * (n : ℝ) ^ 3) := by
  have h := hiter.mul hcost
  simpa only [pow_two, mul_assoc] using h

theorem operation_count_bigO_fast
    (iter cost : ℕ → ℝ)
    (hiter : IsBigO atTop iter (fun n : ℕ => Real.log n))
    (hcost : IsBigO atTop cost
      (fun n : ℕ => Real.log (Real.log n) * (Real.log n) ^ 2 * (n : ℝ) ^ 2)) :
    IsBigO atTop (fun n : ℕ => iter n * cost n)
      (fun n : ℕ => Real.log (Real.log n) * (Real.log n) ^ 3 * (n : ℝ) ^ 2) := by
  have h := hiter.mul hcost
  simpa only [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using h

end Qatlib.Papers.PrimalityOrd17.MainResults
