/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Ring
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Asymptotic composition of primality-test costs

The two theorems multiply an assumed logarithmic iteration bound by an assumed per-iteration
cost bound. They give the total operation bounds for the standard and faster multiplication cost
models as direct statements of asymptotic big-O composition [DonisVelaGarciaEscartin2017].

## Main statements

* `operation_count_bigO`: Logarithmic iterations and O(log n · n³) cost give O((log n)² · n³).
* `operation_count_bigO_fast`: The faster cost model gives O(log log n · (log n)³ · n²).

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option autoImplicit false
open Asymptotics Filter
namespace Qatlib.Papers.PrimalityOrd17.MainResults

/-- An `O(log n)` iteration bound multiplied by an `O(log n * n³)` per-iteration cost gives
total cost `O((log n)² * n³)` [DonisVelaGarciaEscartin2017]. -/
theorem operation_count_bigO
    (iter cost : ℕ → ℝ)
    (hiter : IsBigO atTop iter (fun n : ℕ => Real.log n))
    (hcost : IsBigO atTop cost (fun n : ℕ => Real.log n * (n : ℝ) ^ 3)) :
    IsBigO atTop (fun n : ℕ => iter n * cost n)
      (fun n : ℕ => (Real.log n) ^ 2 * (n : ℝ) ^ 3) := by
  have h := hiter.mul hcost
  simpa only [pow_two, mul_assoc] using h

/-- An `O(log n)` iteration bound multiplied by an `O(log log n * (log n)² * n²)` per-iteration
cost gives total cost `O(log log n * (log n)³ * n²)` [DonisVelaGarciaEscartin2017]. -/
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
