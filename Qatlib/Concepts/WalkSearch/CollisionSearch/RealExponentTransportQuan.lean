/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.CollisionSearch.RealExponentTransportStat
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Positivity

/-!
# Real-exponent transport for collision costs

`collision_power_transport` bounds a natural-number quotient and exponent by their real-valued
counterparts when `1 ≤ r ≤ n`. The module uses this inequality to prove `RealExponentTransport`
for the charges supplied by a `KCollisionSolver`. See [Ambainis2005] for the mathematical
background.

## Main statements

* `collision_power_transport`: comparison of natural and real powers.
* `realExponentTransport_answer`: the real-exponent cost proposition.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.CollisionSearch

/-- For `1 ≤ r ≤ n`, the real cast of the natural power `(n / r) ^ (k / 2)` is at most the real
power `((n : ℝ) / r) ^ ((k : ℝ) / 2)`. -/
theorem collision_power_transport (n k r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    (((n / r) ^ (k / 2) : ℕ) : ℝ) ≤ ((n : ℝ) / r) ^ ((k : ℝ) / 2) := by
  have hquot : 1 ≤ n / r := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mpr (by simpa)
  have hbase : (1 : ℝ) ≤ (n : ℝ) / r := by
    exact_mod_cast (show (((1 : ℕ) : ℝ) ≤ (n : ℝ) / r) from
      (Nat.cast_le.mpr hquot).trans Nat.cast_div_le)
  calc
    (((n / r) ^ (k / 2) : ℕ) : ℝ) = (((n / r : ℕ) : ℝ) ^ ((k / 2 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast, Nat.cast_pow]
    _ ≤ ((n : ℝ) / r) ^ ((k / 2 : ℕ) : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (Nat.cast_nonneg _)
    _ ≤ ((n : ℝ) / r) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hbase Nat.cast_div_le

/-- Establishes the real-exponent cost bound for a supplied collision solver in
`RealExponentTransport`. -/
theorem realExponentTransport_answer : RealExponentTransport := by
  intro kcs _hκ n k r s u c R ρ hr hrn
  have hcost := kcs.charges r R s u c ρ
  have hcast : (kcs.cost r R s u c ρ : ℝ) ≤
      (kcs.κ : ℝ) * ((Nat.log 2 (n + 1) + 2 : ℕ) : ℝ) *
        ((s : ℝ) + (((n / r) ^ (k / 2) : ℕ) : ℝ) *
          ((c : ℝ) + (Nat.sqrt r : ℝ) * (u : ℝ))) := by
    exact_mod_cast hcost
  have hterm :
      (((n / r) ^ (k / 2) : ℕ) : ℝ) * ((c : ℝ) + (Nat.sqrt r : ℝ) * u) ≤
        ((n : ℝ) / r) ^ ((k : ℝ) / 2) * ((c : ℝ) + (Nat.sqrt r : ℝ) * u) :=
    mul_le_mul_of_nonneg_right (collision_power_transport n k r hr hrn) (by positivity)
  exact hcast.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm)
    (by positivity))

end Qatlib.Concepts.WalkSearch.CollisionSearch
