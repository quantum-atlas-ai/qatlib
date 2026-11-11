/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Logarithmic label width and assigned resource budgets

The quantity `qubitCount d` is the base-two ceiling logarithm needed to label `d` states. This
module proves its capacity and real-logarithm bounds and combines them with an assigned
quadratic time budget. The statements formalize scalar and register-width estimates appearing in
the resource discussion of [LloydEtAl2020].

## Main statements

* `dim_le_two_pow_qubitCount`: The capacity of the register with `qubitCount d` qubits is at
  least `d`.
* `qubitCount_log_bound`: For positive `d`, the qubit count is strictly less than the real
  base-two logarithm of `d` plus one.
* `assigned_label_constant`: For positive energy scale, tolerance, and dimension, combine the
  assigned logarithmic label budget bound with the dimension and width capacity inequalities.

## References

* [Lloyd et al., 2020][LloydEtAl2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinearDE20.Resources.LabelWidth

/-- The base-two natural ceiling logarithm of the state-space dimension `d`. -/
def qubitCount (d : ℕ) : ℕ := Nat.clog 2 d

/-- The capacity of the register with `qubitCount d` qubits is at least `d`. -/
theorem dim_le_two_pow_qubitCount (d : ℕ) : d ≤ 2 ^ qubitCount d := by
  exact (Nat.clog_le_iff_le_pow (b := 2) (by norm_num : 1 < 2) (x := d)
    (y := Nat.clog 2 d)).mp le_rfl

/-- For positive `d`, the qubit count is strictly less than the real base-two logarithm of `d`
plus one [LloydEtAl2020]. -/
theorem qubitCount_log_bound (d : ℕ) (hd : 0 < d) :
    (qubitCount d : ℝ) < Real.logb 2 (d : ℝ) + 1 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hd : 1 ≤ d)
  have h := Nat.ceil_lt_add_one
    (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hd1)
  show (Nat.clog 2 d : ℝ) < Real.logb 2 (d : ℝ) + 1
  rw [← Real.natCeil_logb_natCast]
  exact h

/-- The assigned scalar budget `E2 * t^2 / ε` factors as `(E2 / ε) * t^2`. -/
theorem assigned_budget_factorization (E2 ε t : ℝ) :
    E2 * t ^ 2 / ε = (E2 / ε) * t ^ 2 := by
  ring

/-- For positive energy scale, tolerance, and dimension, the assigned budget times qubit count
is bounded by the corresponding real-logarithm expression. -/
theorem assigned_label_budget_bound (E2 ε : ℝ) (hE2 : 0 < E2) (hε : 0 < ε)
    (t : ℝ) (d : ℕ) (hd : 0 < d) :
    (E2 * t ^ 2 / ε) * (qubitCount d : ℝ)
      ≤ (E2 / ε) * t ^ 2 * (Real.logb 2 (d : ℝ) + 1) := by
  have hq := qubitCount_log_bound d hd
  have hc : 0 ≤ (E2 / ε) * t ^ 2 := by positivity
  have h1 : E2 * t ^ 2 / ε = (E2 / ε) * t ^ 2 := by ring
  rw [h1]
  exact mul_le_mul_of_nonneg_left hq.le hc

/-- The label width is strictly less than the capacity of its qubit register. -/
theorem label_width_lt_capacity (d : ℕ) :
    qubitCount d < 2 ^ qubitCount d := by
  have h := Nat.lt_two_pow_self (n := qubitCount d)
  exact h

/-- For positive energy scale, tolerance, and dimension, combine the assigned logarithmic label
budget bound with the dimension and width capacity inequalities. -/
theorem assigned_label_constant (E2 ε : ℝ) (hE2 : 0 < E2) (hε : 0 < ε)
    (t : ℝ) (d : ℕ) (hd : 0 < d) :
    ((E2 * t ^ 2 / ε) * (qubitCount d : ℝ)
        ≤ (E2 / ε) * t ^ 2 * (Real.logb 2 (d : ℝ) + 1))
      ∧ d ≤ 2 ^ qubitCount d
      ∧ qubitCount d < 2 ^ qubitCount d :=
  ⟨assigned_label_budget_bound E2 ε hE2 hε t d hd,
    dim_le_two_pow_qubitCount d, label_width_lt_capacity d⟩

end Qatlib.Papers.NonlinearDE20.Resources.LabelWidth
