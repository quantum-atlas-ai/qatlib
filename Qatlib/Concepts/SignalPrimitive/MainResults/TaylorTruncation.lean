/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation

/-!
# Tolerance Range for a Taylor Degree Budget

This module checks the tolerance dependence of a Taylor truncation budget used in Hamiltonian
simulation, whose broader setting is described in [LowChuang2019]. `Theorem1TaylorTruncationV1`
records a candidate bound with `log (8 / ε)` for every positive `ε`; at zero time and `ε = 8 *
exp 2`, that degree budget equals `-8`.

`not_theorem1TaylorTruncation` therefore refutes this unrestricted formulation.
`zero_time_taylor_truncation` proves the zero-time case for `0 < ε ≤ 8` using degree one, while
the corrected general contract `Theorem1TaylorTruncation` is stated in a separate module.

## Main statements

- `taylor_degree_budget_negative` evaluates the counterexample budget.
- `not_theorem1TaylorTruncation` disproves the unrestricted candidate contract.
- `zero_time_taylor_truncation` gives a valid zero-time witness in the stated tolerance range.

## References

- [Low and Chuang, 2019][LowChuang2019].
-/

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib

namespace Qatlib.Concepts.SignalPrimitive.MainResults
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
/-- The candidate Taylor cutoff contract with degree budget `4 * |τ| + 8 * log (8 / ε) + 8` for
every positive `ε`. This unrestricted formulation is refuted by
`not_theorem1TaylorTruncation`. -/
def Theorem1TaylorTruncationV1 : Prop :=
  ∀ (τ ε : ℝ), 0 < ε → ∃ n : ℕ,
    2 * |τ| ≤ (n : ℝ) + 1 ∧
    Qatlib.Concepts.QspSimulation.Achievability.exponentialTaylorError τ n ≤ ε ∧
    (n : ℝ) ≤ 4 * |τ| + 8 * Real.log (8 / ε) + 8

/-- At `τ = 0` and `ε = 8 * exp 2`, the candidate Taylor degree budget evaluates to `-8`. -/
theorem taylor_degree_budget_negative :
    4 * |(0 : ℝ)| + 8 * Real.log (8 / (8 * Real.exp 2)) + 8 = -8 := by
  have hratio : (8 : ℝ) / (8 * Real.exp 2) = (Real.exp 2)⁻¹ := by
    field_simp
  rw [hratio, Real.log_inv, Real.log_exp]
  norm_num

/-- Refutes `Theorem1TaylorTruncationV1` because its zero-time degree budget is negative at the
positive tolerance `8 * exp 2`. -/
theorem not_theorem1TaylorTruncation : ¬ Theorem1TaylorTruncationV1 := by
  intro h
  obtain ⟨n, _, _, hdegree⟩ := h 0 (8 * Real.exp 2) (by positivity)
  rw [taylor_degree_budget_negative] at hdegree
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- For `0 < ε ≤ 8`, degree one satisfies the zero-time cutoff, Taylor error, and original
logarithmic degree budget. -/
theorem zero_time_taylor_truncation {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 8) :
    ∃ n : ℕ,
      2 * |(0 : ℝ)| ≤ (n : ℝ) + 1 ∧
      exponentialTaylorError 0 n ≤ ε ∧
      (n : ℝ) ≤ 4 * |(0 : ℝ)| + 8 * Real.log (8 / ε) + 8 := by
  have hlog : 0 ≤ Real.log (8 / ε) :=
    Real.log_nonneg ((one_le_div hε).2 hε8)
  refine ⟨1, ?_, ?_, ?_⟩
  · norm_num
  · simpa [exponentialTaylorError] using hε.le
  · norm_num
    linarith

end Qatlib.Concepts.SignalPrimitive.MainResults
