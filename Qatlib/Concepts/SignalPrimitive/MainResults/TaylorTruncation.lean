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
def Theorem1TaylorTruncationV1 : Prop :=
  ∀ (τ ε : ℝ), 0 < ε → ∃ n : ℕ,
    2 * |τ| ≤ (n : ℝ) + 1 ∧
    Qatlib.Concepts.QspSimulation.Achievability.exponentialTaylorError τ n ≤ ε ∧
    (n : ℝ) ≤ 4 * |τ| + 8 * Real.log (8 / ε) + 8

theorem taylor_degree_budget_negative :
    4 * |(0 : ℝ)| + 8 * Real.log (8 / (8 * Real.exp 2)) + 8 = -8 := by
  have hratio : (8 : ℝ) / (8 * Real.exp 2) = (Real.exp 2)⁻¹ := by
    field_simp
  rw [hratio, Real.log_inv, Real.log_exp]
  norm_num

theorem not_theorem1TaylorTruncation : ¬ Theorem1TaylorTruncationV1 := by
  intro h
  obtain ⟨n, _, _, hdegree⟩ := h 0 (8 * Real.exp 2) (by positivity)
  rw [taylor_degree_budget_negative] at hdegree
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

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
