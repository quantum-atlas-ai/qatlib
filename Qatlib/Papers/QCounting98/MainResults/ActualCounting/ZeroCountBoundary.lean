/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.FiniteTraceQueries
import Qatlib.Papers.QCounting98.MainResults.ActualCounting.StandardProgram
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QCounting98.MainResults.ActualCounting
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.StoppingCore.InterruptBridge
open scoped Classical BigOperators

def twoAddressMark (i : Fin 2) : Bool := decide (i = 0)

theorem zero_one_counts :
    (sourceMarked (fun _ : Fin 2 => false)).card = 0 ∧
    (sourceMarked twoAddressMark).card = 1 := by
  constructor
  · simp [sourceMarked]
  · have h : sourceMarked twoAddressMark = {0} := by
      ext i
      simp [sourceMarked,twoAddressMark]
    rw [h,Finset.card_singleton]

theorem zero_input_paid_lower {W H : Type} [Fintype W] [DecidableEq W] [Fintype H]
    (code : H → Circuit ((Fin 2 × Bool) × W))
    (psi : QState ((Fin 2 × Bool) × W)) (decode : H → ℕ)
    (htotal : (∑ h, finiteTraceMass (workspaceBitOracle twoAddressMark) code psi h) ≤ 1)
    (hzero : (3 : ℝ)/4 ≤ finiteTraceSuccess (workspaceBitOracle (fun _ : Fin 2 => false)) code psi decode 0)
    (hone : (3 : ℝ)/4 ≤ finiteTraceSuccess (workspaceBitOracle twoAddressMark) code psi decode 1) :
    (1 : ℝ)/2 ≤ finiteTraceExpected (workspaceBitOracle (fun _ : Fin 2 => false)) code psi := by
  have h := finite_trace_first_query_lower
    (workspaceBitOracle (fun _ : Fin 2 => false)) (workspaceBitOracle twoAddressMark)
    code psi decode 0 1 (by decide) ((3 : ℝ)/4) ((3 : ℝ)/4) htotal hzero hone
  linarith

theorem zero_count_multiplicative_bound_impossible {W H : Type}
    [Fintype W] [DecidableEq W] [Fintype H]
    (code : H → Circuit ((Fin 2 × Bool) × W))
    (psi : QState ((Fin 2 × Bool) × W)) (decode : H → ℕ) (K : ℝ)
    (htotal : (∑ h, finiteTraceMass (workspaceBitOracle twoAddressMark) code psi h) ≤ 1)
    (hzero : (3 : ℝ)/4 ≤ finiteTraceSuccess (workspaceBitOracle (fun _ : Fin 2 => false)) code psi decode 0)
    (hone : (3 : ℝ)/4 ≤ finiteTraceSuccess (workspaceBitOracle twoAddressMark) code psi decode 1) :
    ¬ finiteTraceExpected (workspaceBitOracle (fun _ : Fin 2 => false)) code psi ≤
      K*Real.sqrt (((sourceMarked (fun _ : Fin 2 => false)).card : ℝ)*2) := by
  have hpaid := zero_input_paid_lower code psi decode htotal hzero hone
  rw [zero_one_counts.1]
  norm_num
  linarith

end Qatlib.Papers.QCounting98.MainResults.ActualCounting
