/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Rational
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseGrid

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Full table construction with its actual Gaussian multiplication trace.
The table is built before candidate search. Later early success cannot remove
these events or their positive primitive charges.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Construction for table Loop in the table model. -/
def tableLoop (z : GaussianRat) : ℕ → GaussianRat → Run (List GaussianRat × ℕ)
  | 0,_ => pure ([],0)
  | 1,a => do
    let rows ← allocate a []
    pure (rows,0)
  | n+2,a => do
    let next ← gaussianMul a z
    let tail ← tableLoop z (n+1) next
    let rows ← allocate a tail.1
    pure (rows,tail.2+1)

/-- The traced table loop returns the exact original rows and multiplication counter. -/
@[simp] theorem tableLoop_value (z : GaussianRat) (n : ℕ) (a : GaussianRat) :
    (tableLoop z n a).value = phaseTableLoop z n a := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => simp [tableLoop, phaseTableLoop]
    | succ n =>
      cases n with
      | zero => simp [tableLoop, phaseTableLoop]
      | succ n => simp [tableLoop, phaseTableLoop, ih (n+1) (by omega)]

/-- Construction for table in the table model. -/
def table (z : GaussianRat) (n : ℕ) : Run (List GaussianRat × ℕ) := tableLoop z n gone

/-- Traced table construction preserves the exact pinned phase-table convention. -/
@[simp] theorem table_value (z : GaussianRat) (n : ℕ) :
    (table z n).value = phaseTable z n := by simp [table, phaseTable]

/-- Every nontrivial table step emits six rational operations and one list cell. -/
theorem tableLoop_step_events (z a : GaussianRat) (n : ℕ) :
    (tableLoop z (n+2) a).events.length =
      6 + (tableLoop z (n+1) (gmul a z)).events.length + 1 := by
  simp [tableLoop, gaussianMul_events_length, allocate, emit, Nat.add_assoc]

/-- The complete table trace retains all six rational operations of each multiply. -/
theorem tableLoop_events_lower (z : GaussianRat) (n : ℕ) (a : GaussianRat) :
    6*(n-1) ≤ (tableLoop z n a).events.length := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        have ht := ih (n+1) (by omega) (gmul a z)
        rw [tableLoop_step_events]
        omega

/-- Positive primitive pricing pays every actual table multiplication, before search. -/
theorem table_charge_lower (model : PriceModel) (z : GaussianRat) (n : ℕ) :
    6*(n-1) ≤ charge model (table z n).events :=
  (tableLoop_events_lower z n gone).trans (length_le_charge model _)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
