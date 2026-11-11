/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Source QFT semantics and the omitted Hadamard count

In quant-ph/9508027v2, printed p.14, Eq. (4.4) explicitly contains one
Hadamard per wire, but the following total `l(l-1)/2` counts only controlled
phases. The installed local word also performs the optional final bit reversal.
Its matrix and its counts below concern the same actual local gate list.
The one-wire counterexample preserves and refutes the printed *total* count;
the quadratic asymptotic construction is unaffected.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShorFactoring97.QftCircuit

open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.SpectralFilter.PhaseReadout

/-- The actual source-sign local word, with final bit reversal, is the QFT. -/
theorem source_qft_matrix (l : ℕ) :
    localProgramMatrix (localQFT l) =
      relabelGate (bitVecEquiv l).symm (QFTMatrix (2 ^ l)) :=
  (localQFT_exact_positive_matrix l).1

/-- The same local word charges all Hadamards, controlled phases and swaps. -/
theorem source_qft_total_gates (l : ℕ) :
    GateCount (localProgramCircuit (localQFT l)) =
      l + l * (l - 1) / 2 + l / 2 :=
  (localQFT_exact_gate_counts_and_wires l).2.2.2.1

/-- The printed count is exactly the controlled-phase count, not the total. -/
theorem source_qft_phase_gates (l : ℕ) :
    ((localQFT l).filter (fun g => match g with
      | .cp _ _ _ _ => true | _ => false)).length = l * (l - 1) / 2 :=
  (localQFT_exact_gate_counts_and_wires l).2.1

/-- At one wire the source word has one Hadamard while the printed total is zero. -/
theorem printed_total_one_wire_counterexample :
    GateCount (localProgramCircuit (localQFT 1)) = 1 ∧
    GateCount (localProgramCircuit (localQFT 1)) ≠ 1 * (1 - 1) / 2 := by
  rw [source_qft_total_gates]
  norm_num

/-- Counting the omitted gates still gives a quadratic bound at positive width. -/
theorem source_qft_quadratic (l : ℕ) (hl : 1 ≤ l) :
    GateCount (localProgramCircuit (localQFT l)) ≤ 2 * l ^ 2 := by
  rw [source_qft_total_gates]
  have hphase : l * (l - 1) / 2 ≤ l * (l - 1) := Nat.div_le_self _ _
  have hswap : l / 2 ≤ l := Nat.div_le_self _ _
  have hsub : l - 1 + 1 = l := by omega
  nlinarith

end Qatlib.Papers.ShorFactoring97.QftCircuit
