/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DihedralHSP13.MainResults.MachineModel.SourceMachineEquivalence
public import Qatlib.Papers.DihedralHSP13.MainResults.MachineModel.SourceLinearAccessSimulation

@[expose] public section

/-!
# Instruction semantics and time for the linear scan

In the classical-cell case of Proposition 2.2 in arXiv:1112.3333v1,
a finite scan conditionally adds each cell to the answer. This file checks
the scan after translation into the pinned instruction-charge model.
-/

set_option autoImplicit false

open Qatlib.Papers.DihedralHSP13.MainResults.MachineModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.DihedralHSP13.MainResults

/-- The same compiled scan reads every address coherently on basis kets and incurs
exactly one charged instruction per memory cell. -/
theorem compiled_scan_read_time {I : Type*} [Fintype I] [DecidableEq I]
    (mem : I → ZMod 2) (a : I) (b : ZMod 2) :
    runProgram (compileCircuit 1 (scanCircuit mem)) (Ket (a, b)) = Ket (a, b + mem a) ∧
    programTime (compileCircuit 1 (scanCircuit mem)) = instrCost * Fintype.card I := by
  obtain ⟨hrun, hgates, hqueries⟩ := prop22_scan_implements_qram mem a b
  exact ⟨(prop21_compiled_program_runs 1 (scanCircuit mem) (Ket (a, b))).trans hrun,
    (prop21_oracleFree_time (scanCircuit mem) hqueries).trans (congrArg (instrCost * ·) hgates)⟩

end Qatlib.Papers.DihedralHSP13.MainResults
