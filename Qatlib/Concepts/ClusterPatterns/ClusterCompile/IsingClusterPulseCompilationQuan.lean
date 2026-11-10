/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.ClusterCompile.IsingClusterPulseCompilationStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.ClusterPatterns.ClusterCompile
open Qatlib

theorem isingClusterPulseCompilation : IsingClusterPulseCompilation := by
  classical
  intro n edges _
  have hU : sourcePulse edges ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    rw [sourcePulse_eq_frame_cz]
    exact (Matrix.unitaryGroup (Reg n) ℂ).mul_mem
      (frameMatrix_unitary edges) (czMatrix_unitary edges)
  refine ⟨sourcePulse_eq_frame_cz edges, hU, ?_, ?_, ?_, ?_⟩
  · apply (isUnitaryCircuit_append _ _).mpr
    exact ⟨unitary_gateList _ _ (fun e => networkCzGateB_unitary e.1 e.2),
      unitary_gateList _ _ localZ_unitary⟩
  · rw [compiledPulseWord, queryCount_append]
    simp only [czWord, frameWord, queryCount_gateList, Nat.add_zero]
  · rw [compiledPulseWord, gateCount_append]
    simp only [czWord, frameWord, gateCount_gateList, Finset.length_toList]
  · intro ψ
    rw [compiledPulseWord, run_append, run_czWord, run_frameWord,
      ← applyGate_mul, sourcePulse_eq_frame_cz]

end Qatlib.Concepts.ClusterPatterns.ClusterCompile
