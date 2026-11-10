/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix
open scoped Matrix.Norms.L2Operator

theorem evaluate_operator_error_le_queries {H : Type*} [Fintype H] [DecidableEq H]
    (cs : List (AdjointStep H)) (U V : Matrix H H ℂ) (δ : ℝ)
    (hcs : WellFormedAdjointCircuit cs) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) (hδ : 0 ≤ δ) (hVU : ‖V-U‖ ≤ δ) :
    ‖evaluate V cs - evaluate U cs‖ ≤ (adjointQueryCount cs : ℝ) * δ := by
  induction cs with
  | nil => simp [evaluate, adjointQueryCount]
  | cons c cs ih =>
    have ht := ((WellFormedAdjointCircuit.cons_iff c cs).mp hcs).2
    have hi := ih ht
    have htail := l2_norm_unitary_le_one (ht.evaluate_unitary hV)
    have hstep := l2_norm_mul_sub_mul_le (instructionMatrix V c) (evaluate V cs)
      (instructionMatrix U c) (evaluate U cs)
    cases c with
    | gate A =>
      have hA := hcs A (by simp)
      have hnA := l2_norm_unitary_le_one hA
      simpa [evaluate, instructionMatrix, adjointQueryCount] using
        hstep.trans (by
          simp only [instructionMatrix, sub_self, norm_zero, zero_mul, zero_add]
          exact (mul_le_mul_of_nonneg_right hnA (norm_nonneg _)).trans (by simpa using hi))
    | forward =>
      simp only [evaluate, instructionMatrix, adjointQueryCount, Nat.cast_add,
        Nat.cast_one] at hstep ⊢
      have hleft := mul_le_mul hVU htail (norm_nonneg _) hδ
      have hright := mul_le_mul_of_nonneg_right (l2_norm_unitary_le_one hU)
        (norm_nonneg (evaluate V cs - evaluate U cs))
      nlinarith
    | backward =>
      have hdiff : ‖Vᴴ - Uᴴ‖ ≤ δ := by
        rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
        exact hVU
      simp only [evaluate, instructionMatrix, adjointQueryCount, Nat.cast_add,
        Nat.cast_one] at hstep ⊢
      have hleft := mul_le_mul hdiff htail (norm_nonneg _) hδ
      have hright := mul_le_mul_of_nonneg_right
        (l2_norm_unitary_le_one (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hU))
        (norm_nonneg (evaluate V cs - evaluate U cs))
      nlinarith

end Qatlib.Concepts.QspSimulation.Achievability
