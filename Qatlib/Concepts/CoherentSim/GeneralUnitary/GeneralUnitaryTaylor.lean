/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.CoherentSim.GeneralUnitary
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

theorem general_unitary_taylor_actual_segment_encoding :
    ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
      (h : J → ℝ) (U : J → Matrix I I ℂ) (j₀ : J) (τ : ℝ) (K : ℕ),
      (∀ j, U j ∈ Matrix.unitaryGroup I ℂ) → (∑ j, |h j|)*|τ| ≤ 1/2 →
      BlockEncoding (hamiltonianEvolution (∑ j, (h j : ℂ) • U j) τ)
        (evaluate (taylorQuery U K) (taylorLCUWord h j₀ τ K))
        (taylorFrame j₀ K) (taylorFrame j₀ K) 2 (2/((K+1).factorial : ℝ)) := by
  intro J I _ _ _ _ h U j₀ τ K hU hsmall
  have hb := (taylor_lcu_actual_prepare_select_and_counts (I := I) h j₀ τ K hsmall).2.1
  refine ⟨hb.evaluate_unitary (taylorQuery_unitary U hU K),
    taylorFrame_isIsometry j₀ K, taylorFrame_isIsometry j₀ K,
    by norm_num, by positivity, ?_⟩
  rw [taylor_actual_lcu_corner_polynomial h U j₀ τ K hU hsmall,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  norm_num
  rw [norm_sub_rev]
  exact factorialTaylor_matrix_remainder_of_unitary h U τ K hU hsmall

end Qatlib.Concepts.CoherentSim.GeneralUnitary
