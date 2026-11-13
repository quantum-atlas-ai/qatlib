/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorConsumers

/-!
# Taylor encodings for general unitary summands

`general_unitary_taylor_actual_segment_encoding` constructs a scale-two encoding of the matrix
exponential for a real linear combination of unitary summands. Its factorial remainder bound
requires a small segment but does not require each summand to be Hermitian, extending the Taylor
encoding construction of [BerryEtAl2015Taylor].

## Main statements

* `general_unitary_taylor_actual_segment_encoding`: A scale-two block encoding with factorial
  truncation error.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

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

/-- For unitary summands and coefficient mass times segment duration at most `1 / 2`, the
evaluated Taylor word block-encodes the evolution at scale two with error `2 / (K + 1)!`.
See [BerryEtAl2015Taylor]. -/
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
