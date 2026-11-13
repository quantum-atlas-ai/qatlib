/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.NumericalCopyQPE

/-!
# Numerical copy coherence and controlled qubit swaps

This module specializes numerical copy and controlled-swap constructions to explicit coherence
and basis-state calculations. The theorem `numerical_copy_coherence_and_qubit_swap_consumers`
records the scalar copy phase, the length-40 qubit swap program, and its precision-dependent
vector error.

The copy-evolution setting is motivated by density-matrix simulation
[LloydMohseniRebentrost2014]; the result here retains the phase `-i` in the controlled-swap
output.

## Main statements

* `numerical_copy_coherence_and_qubit_swap_consumers`: scalar coherence, program length, and
  basis-state swap error.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Computes the off-diagonal coherence of the scalar numerical copy step and shows that the
qubit controlled-swap program has length 40. On each specified basis input, its output is
within `2 * (2⁻¹)^k` of the swapped state with phase `-i`. -/
theorem numerical_copy_coherence_and_qubit_swap_consumers : ∀ b k : ℕ,
  numericCopyRawStep 0 (1 : Operator 1) b k (fun _ _ => (1/2:ℂ))
    (false,(0:Fin 1)) (true,(0:Fin 1)) = gaussianRatComplex (copyPhaseData b k)/2 ∧
  (numericControlledSwapSteps 1 1 k).length = 40 ∧
  (∀ i j : Fin 2, ‖toEuclidean_fromVec
    (reflectionProgramMatrix (numericControlledSwapSteps 1 1 k) *ᵥ
        (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(i,j))) -
      (-Complex.I) • (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(j,i))))‖ ≤ 2*((2:ℝ)⁻¹)^k) := by
  intro b k
  have h := local_copy_global_phase_and_qubit_swap_consumers
  refine ⟨?_,by simpa using! (numerical_controlled_swap_clean_and_error 1 1 k).2.1,?_⟩
  · rw [numericCopyRawStep_eq,← localControlledCopyRawMap_eq 0 _ (copyPhaseEffectiveAngle b k)]
    rw [h.1]
    rw [(copy_dyadic_actual_phase_data b k).2.2.1,mul_comm Complex.I]
  · intro i j
    let v := localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(i,j))
    have hn : ‖toEuclidean_fromVec v‖ = 1 := by
      rw [isometry_mulVec_norm (localCopyFrame_isometry 1)]
      exact (normalized_iff_stateVector_norm (Qatlib.Foundations.PureStateMath.Ket (true,(i,j)))).mp (normalized_ket _)
    have hs : reflectionProgramMatrix (fastControlledSwapSteps 1 (Real.pi/(2^1:ℕ))) *ᵥ v =
        (-Complex.I) • (localCopyFrame 1 *ᵥ Qatlib.Foundations.PureStateMath.Ket (true,(j,i))) := by
      rw [fastControlledSwap_matrix]
      simpa only [v,Nat.pow_one,Nat.cast_ofNat] using! h.2.1 i j
    rw [← hs,← Matrix.sub_mulVec]
    have he := l2_norm_mulVec_fromVec_le
      (reflectionProgramMatrix (numericControlledSwapSteps 1 1 k)-
        reflectionProgramMatrix (fastControlledSwapSteps 1 (Real.pi/(2^1:ℕ)))) v
    simp only [hn,mul_one] at he
    exact he.trans (numerical_controlled_swap_clean_and_error 1 1 k).2.2.2.2

end Qatlib.Concepts.TrotterFormula.GeneralOrder
