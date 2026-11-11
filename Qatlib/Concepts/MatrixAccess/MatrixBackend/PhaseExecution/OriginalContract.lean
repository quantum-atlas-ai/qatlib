/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Program
import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Exact original output and actual quantum-word contracts at the traced return value.
The source is pinned Frozen c1e805dd1c0613aab235c19072353acc0208318e; no source
premise, phase convention, parity branch, failure behavior or original query/gate
ledger is replaced by a cost assumption. Arithmetic trace prices remain separate
from the independently preserved physical-word semantics. -/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.Execution.WorkspaceCP Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.WalkSearch.Spectral
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- Complete original frozen contract, using the packet returned by the same traced interpreter. -/
theorem traced_rational_phase_synthesis_terminates : ∀ (p : List ℚ) (d : ℕ) (eps : ℚ), 0<eps →
  (realTarget p).degree ≤ (d:WithBot ℕ) →
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) →
  let result := (produce p d eps).value
  let k := phaseToleranceBits eps
  let N := 2^phaseGridBits d k
  ∃ data : PhaseData, result.value=some data ∧ data.phases.length=d ∧
    ‖gaussianRatComplex data.base‖=1 ∧ (∀ z ∈ data.phases,‖gaussianRatComplex z‖=1) ∧
    (scoreData p d data).1.1 ≤ (1/2:ℚ)^k ∧
    (∀ x ∈ Set.Icc (-1:ℝ) 1,
      |((responseP (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re-
        (realTarget p).eval x| ≤ (eps:ℝ)) ∧
    1 ≤ result.tested ∧ result.tested ≤ 1+N^(d+1) ∧
    result.responseRounds=result.tested*d ∧ result.coefficientVisits=result.tested*(d+1) ∧
    (result.backendCalls=0 ∧ result.tableMultiplications=0 ∨
      result.backendCalls=1 ∧ result.tableMultiplications=N-1) := by
  simpa only [produce_value] using finite_rational_phase_synthesis_terminates

/-- Complete original frozen contract, using the packet returned by the same traced interpreter. -/
theorem traced_phase_word_actual_matrix_transform : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ),
  ProjectedUnitaryEncoding A U L R → 0<eps → (realTarget p).degree ≤ (d:WithBot ℕ) →
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) →
  ∃ data : PhaseData, ((produce p d eps).value).value=some data ∧
    let cs := computedPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit cs ∧ adjointQueryCount cs=d ∧ adjointGateCount cs=d+1 ∧
    (d%2=1 → BlockEncoding (oddSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) 1 (eps:ℝ)) ∧
    (d%2=0 → BlockEncoding (rightSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L) (rangeProjector R) data))
      (averageFrame R) (averageFrame R) 1 (eps:ℝ)) := by
  simpa only [produce_value] using computed_phase_word_actual_matrix_transform

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
