/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Budget
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.OriginalContract

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Original physical-word semantics and the paid preprocessing trace refer to one
actual returned run. The original query and matrix-macro gate counts remain
separate from the explicit arithmetic/access budget. Quantum execution,
host bit time, fixed elementary-gate refinement and polynomial preprocessing
are not certified by this budget. -/
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

/-- The same paid execution returns the original packet and both actual parity words. -/
theorem budgeted_phase_word_actual_matrix_transform : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (p : List ℚ) (d : ℕ) (eps : ℚ),
  ProjectedUnitaryEncoding A U L R → 0<eps → (realTarget p).degree ≤ (d:WithBot ℕ) →
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget p).eval x| ≤ 1) →
  ∀ (model : PriceModel) (actual : Run SynthesisResult) (budget : ℕ),
  CertifiedBudget model p d eps actual budget →
  (∃ data : PhaseData, actual.value.value=some data ∧
    let cs := computedPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit cs ∧ adjointQueryCount cs=d ∧ adjointGateCount cs=d+1 ∧
    (d%2=1 → BlockEncoding (oddSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle U) cs) (averageFrame L) (averageFrame R) 1 (eps:ℝ)) ∧
    (d%2=0 → BlockEncoding (rightSingularTransform A (fun x => (((realTarget p).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L) (rangeProjector R) data))
      (averageFrame R) (averageFrame R) 1 (eps:ℝ))) ∧ charge model actual.events ≤ budget := by
  intro H I O _ _ _ _ _ _ A U L R p d eps henc heps hp hpar hbound model actual budget hpaid
  rcases hpaid with ⟨heq,hcost⟩
  subst actual
  refine ⟨?_,hcost⟩
  exact traced_phase_word_actual_matrix_transform H I O A U L R p d eps henc heps hp hpar hbound

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
