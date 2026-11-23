module

import Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric.TraceDistanceContraction
import Qatlib.Papers.QShannonWilde11.MainResults.QEntropy.PureStateEntropy

set_option autoImplicit false
set_option warningAsError true

open Matrix
open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Qatlib.Papers.QShannonWilde11.MainResults.FidelityMetric
open Qatlib.Papers.QShannonWilde11.MainResults.QEntropy
open scoped BigOperators

namespace QatlibTests.QShannonWilde11TraceDistanceContractionRegression

noncomputable section

/-- The computational basis vector of a qubit. -/
private def qubitVec (i : Fin 2) : Fin 2 → ℂ := fun j => if j = i then 1 else 0

/-- The computational basis vector of a two-qubit register. -/
private def pairVec (a b : Fin 2) : Fin 2 × Fin 2 → ℂ :=
  fun p => if p = (a, b) then 1 else 0

/-- Every computational basis vector of a qubit has unit norm. -/
private theorem qubitVec_unit (i : Fin 2) : IsUnitVec (qubitVec i) := by
  fin_cases i <;> simp [IsUnitVec, qubitVec]

/-- Every computational basis vector of a two-qubit register has unit norm. -/
private theorem pairVec_unit (a b : Fin 2) : IsUnitVec (pairVec a b) := by
  fin_cases a <;> fin_cases b <;> simp [IsUnitVec, pairVec, Fintype.sum_prod_type]

/-- A concrete qubit state, non-degenerate because `Fin 2` is non-empty. -/
private def qubitState (i : Fin 2) : Dens (Fin 2) :=
  pureDensity (qubitVec i) (qubitVec_unit i)

/-- A concrete two-qubit state, non-degenerate because `Fin 2 × Fin 2` is non-empty. -/
private def pairState (a b : Fin 2) : Dens (Fin 2 × Fin 2) :=
  pureDensity (pairVec a b) (pairVec_unit a b)

/-- The rank-one projector `|0⟩⟨0|` is an effect on a qubit. -/
private theorem qubitState_zero_effect : IsEffect (qubitState 0).val := by
  constructor
  · exact (qubitState 0).property.1
  · have hcomp : (1 : Op (Fin 2)) - (qubitState 0).val = (qubitState 1).val := by
      rw [show (qubitState 0).val =
            Qatlib.Foundations.PureStateMath.Reflection.outerProduct (qubitVec 0) from
            pureDensity_val (qubitVec 0) (qubitVec_unit 0),
          show (qubitState 1).val =
            Qatlib.Foundations.PureStateMath.Reflection.outerProduct (qubitVec 1) from
            pureDensity_val (qubitVec 1) (qubitVec_unit 1)]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [qubitVec, Qatlib.Foundations.PureStateMath.Reflection.outerProduct]
    rw [hcomp]
    exact (qubitState 1).property.1

/-- Corollary 9.1.1 is invoked on the concrete orthogonal qubit states `|0⟩` and `|1⟩` with
the rank-one effect `|0⟩⟨0|`. -/
theorem measurement_close_states_qubit :
    (Matrix.trace ((qubitState 0).val * (qubitState 1).val)).re ≥
      (Matrix.trace ((qubitState 0).val * (qubitState 0).val)).re -
        (1 / 2 : ℝ) * traceNormDiff (qubitState 1).val (qubitState 0).val :=
  measurement_close_states (qubitState 1) (qubitState 0) (qubitState 0).val
    qubitState_zero_effect

/-- The same concrete instance through the uniform-constant interface. -/
theorem exists_uniform_measurement_close_states_qubit :
    ∃ C : ℝ, 0 < C ∧
      (Matrix.trace ((qubitState 0).val * (qubitState 0).val)).re ≥
        (Matrix.trace ((qubitState 0).val * (qubitState 1).val)).re -
          C * traceNormDiff (qubitState 0).val (qubitState 1).val := by
  obtain ⟨C, hC, h⟩ := exists_uniform_measurement_close_states
  exact ⟨C, hC, h (Fin 2) (qubitState 0) (qubitState 1) (qubitState 0).val
    qubitState_zero_effect⟩

/-- Corollary 9.1.2 is invoked on the concrete two-qubit states `|00⟩` and `|11⟩`. -/
theorem partial_trace_contracts_pair :
    traceNormDiff (marginR (pairState 0 0)).val (marginR (pairState 1 1)).val ≤
      traceNormDiff (pairState 0 0).val (pairState 1 1).val :=
  traceNormDiff_marginR_le (pairState 0 0) (pairState 1 1)

/-- The same concrete instance through the uniform-constant interface. -/
theorem exists_uniform_traceNormDiff_marginR_pair :
    ∃ C : ℝ, 0 < C ∧
      traceNormDiff (marginR (pairState 0 0)).val (marginR (pairState 1 1)).val ≤
        C * traceNormDiff (pairState 0 0).val (pairState 1 1).val := by
  obtain ⟨C, hC, h⟩ := exists_uniform_traceNormDiff_marginR
  exact ⟨C, hC, h (Fin 2) (Fin 2) (pairState 0 0) (pairState 1 1)⟩

end

end QatlibTests.QShannonWilde11TraceDistanceContractionRegression
