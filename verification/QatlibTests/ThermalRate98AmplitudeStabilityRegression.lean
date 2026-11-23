module

import Qatlib.Papers.ThermalRate98.MainResults.AmplitudeStability
import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.ThermalRate98AmplitudeStabilityRegression

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.ThermalRate98.MainResults

/-- A four-level phase transform on two encoded qubits is unitary. -/
private theorem phase4_mem_unitaryGroup :
    Matrix.diagonal (fun _ : Fin 4 => Complex.I) ∈
      Matrix.unitaryGroup (Fin 4) ℂ :=
  diagonal_mem_unitaryGroup _ fun _ => by norm_num

/-- The Eq. 47 isometry is exercised on distinct basis states of a two-qubit
register with a nontrivial phase transform. -/
example :
    ‖toEuclidean_fromVec
        (ApplyGate (Matrix.diagonal (fun _ : Fin 4 => Complex.I)) (Ket (0 : Fin 4)) -
          ApplyGate (Matrix.diagonal (fun _ : Fin 4 => Complex.I)) (Ket (1 : Fin 4)))‖ =
      ‖toEuclidean_fromVec (Ket (0 : Fin 4) - Ket (1 : Fin 4))‖ :=
  eq47_unitary_recovery_isometry _ phase4_mem_unitaryGroup _ _

/-- The uniform bound controls the difference between an event probability
after reconstruction and its exact value in the position basis. -/
example :
    ∃ C > 0,
      |MeasureProb
          (ApplyGate (Matrix.diagonal (fun _ : Fin 4 => Complex.I)) (Ket (0 : Fin 4)))
          {0} -
        MeasureProb (Ket (1 : Fin 4)) {0}| ≤
        C * ‖toEuclidean_fromVec (Ket (0 : Fin 4) -
          ApplyGate (star (Matrix.diagonal (fun _ : Fin 4 => Complex.I))) (Ket (1 : Fin 4)))‖ := by
  obtain ⟨C, hC, h⟩ := eq47_encoded_qubits_born_stability
  refine ⟨C, hC, ?_⟩
  exact h 2 (by norm_num) _ phase4_mem_unitaryGroup _ _
    (normalized_ket (1 : Fin 4)) (normalized_ket (0 : Fin 4)) {0}

end QatlibTests.ThermalRate98AmplitudeStabilityRegression
