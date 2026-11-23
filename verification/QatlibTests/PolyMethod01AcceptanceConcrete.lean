module

public import Qatlib.Papers.PolyMethod01.MainResults.AcceptanceConcrete

set_option autoImplicit false

namespace QatlibTests.PolyMethod01AcceptanceConcrete

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.PolyMethod01.MainResults

/-- The ordinary consumer checks the one-query resource count on a concrete workspace. -/
example : QueryCount oneQueryCircuit = 1 :=
  oneQueryCircuit_queryCount

/-- The ordinary consumer checks both oracle answers on the same nontrivial circuit. -/
example :
    MeasureProb
        (Run (TensorGate (BitOracleOn (fun _ : Fin 1 => true)) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          oneQueryCircuit oneQueryInput)
        oneQueryAccepted = 1 := by
  simpa using oneQuery_measure_probability (fun _ : Fin 1 => true)

example :
    MeasureProb
        (Run (TensorGate (BitOracleOn (fun _ : Fin 1 => false)) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          oneQueryCircuit oneQueryInput)
        oneQueryAccepted = 0 := by
  simpa using oneQuery_measure_probability (fun _ : Fin 1 => false)

example :
    MeasureProb
        (Run (TensorGate (BitOracleOn (fun _ : Fin 1 => true)) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          oneQueryCircuit oneQueryInput)
        oneQueryAccepted = ‖oneQueryAcceptedVector (fun _ : Fin 1 => true)‖ ^ 2 := by
  exact oneQuery_probability_eq_euclidean_norm_sq (fun _ : Fin 1 => true)

/-- The ordinary consumer invokes the top-level polynomial-method specification. -/
example :
    (booleanAcceptancePolynomial oneQueryCircuit oneQueryInput oneQueryAccepted).totalDegree ≤
        2 * QueryCount oneQueryCircuit :=
  oneQuery_acceptance_spec.1

end QatlibTests.PolyMethod01AcceptanceConcrete
