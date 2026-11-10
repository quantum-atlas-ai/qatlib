/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalTigh
import Qatlib.Concepts.SearchStopping.GroverSuccess.Section2HalfIterationsSubgoalTigh
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.FairRandomBits.GeometricRetry
set_option warningAsError false
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.SearchStopping.GateCore

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def bbhtPreparedSourceCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I := Step.gate T' :: SourceGateCircuit T' v j

noncomputable def bbhtBitSearchCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit (I × Bool) :=
  Step.gate (TensorGate (1 : Matrix I I ℂ) Hadamard) ::
    LiftCircuit (bbhtPreparedSourceCircuit T' v j)

noncomputable def bbhtBitSearchSamples (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) : PMF (I × Bool) :=
  bornDistribution
    (Run (BitOracleOn (fun i => decide (i ∈ A))) (bbhtBitSearchCircuit T' v j)
      (TensorState v (Ket true)))
    (hC.normalized_run (bitOracleOn_unitary _)
      (normalized_tensorState hv (normalized_ket true)))

noncomputable def bbhtVerificationLaw (A : Finset I) (i : I) : PMF Bool :=
  (bornDistribution
    (Run (BitOracleOn (fun z => decide (z ∈ A))) [Step.query] (Ket (i, false)))
    (((isUnitaryCircuit_query ([] : Circuit (I × Bool))).mpr isUnitaryCircuit_nil).normalized_run
      (bitOracleOn_unitary _) (normalized_ket (i, false)))).map Prod.snd

noncomputable def bbhtActualRestartNextPrice (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) (price : ℕ) : Unit → PMF ((I ⊕ Unit) × ℕ) :=
  fun _ => (bbhtBitSearchSamples T' v j A hC hv).bind fun q =>
    (bbhtVerificationLaw A q.1).map fun b =>
      (((if b then Sum.inl q.1 else Sum.inr ()) : I ⊕ Unit), price)

noncomputable def bbhtActualRestartNext (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) : Unit → PMF ((I ⊕ Unit) × ℕ) :=
  bbhtActualRestartNextPrice T' v j A hC hv (j + 1)

end Qatlib.Concepts.SearchStopping.PaidRestart
