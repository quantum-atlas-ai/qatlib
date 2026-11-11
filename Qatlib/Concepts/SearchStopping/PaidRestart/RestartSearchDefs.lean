/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalTigh
import Qatlib.Concepts.SearchStopping.GroverSuccess.Section2HalfIterationsSubgoalTigh
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.FairRandomBits.GeometricRetry

/-!
# Circuits and transitions for paid Grover restarts

Defines the prepared source circuit and its bit-oracle lift, together with their Born sampling
laws. `bbhtActualRestartNextPrice` performs search, verifies the sampled address with a Boolean
query, and attaches a fixed receipt; `bbhtActualRestartNext` selects price `j + 1`. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `bbhtBitSearchCircuit`: The lifted prepared source circuit preceded by a Hadamard gate on the
  Boolean oracle register.
* `bbhtActualRestartNextPrice`: The paid restart transition that samples the bit-search circuit,
  verifies its address, and returns either that address or the retry state with the specified
  price.
* `bbhtActualRestartNext`: The verified search restart transition with fixed price `j + 1` for
  `j` Grover iterations.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

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

/-- Prepends the preparation gate `T'` to the `j`-step source-gate search circuit. -/
noncomputable def bbhtPreparedSourceCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit I := Step.gate T' :: SourceGateCircuit T' v j

/-- The lifted prepared source circuit preceded by a Hadamard gate on the Boolean oracle
register. -/
noncomputable def bbhtBitSearchCircuit (T' : Matrix I I ℂ) (v : QState I) (j : ℕ) :
    Circuit (I × Bool) :=
  Step.gate (TensorGate (1 : Matrix I I ℂ) Hadamard) ::
    LiftCircuit (bbhtPreparedSourceCircuit T' v j)

/-- The Born distribution obtained by running the bit-search circuit with the marked-set Boolean
oracle from `v` tensored with `Ket true`. -/
noncomputable def bbhtBitSearchSamples (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) : PMF (I × Bool) :=
  bornDistribution
    (Run (BitOracleOn (fun i => decide (i ∈ A))) (bbhtBitSearchCircuit T' v j)
      (TensorState v (Ket true)))
    (hC.normalized_run (bitOracleOn_unitary _)
      (normalized_tensorState hv (normalized_ket true)))

/-- The Boolean outcome distribution of a single marked-set oracle query on the basis input `(i,
false)`. -/
noncomputable def bbhtVerificationLaw (A : Finset I) (i : I) : PMF Bool :=
  (bornDistribution
    (Run (BitOracleOn (fun z => decide (z ∈ A))) [Step.query] (Ket (i, false)))
    (((isUnitaryCircuit_query ([] : Circuit (I × Bool))).mpr isUnitaryCircuit_nil).normalized_run
      (bitOracleOn_unitary _) (normalized_ket (i, false)))).map Prod.snd

/-- The paid restart transition that samples the bit-search circuit, verifies its address, and
returns either that address or the retry state with the specified price. -/
noncomputable def bbhtActualRestartNextPrice (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) (price : ℕ) : Unit → PMF ((I ⊕ Unit) × ℕ) :=
  fun _ => (bbhtBitSearchSamples T' v j A hC hv).bind fun q =>
    (bbhtVerificationLaw A q.1).map fun b =>
      (((if b then Sum.inl q.1 else Sum.inr ()) : I ⊕ Unit), price)

/-- The verified search restart transition with fixed price `j + 1` for `j` Grover iterations. -/
noncomputable def bbhtActualRestartNext (T' : Matrix I I ℂ) (v : QState I) (j : ℕ)
    (A : Finset I) (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j))
    (hv : Normalized v) : Unit → PMF ((I ⊕ Unit) × ℕ) :=
  bbhtActualRestartNextPrice T' v j A hC hv (j + 1)

end Qatlib.Concepts.SearchStopping.PaidRestart
