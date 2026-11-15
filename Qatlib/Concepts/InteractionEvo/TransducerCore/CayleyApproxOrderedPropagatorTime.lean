/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.InteractionEvo.TransducerCore.CayleyTransducer

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.CayleyTransform Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

set_option autoImplicit false

namespace Qatlib.Concepts.InteractionEvo.TransducerCore
open Qatlib
open scoped Matrix.Norms.L2Operator

/-- For the stated bounded Lipschitz Hamiltonian, a unitary Cayley transducer realizes the
Cayley product with bounded catalyst norm, and the product approximates the ordered
propagator with the specified discretization error. -/
theorem cayleyTransducerApproximatesOrderedPropagator : CayleyTransducerApproximatesOrderedPropagator := by
  intro ιS ιA _ _ _ _ a0 T α β H J hT hα hβ hcont hH hnorm hlip hJ hw
  have hwpos : 0 < α * T / J := by positivity
  refine ⟨transducerCircuit a0 (α * T / J) J,
    transducerCircuit_unitary a0 hwpos J, ?_,
    cayleyProduct_orderedEvolution_error H hcont hα hT hβ hJ hw hH hnorm hlip⟩
  intro oracle
  refine ⟨catalystMap a0 oracle, catalystMap_norm_sq_le a0 oracle hα hT hJ hH, ?_⟩
  intro ψ0
  exact cayleyTransducer_identity a0 oracle hα hT hJ hH ψ0

end Qatlib.Concepts.InteractionEvo.TransducerCore
