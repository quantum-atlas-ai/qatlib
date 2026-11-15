/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.NormObstruction.Lemma33FactorizationToAlgorithmQuan
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Theorem13CertFormToAlgorithmStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Concepts.QueryComplexity.NormObstruction Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.QueryComplexity.NormObstruction

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

/-- A completely bounded form certificate for a real tensor of order twice `t` yields a sign
algorithm for its form bias using `t` queries. -/
theorem theorem1_3CertificateFormToAlgorithm : Theorem1_3CertificateFormToAlgorithm := by
  intro n t S hcert
  obtain ⟨S', hfac, hvals⟩ := hcert
  obtain ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, hbias⟩ :=
    lemma3_3FactorizationToAlgorithm n t S' hfac
  refine ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, ?_⟩
  intro x
  rw [hbias x, hvals x]

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
