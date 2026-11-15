/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Theorem13CertFormToAlgorithmQuan
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Corollary15CertificateQueryBelowStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Concepts.QueryComplexity.NormObstruction Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

/-- For nonnegative error and positive query budget, a completely bounded form certificate with
the stated approximation bound yields `ComputesBiasOn` at that budget. -/
theorem corollary1_5CertificateQueryBelow : Corollary1_5CertificateQueryBelow := by
  intro n D f ε t hε ht hex
  obtain ⟨S, hcert, hbox⟩ := hex
  obtain ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, hbias⟩ :=
    theorem1_3CertificateFormToAlgorithm n t S hcert
  refine ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, ?_⟩
  intro x hx
  have h1 : signBias (Run (cbPhaseOracle δ x) C ψ) E = formBias S x := hbias x
  rw [h1]
  exact hbox x hx

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
