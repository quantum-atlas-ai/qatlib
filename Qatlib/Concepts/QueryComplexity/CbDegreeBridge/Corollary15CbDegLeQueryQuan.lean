/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Theorem13AlgorithmToFormQuan
public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.Corollary15CbDegLeQueryStat

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

/-- For positive input size and query budget and nonnegative error, computing the bias with that
budget bounds `cbDeg` by the budget. -/
theorem corollary1_5CbDegLeQuery : Corollary1_5CbDegLeQuery := by
  intro n hn D f ε t hε ht hcomp
  obtain ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, hbox⟩ := hcomp
  have hsign : HasSignAlgorithm (fun x => signBias (Run (cbPhaseOracle δ x) C ψ) E) t :=
    ⟨R, iR, dR, δ, C, ψ, E, hC, hψ, hqc, fun _ => rfl⟩
  obtain ⟨S, hsymm, hnorm, hbias⟩ :=
    theorem1_3AlgorithmToForm n hn t (fun x => signBias (Run (cbPhaseOracle δ x) C ψ) E) hsign
  refine Nat.sInf_le ⟨ht, S, hsymm, hnorm, ?_⟩
  intro x hx
  have h1 : formBias S x = signBias (Run (cbPhaseOracle δ x) C ψ) E := hbias x
  rw [h1]
  exact hbox x hx

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
