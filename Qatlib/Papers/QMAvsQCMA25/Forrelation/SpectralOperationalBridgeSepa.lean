/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.SpectralOperationalBridgeStat
public import Qatlib.Papers.QMAvsQCMA25.Forrelation.MarriottWatrousAmplificationSepa

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationSepa Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Papers.QMAvsQCMA25.Forrelation.MarriottWatrousAmplificationSepa

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Qatlib

set_option autoImplicit false

/-- Every strong yes instance admits a unitary bit-oracle verifier accepting some normalized
witness with probability at least two thirds, while all normalized witnesses are accepted
with probability at most one third after restricting `S` to any suboracle of support size at
most `v`. -/
theorem spectralOperationalBridge : SpectralOperationalBridge := by
  intro n S U v hstrong
  obtain ⟨qB, C, E, _hqB, hunit, _qs, _qu, hall⟩ :=
    marriottWatrousAmplification n (59 / 100) (57 / 100)
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, E, hunit, (hall S U).1 hstrong.1, ?_⟩
  intro Δ hsub hcard ψ hnorm
  exact (hall Δ U).2 (hstrong.2 Δ hsub hcard) ψ hnorm

end Qatlib.Papers.QMAvsQCMA25.Forrelation
