/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
public import Qatlib.Papers.QMAvsQCMA25.Forrelation.PhaseBitCircuitTransportDefs

@[expose] public section
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Qatlib

def PhaseBitCircuitTransport : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)),
    let C' := transportPhaseToBit (hadamardSControl n W) (hadamardUControl n W) C
    MeasureProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) E =
      MeasureProb (TORun (forrBitOracleS n S W) (forrBitOracleU n U W) C' ψ) E ∧
      TOQueryCountS C' = TOQueryCountS C ∧
      TOQueryCountU C' = TOQueryCountU C ∧
      (IsUnitaryTOCircuit C → IsUnitaryTOCircuit C')

end Qatlib.Papers.QMAvsQCMA25.Forrelation
