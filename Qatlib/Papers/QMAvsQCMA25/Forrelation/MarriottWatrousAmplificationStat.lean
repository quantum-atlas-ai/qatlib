/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationStat
public import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation

@[expose] public section
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Qatlib

def MarriottWatrousAmplification : Prop :=
  ∀ (n : ℕ) (α β : ℝ), 0 ≤ β → β < α → α ≤ 1 →
    ∃ (qB : ℕ) (C : TOCircuit (ForrSpace n (Reg n × Bool)))
      (E : Finset (ForrSpace n (Reg n × Bool))),
      (qB : ℝ) ≤ 256 / (α - β) ^ 2 ∧
      IsUnitaryTOCircuit C ∧
      TOQueryCountS C ≤ qB ∧
      TOQueryCountU C ≤ qB ∧
      ∀ (S U : Reg n → Bool),
        (α ≤ spectralForrelation n S U →
          ∃ ψ : QState (Reg n), Normalized ψ ∧
            2 / 3 ≤ MeasureProb
              (TORun (forrBitOracleS n S (Reg n × Bool))
                (forrBitOracleU n U (Reg n × Bool)) C (witnessEmbed n ψ)) E) ∧
        (spectralForrelation n S U ≤ β →
          ∀ ψ : QState (Reg n), Normalized ψ →
            MeasureProb
              (TORun (forrBitOracleS n S (Reg n × Bool))
                (forrBitOracleU n U (Reg n × Bool)) C (witnessEmbed n ψ)) E ≤
              1 / 3)

end Qatlib.Papers.QMAvsQCMA25.Forrelation
