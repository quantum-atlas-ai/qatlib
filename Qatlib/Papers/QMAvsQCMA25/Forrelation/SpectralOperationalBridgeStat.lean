/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyStat
public import Qatlib.Concepts.WalshMoment.Forrelation.QmaVerifierSpectralForrelationStat

@[expose] public section
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Qatlib

def SpectralOperationalBridge : Prop :=
  ∀ (n : ℕ) (S U : Reg n → Bool) (v : ℕ),
    IsStrongYes (57 / 100) (59 / 100) v S U →
    ∃ (C : TOCircuit (ForrSpace n (Reg n × Bool)))
      (E : Finset (ForrSpace n (Reg n × Bool))),
      IsUnitaryTOCircuit C ∧
      (∃ ψ : QState (Reg n), Normalized ψ ∧
        2 / 3 ≤ MeasureProb
          (TORun (forrBitOracleS n S (Reg n × Bool))
            (forrBitOracleU n U (Reg n × Bool)) C (witnessEmbed n ψ)) E) ∧
      (∀ Δ : Reg n → Bool, (∀ x, Δ x → S x) → supportCard Δ ≤ v →
        ∀ ψ : QState (Reg n), Normalized ψ →
          MeasureProb
            (TORun (forrBitOracleS n Δ (Reg n × Bool))
              (forrBitOracleU n U (Reg n × Bool)) C (witnessEmbed n ψ)) E ≤
            1 / 3)

end Qatlib.Papers.QMAvsQCMA25.Forrelation
