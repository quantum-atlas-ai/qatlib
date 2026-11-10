/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib

def QmaVerifierSpectralForrelation : Prop :=
  ∀ (n : ℕ) (S U : Reg n → Bool),
    ∃ (C : TOCircuit (ForrSpace n (Reg n × Bool)))
      (E : Finset (ForrSpace n (Reg n × Bool))),
      IsUnitaryTOCircuit C ∧
      TOQueryCountS C = 1 ∧
      TOQueryCountU C = 1 ∧
      ∀ ψ : QState (Reg n),
        MeasureProb
            (TORun (forrBitOracleS n S (Reg n × Bool)) (forrBitOracleU n U (Reg n × Bool)) C
              (witnessEmbed n ψ)) E =
          forrWitnessMass n S U ψ

end Qatlib.Concepts.WalshMoment.Forrelation
