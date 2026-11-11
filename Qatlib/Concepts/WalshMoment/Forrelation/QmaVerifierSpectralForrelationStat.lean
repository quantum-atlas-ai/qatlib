/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

/-!
# Specification of the spectral forrelation verifier

This module states `QmaVerifierSpectralForrelation`: for every register size and pair of Boolean
oracles, a unitary two-oracle circuit makes one query to each oracle and has an accepting event
whose measurement weight equals `forrWitnessMass` for every embedded witness vector. The
equality is stated for arbitrary vectors; normalized vectors yield the usual
acceptance-probability interpretation.

The state, unitary circuit, and measurement framework follows the standard setting of
[Watrous2018].

## Key declaration

* `QmaVerifierSpectralForrelation` records the circuit, query-count, and measurement
  requirements.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

open Qatlib.Concepts.QmaCompleteness.WitnessSampler
open Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib

/-- The specification that every pair of Boolean oracles has a unitary circuit making one query
to each oracle and an accepting event whose measurement weight equals `forrWitnessMass` for
every embedded witness vector. -/
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
