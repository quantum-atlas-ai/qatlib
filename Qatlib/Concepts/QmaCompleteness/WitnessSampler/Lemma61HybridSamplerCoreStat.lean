/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

def Lemma6_1HybridSamplerCore : Prop :=
  ∀ (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (S Δ U : Reg n → Bool) (t : ℕ)
    (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)),
    IsUnitaryTOCircuit C →
    Normalized ψ →
    (∀ x, Δ x → S x) →
    TOQueryCountS C ≤ t →
    2 / 3 ≤
        MeasureProb (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ) E →
    MeasureProb (TORun (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ) E ≤ 1 / 3 →
    1 / (t : ℝ) *
        ((sQueryStates (forrPhaseOracleS n Δ W) (forrPhaseOracleU n U W) C ψ).map
          (controlFiberMass n S Δ W)).sum ≥
      1 / (36 * (t : ℝ) ^ 2)

end Qatlib.Concepts.QmaCompleteness.WitnessSampler
