/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.UniformBqp.OracleAmplify.Theorem35RandomOracleFiniteDefs
set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UniformBqp.OracleAmplify

open Qatlib

open Classical in

def Theorem3_5RandomOracleFinite : Prop :=
  ∀ {K W : Type} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W]
    (C : Circuit (QueryRegister K W)) (ψ : QState (QueryRegister K W))
    (E : Finset (QueryRegister K W)),
    IsUnitaryCircuit C → Normalized ψ →
      1 ≤ QueryCount C →
        160 * (QueryCount C : ℝ) ^ 2 ≤ (Fintype.card (K → Bool) : ℝ) →
          (Fintype.card ((K → Bool) → (K → Bool)) : ℝ) ≤
            8 * (Finset.univ.filter (fun A : (K → Bool) → (K → Bool) =>
              ¬ decidesAtAllOnes (acceptProb C ψ E A) A)).card

end Qatlib.Concepts.UniformBqp.OracleAmplify
