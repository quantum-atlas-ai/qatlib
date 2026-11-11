/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.UniformBqp.OracleAmplify.Theorem35RandomOracleFiniteDefs

/-!
# Finite random-oracle lower-bound specification

`Theorem3_5RandomOracleFinite` formulates the finite counting form of the random-oracle
obstruction in [BennettEtAl1997]. Under the stated quadratic query bound, at least one eighth of
all string-valued oracles violate the circuit's bounded-error all-ones image-membership
criterion. The background is described in [BennettEtAl1997].

## Main statements

* `Theorem3_5RandomOracleFinite`: a constant-fraction failure bound under a quadratic query
  restriction.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UniformBqp.OracleAmplify

open Qatlib

open Classical in

/-- The finite random-oracle failure assertion: a normalized unitary circuit using at least one
query, with `160*(QueryCount C)^2 ≤ Fintype.card (K → Bool)`, fails to decide all-ones image
membership on at least one eighth of all oracles [BennettEtAl1997]. -/
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
