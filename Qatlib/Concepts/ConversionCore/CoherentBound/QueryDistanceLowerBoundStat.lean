/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2

/-!
# Coherent query distance lower bound specification

`StateConversionQueryDistanceLowerBound` states the existence of a positive semidefinite
intermediate matrix for coherent state conversion by a unitary Boolean query circuit. Its two
certificates measure closeness to the target Gram matrix and the query cost from the initial
Gram matrix.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `StateConversionQueryDistanceLowerBound`: The intermediate matrix statement with budgets
  2√(2ε) and 2T.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder MatrixOrder

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.CoherentBound

/-- The statement that a `T`-query unitary circuit with normalized input and target states and
real overlap at least √(1 − ε) produces a positive semidefinite intermediate matrix with
unfiltered error budget 2√(2ε) and query-filtered budget 2T, for 0 < ε ≤ 1. -/
def StateConversionQueryDistanceLowerBound : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n T R : ℕ) (input : X → Fin n → Bool)
    (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (ρ σ : X → QState ((Fin n × Bool) × Fin R)),
      (∀ x, Normalized (ρ x)) → (∀ x, Normalized (σ x)) →
      ∀ (C : Circuit ((Fin n × Bool) × Fin R)),
        QueryCount C = T → IsUnitaryCircuit C →
        (∀ x, Real.sqrt (1 - ε) ≤ Complex.re
          (Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)) (σ x))) →
        ∃ (σ' : Matrix X X ℂ), σ'.PosSemidef ∧
          gramFilteredCert (σ' - gramStateMatrix σ)
            (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt (2 * ε)) ∧
          gramFilteredCert (gramStateMatrix ρ - σ')
            (gramFilterDelta input) (2 * T)

end Qatlib.Concepts.ConversionCore.CoherentBound
