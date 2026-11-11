/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value

/-!
# Coherent state conversion SDP specification

`StateConversionSDPLowerBound` formulates a lower bound on circuit query cost through
`stateConversionSDP`. For normalized state families and a real overlap guarantee, the SDP
evaluated at tolerance `2 * Real.sqrt (2 * ε)` is bounded by twice the number of Boolean
workspace queries.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `StateConversionSDPLowerBound`: The SDP value bound in the extended nonnegative reals.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder MatrixOrder ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.CoherentBound

/-- The statement that coherent conversion with real overlaps at least √(1 − ε) by a unitary
`T`-query circuit bounds the state conversion SDP at tolerance 2√(2ε) by 2T, for 0 < ε ≤ 1. -/
def StateConversionSDPLowerBound : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n T R : ℕ) (input : X → Fin n → Bool)
    (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (ρ σ : X → QState ((Fin n × Bool) × Fin R)),
      (∀ x, Normalized (ρ x)) → (∀ x, Normalized (σ x)) →
      ∀ (C : Circuit ((Fin n × Bool) × Fin R)),
        QueryCount C = T → IsUnitaryCircuit C →
        (∀ x, Real.sqrt (1 - ε) ≤ Complex.re
          (Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)) (σ x))) →
        stateConversionSDP input (2 * Real.sqrt (2 * ε)) (gramStateMatrix ρ)
          (gramStateMatrix σ) ≤ ((2 * T : ℕ) : ℝ≥0∞)

end Qatlib.Concepts.ConversionCore.CoherentBound
