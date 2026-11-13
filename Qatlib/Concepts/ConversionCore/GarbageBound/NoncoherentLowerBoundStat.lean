/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2

/-!
# Noncoherent state conversion lower bound specification

`StateConversionNoncoherentLowerBound` states the two-certificate lower bound for conversion
with garbage states. The target family has Gram matrix `gramStateMatrix σ ⊙ S`, and the
conclusion permits a new positive semidefinite matrix `S'` with diagonal one after aligning
phases.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `StateConversionNoncoherentLowerBound`: The noncoherent conversion certificate proposition.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open scoped ComplexOrder MatrixOrder
open Matrix

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.GarbageBound

/-- The statement that noncoherent conversion with absolute overlaps at least √(1 − ε) yields a
positive semidefinite intermediate matrix and a positive semidefinite garbage matrix with
diagonal one, with unfiltered error budget 2√(2ε) and query-filtered budget 2T for 0 < ε ≤
1. -/
def StateConversionNoncoherentLowerBound : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n T R : ℕ) (input : X → Fin n → Bool)
    (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (ρ σ : X → QState ((Fin n × Bool) × Fin R)),
      (∀ x, Normalized (ρ x)) → (∀ x, Normalized (σ x)) →
    ∀ χ : X → QState ((Fin n × Bool) × Fin R), (∀ x, Normalized (χ x)) →
    ∀ S : Matrix X X ℂ, S.PosSemidef → (∀ x, S x x = 1) →
      gramStateMatrix χ = gramStateMatrix σ ⊙ S →
    ∀ C : Circuit ((Fin n × Bool) × Fin R),
      QueryCount C = T → IsUnitaryCircuit C →
      (∀ x, Real.sqrt (1 - ε) ≤
        ‖Inner (Run (workspaceBitOracle (W := Fin R) (input x)) C (ρ x)) (χ x)‖) →
    ∃ (σ' S' : Matrix X X ℂ),
      σ'.PosSemidef ∧ S'.PosSemidef ∧ (∀ x, S' x x = 1) ∧
      gramFilteredCert (σ' - gramStateMatrix σ ⊙ S')
        (fun _ : Fin 1 => gramFilterAllOnes) (2 * Real.sqrt (2 * ε)) ∧
      gramFilteredCert (gramStateMatrix ρ - σ')
        (gramFilterDelta input) (2 * T)

end Qatlib.Concepts.ConversionCore.GarbageBound
