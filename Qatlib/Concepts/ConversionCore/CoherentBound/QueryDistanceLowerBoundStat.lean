/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder MatrixOrder

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.CoherentBound

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
