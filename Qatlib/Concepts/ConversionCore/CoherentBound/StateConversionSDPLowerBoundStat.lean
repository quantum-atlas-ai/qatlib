/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Value
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open scoped ComplexOrder MatrixOrder ENNReal

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.ConversionCore.CoherentBound

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
