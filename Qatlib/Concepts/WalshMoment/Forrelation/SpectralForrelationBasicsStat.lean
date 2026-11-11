/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation

/-!
# Specification of basic spectral forrelation properties

This module collects the desired bounds and witness properties of spectral forrelation into
`SpectralForrelationBasics`. The specification requires a value in `[0, 1]`, an upper bound on
normalized witness mass, a normalized witness meeting every lower target at most the spectral
value, and vanishing when either Boolean predicate is identically false.

These properties express the finite-dimensional operator-norm viewpoint used in quantum
information; see [Watrous2018].

## Key declaration

* `SpectralForrelationBasics` packages the bounds, witness existence, and zero cases.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib

/-- The specification of spectral forrelation's range, normalized-witness upper bound, and
existence of witnesses meeting every target at most the spectral value. It also requires
vanishing when either oracle predicate is identically false. -/
def SpectralForrelationBasics : Prop :=
  ∀ (n : ℕ) (S U : Reg n → Bool),
    0 ≤ spectralForrelation n S U ∧
    spectralForrelation n S U ≤ 1 ∧
    (∀ ψ : QState (Reg n), Normalized ψ → forrWitnessMass n S U ψ ≤ spectralForrelation n S U) ∧
    (∀ α : ℝ, α ≤ spectralForrelation n S U →
      ∃ ψ : QState (Reg n), Normalized ψ ∧ α ≤ forrWitnessMass n S U ψ) ∧
    (S = (fun _ => false) → spectralForrelation n S U = 0) ∧
    (U = (fun _ => false) → spectralForrelation n S U = 0)

end Qatlib.Concepts.WalshMoment.Forrelation
