/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.SignalProcessing
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

/-!
# Specification of QSP polynomial entry form

`FunctionFormSubgoal` specifies four polynomials representing the entries of `QSPWord` on the
real unit interval. It records their degree bounds, their parity, and the square-root factor in
the off-diagonal entries. Background and related constructions are discussed in
[GilyenSuLowWiebe2019].

## Main statements

* `FunctionFormSubgoal`: the polynomial function-form property for every phase list.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

/-- Specifies four complex polynomials representing the entries of every QSP word on [−1, 1],
with degree and parity determined by the phase-list length. The off-diagonal entries include
the factor i√(1 − x²). -/
def FunctionFormSubgoal : Prop :=
  ∀ (phis : List ℝ), ∃ (P Q₁ Q₂ S : Polynomial ℂ),
    P.natDegree ≤ phis.length ∧
    S.natDegree ≤ phis.length ∧
    Q₁.natDegree ≤ phis.length - 1 ∧
    Q₂.natDegree ≤ phis.length - 1 ∧
    (∀ t : ℂ, P.eval (-t) = ((-1 : ℂ) ^ phis.length) * P.eval t) ∧
    (∀ t : ℂ, S.eval (-t) = ((-1 : ℂ) ^ phis.length) * S.eval t) ∧
    (∀ t : ℂ, Q₁.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₁.eval t) ∧
    (∀ t : ℂ, Q₂.eval (-t) = ((-1 : ℂ) ^ (phis.length + 1)) * Q₂.eval t) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 0 = P.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 1 = S.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 0 1
      = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₁.eval ((x : ℂ))) ∧
    (∀ x : ℝ, -1 ≤ x → x ≤ 1 → (QSPWord phis x) 1 0
      = Complex.I * ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) * Q₂.eval ((x : ℂ)))

end Qatlib.Concepts.QspSimulation.WordModel
