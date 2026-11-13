/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Specification of real polynomial pair completion

`Theorem5RealCharacterization` states an equivalence between a bounded real polynomial pair with
the prescribed degree and parity and the existence of a complex `CompletedPair` with those real
parts. The real-part conditions are expressed as identities involving coefficientwise
conjugation. See [GilyenSuLowWiebe2019].

## Main statements

* `Theorem5RealCharacterization`: the real-pair completion equivalence.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial

/-- The assertion that real polynomial pairs satisfying the degree, parity, and weighted
interval bound are precisely the real parts of complex completed pairs, as in [Gilyén et
al., Theorem 5][GilyenSuLowWiebe2019]. -/
def Theorem5RealCharacterization : Prop :=
  ∀ (k : ℕ) (Pt Qt : Polynomial ℝ),
    (Pt.degree ≤ (k : WithBot ℕ) ∧ Qt.degree < (k : WithBot ℕ) ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity k Pt ∧
      Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (k + 1) Qt ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) ↔
    (∃ P Q : Polynomial ℂ,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair k P Q ∧
      P + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial P =
        C (2 : ℂ) * Pt.map Complex.ofRealHom ∧
      Q + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial Q =
        C (2 : ℂ) * Qt.map Complex.ofRealHom)

end Qatlib.Concepts.QsvtCore.PhaseExistence
