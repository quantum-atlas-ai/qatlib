/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
set_option warningAsError false


open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial

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
