/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

def Theorem4QCharacterization : Prop :=
  ∀ (k : ℕ) (Q : Polynomial ℂ),
    (∃ P : Polynomial ℂ,
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.CompletedPair k P Q) ↔
      (Q.degree < (k : WithBot ℕ) ∧
        Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity (k + 1) Q ∧
        (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
          (1 - x ^ 2) * Complex.normSq (Q.eval (Complex.ofReal x)) ≤ 1) ∧
        (k % 2 = 1 → ∀ y : ℝ,
          1 ≤ (1 + y ^ 2) * Complex.normSq (Q.eval (Complex.ofReal y * Complex.I))))

end Qatlib.Concepts.QsvtCore.PhaseExistence
