/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

def Theorem3Characterization : Prop :=
  ∀ (k : ℕ) (P Q : Polynomial ℂ),
    (∃ base : ℂ, ∃ zs : List ℂ,
      Qatlib.Concepts.PhaseGeometry.Phase.IsPhase base ∧
      (∀ z ∈ zs, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) ∧
      zs.length = k ∧
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseP base zs = P ∧
      Qatlib.Concepts.TrotterFormula.SuzukiFourth.responseQ base zs = Q) ↔
    (P.degree ≤ (k : WithBot ℕ) ∧ Q.degree < (k : WithBot ℕ) ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity k P ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity (k + 1) Q ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (Complex.ofReal x))
          + (1 - x ^ 2) * Complex.normSq (Q.eval (Complex.ofReal x)) = 1))

end Qatlib.Concepts.QsvtCore.PhaseExistence
