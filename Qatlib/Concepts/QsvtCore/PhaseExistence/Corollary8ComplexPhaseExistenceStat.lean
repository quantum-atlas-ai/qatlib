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
open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

def Corollary8ComplexPhaseExistence : Prop :=
  ∀ (P : Polynomial ℂ) (d : ℕ), 0 < d → P.natDegree = d →
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity d P →
    (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1) →
    (∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 → 1 ≤ Complex.normSq (P.eval (Complex.ofReal x))) →
    (d % 2 = 0 → ∀ y : ℝ,
      1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))) →
    ∃ Φ : List ℝ, Φ.length = d ∧ Qatlib.Concepts.QsvtCore.QsVtMain.sourcePhaseResponse Φ = P ∧
      (∀ Ψ : List ℝ, Qatlib.Concepts.QsvtCore.QsVtMain.sourcePhaseResponse Ψ = P →
        d ≤ Ψ.length ∧ Ψ.length % 2 = d % 2)

end Qatlib.Concepts.QsvtCore.PhaseExistence
