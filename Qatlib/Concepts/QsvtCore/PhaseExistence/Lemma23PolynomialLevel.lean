/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23OutputTransport
set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

def Lemma23PolynomialLevel : Prop :=
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (P : Polynomial ℂ) (n : ℕ),
    0 < n → P.natDegree = n →
    Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity n P →
    (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1) →
    (∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
      1 ≤ Complex.normSq (P.eval (Complex.ofReal x))) →
    (n % 2 = 0 → ∀ y : ℝ,
      1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))) →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
    let rate : ℝ :=
      (n : ℝ) * Real.sqrt (2 / (1 - ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2)) * ‖A - B‖
    (n % 2 = 1 →
      ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A (fun x => P.eval (x : ℂ)) -
        Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform B (fun x => P.eval (x : ℂ))‖ ≤
      rate) ∧
    (n % 2 = 0 →
      ‖Qatlib.Concepts.WalkSearch.Spectral.rightSingularTransform A (fun x => P.eval (x : ℂ)) -
        Qatlib.Concepts.WalkSearch.Spectral.rightSingularTransform B (fun x => P.eval (x : ℂ))‖ ≤
      rate)

end Qatlib.Concepts.QsvtCore.PhaseExistence
