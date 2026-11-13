/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionBridge

/-!
# Statement of complex QSP phase existence

`Corollary8ComplexPhaseExistence` specifies exact realization of a complex polynomial by
`sourcePhaseResponse`. Its hypotheses require a positive exact degree, matching response parity,
and the real- and imaginary-axis inequalities used in QSP characterization.

The conclusion includes a phase list of the prescribed length and length and parity restrictions
on every realization, following the formulation associated with Corollary 8 of
[GilyenSuLowWiebe2019].

## Main statements

* `Corollary8ComplexPhaseExistence`: defines exact phase realization together with minimal
  length and parity.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError

open Polynomial

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

/-- The proposition that a complex polynomial of positive exact degree d satisfying the response
parity and QSP norm inequalities has a realizing real phase list of length d. Every phase
list with the same response has length at least d and parity d modulo two [Gilyén et al.,
Corollary 8][GilyenSuLowWiebe2019]. -/
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
