/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT

/-!
# Source-convention QSVT specification

This module defines `SourceConventionQSVTGeneral`, a proposition combining degree-optimal real
phase synthesis with odd and even projected-corner identities. It also specifies the separate
minimal lengths for constant responses, in the QSVT setting of [GilyenSuLowWiebe2019].

## Main statements

* `SourceConventionQSVTGeneral`: Specify phase existence, minimality, projected corners, and
  constant cases.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false


open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.QsVtMain

/-- The source-convention QSVT specification combining degree-optimal real phases,
parity-dependent projected singular transforms, and minimal lengths for constants. -/
def SourceConventionQSVTGeneral : Prop :=
  (∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (p : Polynomial ℝ) (d : ℕ),
    ProjectedUnitaryEncoding A U L R → 0 < d → p.degree = (d : WithBot ℕ) →
    HasRealParity d p → (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
    ∃ Φ : List ℝ, Φ.length = d ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) ∧
      (∀ Ψ : List ℝ, (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re = p.eval x) →
        d ≤ Ψ.length ∧ Ψ.length % 2 = d % 2) ∧
      (d % 2 = 1 →
        rangeProjector L * phasedAlternating U (rangeProjector R) (rangeProjector L) 1
            (Φ.map anglePhase) * rangeProjector R =
          L * oddSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ) ∧
      (d % 2 = 0 →
        rangeProjector R * phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) 1
            (Φ.map anglePhase) * rangeProjector R =
          R * rightSingularTransform A (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) * Rᴴ)) ∧
  (∀ c : ℝ, |c| ≤ 1 →
    (∃ Φ : List ℝ, Φ.length = (if c = 1 then 0 else if c = 0 then 1 else 2) ∧
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = c)) ∧
    (∀ Ψ : List ℝ, (∀ x : ℝ, ((sourcePhaseResponse Ψ).eval (x : ℂ)).re = c) →
      (if c = 1 then 0 else if c = 0 then 1 else 2) ≤ Ψ.length))

end Qatlib.Concepts.QsvtCore.QsVtMain
