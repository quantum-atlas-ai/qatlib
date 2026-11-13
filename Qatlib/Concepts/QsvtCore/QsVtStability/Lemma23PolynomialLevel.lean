/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma23PolynomialLevel
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23InteriorRobustnessGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily

/-!
# Polynomial-level interior QSVT robustness

This module proves `lemma23PolynomialLevel` by synthesizing a complex polynomial response and
applying the packaged interior phase-list estimate. It connects polynomial phase existence with
the singular-transform robustness statement associated with Lemma 23 of [GilyenSuLowWiebe2019].

## Main statements

* `lemma23PolynomialLevel`: Establish the polynomial-level interior robustness specification.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Matrix.Norms.L2Operator

/-- Derive the polynomial-level interior singular-transform robustness specification from
complex phase synthesis and [GilyenSuLowWiebe2019, Lemma 23][GilyenSuLowWiebe2019]. -/
theorem lemma23PolynomialLevel : Lemma23PolynomialLevel := by
  intro I O _ _ _ _ A B P n hn hdeg hpar hin hout himag hA hB hbudget
  obtain ⟨Φ,hlen,hP,_⟩ := corollary8ComplexPhaseExistence P n hn hdeg hpar hin hout himag
  have hphases : ∀ z ∈ Φ.map anglePhase, IsPhase z := by
    intro z hz
    obtain ⟨φ,_,rfl⟩ := List.mem_map.mp hz
    exact anglePhase_isPhase φ
  have hresponse : interiorResponse 1 (Φ.map anglePhase) =
      (fun x : ℝ => P.eval (x : ℂ)) := by
    change (fun x : ℝ => (sourcePhaseResponse Φ).eval (x : ℂ)) = _
    rw [hP]
  have h := lemma23InteriorRobustness I O A B 1 (Φ.map anglePhase)
    (by simp [IsPhase]) hphases hA hB hbudget
  simpa only [List.length_map,hlen,hresponse,interiorRate] using! h

end Qatlib.Concepts.QsvtCore.QsVtStability
