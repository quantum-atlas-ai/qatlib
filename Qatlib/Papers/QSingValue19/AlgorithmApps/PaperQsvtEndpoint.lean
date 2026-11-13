/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSingValue19.AlgorithmApps.PaperQsvtEndpointDefs
import Qatlib.Concepts.QsvtCore.ApproxToolkit.Lemma35DolphWindow
import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow

/-!
# QSVT application endpoint

This module proves the application endpoint combining odd word resource accounting, a Dolph
window with a flat center, and polynomial functional calculus robustness in the setting of
[GilyenSuLowWiebe2019]. The theorem `paperEndpointNext` assembles these three guarantees into
`PaperEndpointNext`.

## Main statements

* `paper_application_window_flat`: Certifies the flat center of the chosen window.
* `paper_response_robustness`: Bounds polynomial responses of Hermitian contractions.
* `paperEndpointNext`: Combines all three endpoint clauses.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Polynomial
open scoped Classical BigOperators
open scoped Matrix.Norms.L2Operator

open Qatlib

/-- For ε and δ in (0, 1), the chosen application window has `DolphFlatCenter` with accuracy ε
and center parameter 1 − δ. -/
theorem paper_application_window_flat {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphFlatCenter
      (paperApplicationWindow ε δ) ε (1 - δ) := by
  exact Qatlib.Concepts.QsvtCore.ApproxToolkit.dolphWindow_degree_budget hε
    (le_of_lt hε1) δ hδ hδ1

/-- For Hermitian contractions A and B, bounds the polynomial functional calculus difference by
the printed robustness factor times the polynomial response modulus at their distance. -/
theorem paper_response_robustness {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) (p : Polynomial ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖hermitianFunction A hA (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      hermitianFunction B hB (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      modulusRobustnessFactor ‖A - B‖ *
        Qatlib.Concepts.QsvtCore.ApproxToolkit.polynomialResponseModulus p ‖A - B‖ :=
  Qatlib.Concepts.QsvtCore.ApproxToolkit.hermitianFunction_polynomial_printed
    A B hA hB hA1 hB1 p

/-- Establishes the conjunction of odd word ledger accounting, application window flatness, and
Hermitian polynomial response robustness. See [GilyenSuLowWiebe2019]. -/
theorem paperEndpointNext : PaperEndpointNext := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ
    exact Qatlib.Concepts.QsvtCore.PhaseExistence.paper_odd_word_ledger Φ
  · intro ε δ hε hε1 hδ hδ1
    exact paper_application_window_flat hε hε1 hδ hδ1
  · intro I _ _ A B hA hB p hA1 hB1
    exact paper_response_robustness A B hA hB p hA1 hB1

end Qatlib.Papers.QSingValue19.AlgorithmApps
