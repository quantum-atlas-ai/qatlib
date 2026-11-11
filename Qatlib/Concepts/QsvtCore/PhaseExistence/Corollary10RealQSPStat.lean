/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed

/-!
# Statement of real QSP completion

`Corollary10RealQSP` specifies a complex completion of a bounded real polynomial with positive
exact degree and matching parity. The complex polynomial has the same degree, satisfies the
interval, exterior, and even-degree imaginary-axis inequalities, and obeys a coefficientwise
identity fixing its real part.

This is the completion statement associated with Corollary 10 of [GilyenSuLowWiebe2019].

## Main statements

* `Corollary10RealQSP`: defines the real-to-complex polynomial completion proposition.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial

/-- The proposition that a real polynomial of positive exact degree d, parity d, and magnitude
at most one on [-1, 1] possesses a complex completion of the same degree and parity
satisfying the complex QSP inequalities. The identity `P + conjugatePolynomial P = C (2 : ℂ)
* Pt.map Complex.ofRealHom` fixes its real part [Gilyén et al., Corollary
10][GilyenSuLowWiebe2019]. -/
def Corollary10RealQSP : Prop :=
  ∀ (Pt : Polynomial ℝ) (d : ℕ), 0 < d → Pt.natDegree = d →
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d Pt →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pt.eval x| ≤ 1) →
    ∃ P : Polynomial ℂ,
      P.natDegree = d ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity d P ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1) ∧
      (∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
        1 ≤ Complex.normSq (P.eval (Complex.ofReal x))) ∧
      (d % 2 = 0 → ∀ y : ℝ,
        1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))) ∧
      P + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial P =
        C (2 : ℂ) * Pt.map Complex.ofRealHom

end Qatlib.Concepts.QsvtCore.PhaseExistence
