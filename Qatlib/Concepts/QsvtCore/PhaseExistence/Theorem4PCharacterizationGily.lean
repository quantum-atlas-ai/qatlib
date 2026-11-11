/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4PCharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.ComplexPolynomial
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality

/-!
# Characterization of the upper response polynomial

`theorem4PCharacterization` proves the criterion for a complex polynomial to occur as the upper
component of a `CompletedPair`. The conditions comprise degree and parity constraints, a unit
bound on the real interval, a reverse bound outside its interior, and an imaginary-axis bound
for even length. See [GilyenSuLowWiebe2019].

## Main statements

* `theorem4PCharacterization`: characterize existence of a completed lower partner.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- A polynomial has a completed lower partner exactly when it satisfies the stated degree,
parity, real-axis bounds, and even-length imaginary-axis bound. This is the upper-polynomial
criterion of [Gilyén et al., Theorem 4][GilyenSuLowWiebe2019]. -/
theorem theorem4PCharacterization : Theorem4PCharacterization := by
  intro k P
  refine ⟨?_, ?_⟩
  · rintro ⟨Q, h⟩
    exact ⟨h.degreeP, h.parityP, fun x hx => h.normSq_eval_le_one hx,
      fun x hx => h.one_le_normSq_eval hx,
      fun heven y => h.one_le_normSq_eval_imag heven y⟩
  · rintro ⟨hdeg, hpar, hin, hout, himag⟩
    exact exists_completedPair_of_cor8_conditions P k hdeg hpar hin hout himag

end Qatlib.Concepts.QsvtCore.PhaseExistence
