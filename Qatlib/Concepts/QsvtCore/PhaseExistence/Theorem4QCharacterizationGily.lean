/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4QCharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality

/-!
# Characterization of the lower response polynomial

`theorem4QCharacterization` proves the criterion for a complex polynomial to be the lower
component of a `CompletedPair`. Its interval bound is weighted by `1 - x^2`, and odd length
additionally requires a weighted lower bound on the imaginary axis. See [GilyenSuLowWiebe2019].

## Main statements

* `theorem4QCharacterization`: characterize existence of a completed upper partner.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

/-- A polynomial has a completed upper partner exactly when it satisfies the prescribed degree,
parity, weighted interval bound, and odd-length imaginary-axis bound. This is the
lower-polynomial criterion of [Gilyén et al., Theorem 4][GilyenSuLowWiebe2019]. -/
theorem theorem4QCharacterization : Theorem4QCharacterization := by
  intro k Q
  refine ⟨?_, ?_⟩
  · rintro ⟨P, h⟩
    exact ⟨h.degreeQ, h.parityQ, fun x hx => h.scaled_normSq_eval_le_one hx,
      fun hodd y => h.one_le_scaled_normSq_eval_imag hodd y⟩
  · rintro ⟨hdeg, hpar, hin, himag⟩
    exact exists_completedPair_of_q_conditions Q k hdeg hpar hin himag

end Qatlib.Concepts.QsvtCore.PhaseExistence
