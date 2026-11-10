/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4PCharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.ComplexPolynomial
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality
set_option warningAsError false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

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
