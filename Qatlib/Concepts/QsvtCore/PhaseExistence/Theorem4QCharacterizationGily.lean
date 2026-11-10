/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4QCharacterizationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.PairCompletionDuality
set_option warningAsError false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis

theorem theorem4QCharacterization : Theorem4QCharacterization := by
  intro k Q
  refine ⟨?_, ?_⟩
  · rintro ⟨P, h⟩
    exact ⟨h.degreeQ, h.parityQ, fun x hx => h.scaled_normSq_eval_le_one hx,
      fun hodd y => h.one_le_scaled_normSq_eval_imag hodd y⟩
  · rintro ⟨hdeg, hpar, hin, himag⟩
    exact exists_completedPair_of_q_conditions Q k hdeg hpar hin himag

end Qatlib.Concepts.QsvtCore.PhaseExistence
