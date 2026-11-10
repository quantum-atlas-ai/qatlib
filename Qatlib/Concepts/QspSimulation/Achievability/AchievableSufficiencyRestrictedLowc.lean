/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxTransfer
import Qatlib.Concepts.QsvtCore.PolyApprox.EvenIntervalSOS
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxReal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PolyApprox

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib
section Helpers

end Helpers

theorem achievableSufficiencyRestricted : AchievableSufficiencyRestricted := by
  intro d A Qt hd hp hAeven hQtodd hAdeg hQtdeg hcond hAone
  exact achievableSufficiencyCore d A Qt hd hp hAeven hQtodd hAdeg hQtdeg hcond

end Qatlib.Concepts.QspSimulation.Achievability
