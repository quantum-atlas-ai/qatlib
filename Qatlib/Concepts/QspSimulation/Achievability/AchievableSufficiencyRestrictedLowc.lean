/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxTransfer
import Qatlib.Concepts.QsvtCore.PolyApprox.EvenIntervalSOS
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxReal

/-!
# Restricted QSP sufficiency

This module proves the restricted sufficiency statement for an even real polynomial and an odd
real polynomial whose weighted squared sum is bounded by one on the interval from minus one to
one. The result transfers the phase-existence construction into the repository amplitude
convention associated with QSP [LowChuang2017].

## Main statements

* `achievableSufficiencyRestricted` realizes the prescribed polynomial amplitude under the
  parity, degree, interval-bound, and endpoint-normalization hypotheses of
  `AchievableSufficiencyRestricted`.

## References

* [Low and Chuang, 2017][LowChuang2017], *Optimal Hamiltonian Simulation by Quantum Signal
  Processing*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PolyApprox

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib
open Qatlib
section Helpers

end Helpers

/-- Establishes `AchievableSufficiencyRestricted`, realizing the prescribed even-polynomial plus
imaginary square-root-weighted odd-polynomial amplitude by repository QSP phases under its
degree, parity, interval-bound, and normalization hypotheses. -/
theorem achievableSufficiencyRestricted : AchievableSufficiencyRestricted := by
  intro d A Qt hd hp hAeven hQtodd hAdeg hQtdeg hcond hAone
  exact achievableSufficiencyCore d A Qt hd hp hAeven hQtodd hAdeg hQtdeg hcond

end Qatlib.Concepts.QspSimulation.Achievability
