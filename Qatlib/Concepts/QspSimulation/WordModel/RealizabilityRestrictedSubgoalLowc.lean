/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.RealizabilityRestrictedSubgoalStat
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs

namespace Qatlib.Concepts.QspSimulation.WordModel

open Qatlib

theorem phaseRotation_zero : PhaseRotation (0 : ℝ) = 1 := by
  ext a b
  rw [phaseRotation_apply, Matrix.one_apply]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab]
    by_cases ha : a = 0
    · rw [if_pos ha]
      simp
    · rw [if_neg ha]
      simp
  · rw [if_neg hab, if_neg hab]

theorem qspWord_zero_zero (x : ℝ) :
    QSPWord [0, 0] x = SignalMatrix x * SignalMatrix x := by
  rw [qspWord_cons, qspWord_cons, qspWord_nil, phaseRotation_zero, mul_one, mul_one]

theorem realizabilityRestrictedSubgoal : RealizabilityRestrictedSubgoal := by
  refine ⟨[0, 0], rfl, ?_⟩
  intro x hx1 hx2
  have hy2 : ((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ))
      = 1 - (x : ℂ) ^ 2 := qsp_sqrt_mul_self hx1 hx2
  calc (QSPWord [0, 0] x) 0 0 = (SignalMatrix x * SignalMatrix x) 0 0 := by
        rw [qspWord_zero_zero]
    _ = SignalMatrix x 0 0 * SignalMatrix x 0 0
        + SignalMatrix x 0 1 * SignalMatrix x 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]
    _ = (x : ℂ) * (x : ℂ) + ((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I
          * (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I) := by
        rw [signalMatrix_apply, signalMatrix_apply, signalMatrix_apply]
        rw [if_pos rfl, if_neg (by decide : ¬((0 : Fin 2) = 1)),
          if_neg (by decide : ¬((1 : Fin 2) = 0))]
    _ = ((2 * x ^ 2 - 1 : ℝ) : ℂ) := by
        have h1 : (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
            * (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
            = -((((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))) := by
          rw [show (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
              * (((Real.sqrt (1 - x ^ 2) : ℂ)) * Complex.I)
            = (((Real.sqrt (1 - x ^ 2) : ℂ)) * ((Real.sqrt (1 - x ^ 2) : ℂ)))
              * (Complex.I * Complex.I) from by ring, Complex.I_mul_I]
          ring
        rw [h1, hy2]
        push_cast
        ring

end Qatlib.Concepts.QspSimulation.WordModel
