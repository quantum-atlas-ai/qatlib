/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartStationaritySubgoalStat
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Qatlib.Concepts.SearchStopping.KnownCount

theorem restartExpectedIterations_deriv (θ j : ℝ)
    (hs : Real.sin ((2 * j + 1) * θ) ≠ 0) :
    deriv (restartExpectedIterations θ) j =
      (Real.sin ((2 * j + 1) * θ) - 4 * θ * j * Real.cos ((2 * j + 1) * θ)) /
        Real.sin ((2 * j + 1) * θ)^3 := by
  have haff : HasDerivAt (fun x : ℝ => (2 * x + 1) * θ) (2 * θ) j := by
    simpa using (((hasDerivAt_id j).const_mul 2).add_const 1).mul_const θ
  have hsin := (Real.hasDerivAt_sin ((2 * j + 1) * θ)).comp j haff
  have hd := ((hasDerivAt_id j).div (hsin.pow 2) (pow_ne_zero 2 hs)).deriv
  change deriv (id / (Real.sin ∘ (fun x : ℝ => (2 * x + 1) * θ))^2) j = _
  rw [hd]
  dsimp only [Function.comp_apply, id_eq, Pi.pow_apply]
  field_simp [hs]
  ring

theorem section3RestartStationaritySubgoal : Section3RestartStationaritySubgoal := by
  intro θ hθ hθupper j hs
  have hctheta : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθupper⟩
  rw [restartExpectedIterations_deriv θ j hs]
  have hs3 : Real.sin ((2 * j + 1) * θ)^3 ≠ 0 := pow_ne_zero 3 hs
  simp only [div_eq_zero_iff, hs3, or_false, sub_eq_zero]
  constructor
  · intro he
    have hc : Real.cos ((2 * j + 1) * θ) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at he
      exact hs he
    rw [Real.tan_eq_sin_div_cos]
    exact (div_eq_iff hc).2 he
  · intro he
    have hc : Real.cos ((2 * j + 1) * θ) ≠ 0 := by
      intro hz
      rw [Real.tan_eq_sin_div_cos, hz, div_zero] at he
      have hj : j = 0 := (mul_eq_zero.mp (show (4 * θ) * j = 0 by linarith)).resolve_left
        (ne_of_gt (by positivity : 0 < 4 * θ))
      rw [hj] at hz
      simp only [mul_zero, zero_add, one_mul] at hz
      exact hctheta.ne' hz
    rw [Real.tan_eq_sin_div_cos] at he
    exact (div_eq_iff hc).1 he

end Qatlib.Concepts.SearchStopping.RestartLaw
