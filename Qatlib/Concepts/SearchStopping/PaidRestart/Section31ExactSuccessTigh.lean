/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.SearchStopping.PaidRestart.Section31ExactSuccessStat
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem quarterDensity_success (hN : 0 < Fintype.card I) (A : Finset I)
    (hquarter : 4 * A.card = Fintype.card I) :
    MeasureProb (GroverState A 1) A = 1 := by
  have hNr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hN
  have hqr : (4 : ℝ) * A.card = Fintype.card I := by exact_mod_cast hquarter
  have hsin : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  have hθ : (Real.sin (Real.pi / 6)) ^ 2 = (A.card : ℝ) / Fintype.card I := by
    rw [hsin, eq_div_iff hNr.ne']
    nlinarith
  have hs : Real.sin (Real.pi / 6) ≠ 0 := by rw [hsin]; norm_num
  have hc : Real.cos (Real.pi / 6) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).ne'
  rw [measureProb_groverState hN A (Real.pi / 6) hθ hs hc]
  have ha : (2 * (1 : ℝ) + 1) * (Real.pi / 6) = Real.pi / 2 := by ring
  rw [Nat.cast_one, ha, Real.sin_pi_div_two]
  norm_num

theorem quarterDensity_searchClaim {m : ℕ} (hm : 0 < m) (hquarter : 4 * m = Fintype.card I) :
    QuarterDensitySearchClaim I m := by
  have hN : 0 < Fintype.card I := by omega
  refine ⟨by norm_num, fun A => setOracle_unitary A.val,
    GroverCircuit I 1, Uniform I, isUnitaryCircuit_groverCircuit hN 1,
    normalized_uniform hN, (queryCount_groverCircuit 1).le, ?_⟩
  intro A
  change 1 - (0 : ℝ) ≤ MeasureProb (GroverState A.val 1) A.val
  rw [quarterDensity_success hN A.val (by simpa [A.property] using hquarter)]
  norm_num

theorem section3_1ExactSuccess : Section3_1ExactSuccess := by
  intro I _ _ m hm hquarter
  exact quarterDensity_searchClaim hm hquarter

end Qatlib.Concepts.SearchStopping.PaidRestart
