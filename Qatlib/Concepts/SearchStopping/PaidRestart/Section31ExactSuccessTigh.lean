/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.SearchStopping.PaidRestart.Section31ExactSuccessStat
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Exact success after one quarter-density Grover step

Proves that one Grover iteration succeeds with probability one when exactly one quarter of the
addresses are marked. `quarterDensity_searchClaim` packages this as an exact fixed-space query
upper bound, and `section3_1ExactSuccess` establishes the corresponding statement. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `quarterDensity_success`: On a nonempty finite space with one quarter of its addresses marked,
  one Grover iteration has marked-set success probability one.
* `section3_1ExactSuccess`: Establishes `Section3_1ExactSuccess`, the exact one-query search
  result at quarter marked density.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.SearchStopping.PaidRestart

open Qatlib.Concepts.SearchStopping.KnownCount

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- On a nonempty finite space with one quarter of its addresses marked, one Grover iteration
has marked-set success probability one. -/
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

/-- Positive marked count `m` with `4 * m = Fintype.card I` gives the exact one-query search
bound `QuarterDensitySearchClaim I m`. -/
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

/-- Establishes `Section3_1ExactSuccess`, the exact one-query search result at quarter marked
density. See [BoyerEtAl1998]. -/
theorem section3_1ExactSuccess : Section3_1ExactSuccess := by
  intro I _ _ m hm hquarter
  exact quarterDensity_searchClaim hm hquarter

end Qatlib.Concepts.SearchStopping.PaidRestart
