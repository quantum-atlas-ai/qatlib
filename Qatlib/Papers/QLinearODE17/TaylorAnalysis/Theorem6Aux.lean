/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux

/-!
# Initial block of a Taylor-system solution

The zeroth row of `taylorStepMatrix` fixes the initial block to `x_in`. The theorem
`taylor_initial_error_zero` identifies that block with the reference evolution at time zero. See
[BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylor_initial_block`: Every solution of the stated Taylor system has initial time block
  equal to `x_in`.
* `taylor_initial_error_zero`: At time zero, the reference ODE solution equals the initial block
  of every solution of the stated Taylor system.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.TimeOrdered

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
set_option warningAsError false

/-- Every solution of the stated Taylor system has initial time block equal to `x_in`. -/
theorem taylor_initial_block {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (M : Matrix N N ℂ) (h : ℝ) (x_in b : QState N)
    (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrix m k p M *ᵥ x = taylorRHS m k p h x_in b) :
    taylorBlock x (taylorTimeLabel m k p 0 (Nat.zero_le m)) = x_in := by
  ext n
  let r : Fin (m * (k + 1) + p + 1) × N :=
    (taylorTimeLabel m k p 0 (Nat.zero_le m), n)
  have hrow (c : Fin (m * (k + 1) + p + 1) × N) :
      taylorStepMatrix m k p M r c = (1 : Matrix _ _ ℂ) r c := by
    by_cases hc : c.1.val = 0
    · have hlabel : r.1 = c.1 := by
        apply Fin.ext
        simpa [r, taylorTimeLabel] using! hc.symm
      rw [taylorStepMatrix_same_label m k p M r c hlabel]
      simp [Matrix.one_apply, Prod.ext_iff, hlabel]
    · have hlt : r.1 < c.1 := by
        simpa [r, taylorTimeLabel] using! Nat.pos_of_ne_zero hc
      rw [taylorStepMatrix_above m k p M r c hlt]
      have hne : r ≠ c := by intro he; subst c; exact lt_irrefl _ hlt
      simp [hne]
  have he := congrFun hx r
  have hleft : (taylorStepMatrix m k p M *ᵥ x) r = x r := by
    change (∑ c, taylorStepMatrix m k p M r c * x c) = x r
    simp_rw [hrow]
    exact congrFun (Matrix.one_mulVec x) r
  rw [hleft] at he
  simpa [r, taylorRHS, taylorTimeLabel, taylorBlock] using! he

/-- At time zero, the reference ODE solution equals the initial block of every solution of the
stated Taylor system. -/
theorem taylor_initial_error_zero {N : Type} [Fintype N] [DecidableEq N]
    (m k p : ℕ) (A M : Matrix N N ℂ) (h : ℝ) (x_in b : QState N)
    (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (hx : taylorStepMatrix m k p M *ᵥ x = taylorRHS m k p h x_in b) :
    taylorODESolution A b x_in 0 =
      taylorBlock x (taylorTimeLabel m k p 0 (Nat.zero_le m)) := by
  rw [taylor_initial_block m k p M h x_in b x hx]
  exact orderedForcedSolution_self _ _ _ _

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
