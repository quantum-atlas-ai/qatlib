/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.PrepQueries.NativePromise
import Qatlib.Concepts.QueryComplexity.PrepQueries.NativeQueries

/-!
# Lower bounds from source preparation

This module packages lower bounds for experiments that distinguish a reference source from a
nearby prepared source. It relates source overlap or source distance to the number of oracle
calls needed for a two thirds versus one third Born probability separation. See
[MontanaroPallister2016].

## Main statements

* `actual_source_overlap_contract`: Under the stated probability separation, the base and
  prepared states are normalized with squared overlap `1 - eps`, and the number of calls is at
  least `1 / (12 * √eps)`.
* `actual_source_distance_contract`: For source parameter `(delta / 2) ^ 2` and the stated
  probability separation, the source states are within distance `delta` and the number of calls
  is at least `1 / (6 * delta)`.

## References

* [Montanaro and Pallister, 2016][MontanaroPallister2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Papers.QuantumFEM15.PrepLower
open Qatlib.Concepts.QueryComplexity.PrepQueries

/-- Under the stated probability separation, the base and prepared states are normalized with
squared overlap `1 - eps`, and the number of calls is at least `1 / (12 * √eps)`. See
[MontanaroPallister2016]. -/
theorem actual_source_overlap_contract {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (eps : ℝ) (he0 : 0<eps) (he1 : eps≤1)
    (inverse : ℕ→Bool) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) (hx : ‖x‖=1)
    (w : W) (S : Finset (W×Bool))
    (hyes : 2/3 ≤ born S (reference U t x))
    (hno : born S (experiment U eps inverse t x) ≤ 1/3) :
    ‖baseState w‖=1 ∧ ‖preparedState eps w‖=1 ∧
    Complex.normSq (inner ℂ (baseState w) (preparedState eps w))=1-eps ∧
    1/(12*Real.sqrt eps)≤(t:ℝ) := by
  exact ⟨baseState_norm w,preparedState_norm eps he0.le he1 w,
    preparedState_fidelity eps he1 w,
    actual_preparation_query_lower_bound U eps he0 he1 inverse t x hx S hyes hno⟩

/-- For source parameter `(delta / 2) ^ 2` and the stated probability separation, the source
states are within distance `delta` and the number of calls is at least `1 / (6 * delta)`.
See [MontanaroPallister2016]. -/
theorem actual_source_distance_contract {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (U : ℕ→Matrix.unitaryGroup (W×Bool) ℂ) (delta : ℝ) (hd0 : 0<delta) (hd1 : delta≤1)
    (inverse : ℕ→Bool) (t : ℕ) (x : EuclideanSpace ℂ (W×Bool)) (hx : ‖x‖=1)
    (w : W) (S : Finset (W×Bool))
    (hyes : 2/3 ≤ born S (reference U t x))
    (hno : born S (experiment U ((delta/2)^2) inverse t x) ≤ 1/3) :
    ‖baseState w-preparedState ((delta/2)^2) w‖≤delta ∧
      1/(6*delta)≤(t:ℝ) := by
  have he0 : 0<(delta/2)^2 := sq_pos_of_pos (by positivity)
  have he1 : (delta/2)^2≤1 := by nlinarith
  have hs : Real.sqrt ((delta/2)^2)=delta/2 := Real.sqrt_sq (by positivity)
  have hp := preparedState_distance ((delta/2)^2) he0.le he1 w
  have hq := actual_preparation_query_lower_bound U ((delta/2)^2) he0 he1 inverse t x hx S hyes hno
  rw [hs] at hp hq
  constructor
  · nlinarith
  · convert hq using 1; ring
end Qatlib.Papers.QuantumFEM15.PrepLower
