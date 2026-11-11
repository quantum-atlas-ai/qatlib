/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Circuit

/-!
# Promise-gap inequalities for circuit-derived networks

Verifies the controlled bit flip's unitarity and the normalized range of the Figure 6 value
`p0`. It then proves the scalar threshold inequalities used in the circuit-to-network reduction
underlying Corollary 4.1 of [AradLandau2010].

An approximation to `Δ * p0` with error strictly below `Δ / 6` separates the promised cases `p0
≤ 1 / 3` and `p0 ≥ 2 / 3` at threshold `Δ / 2`.

## Main statements

* `fig6_gate_unitary`: proves unitarity of the controlled bit-flip permutation matrix.
* `corollary4_1_promise_decision`: establishes threshold separation.
* `corollary4_1_decides`: combines separation with the promise.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor41

open Qatlib.Papers.TensorNetwork08.MainResults.Circuit
open Qatlib.Foundations.TableAccess.ReversibleTable

/-- The permutation matrix implementing the controlled bit flip in the Figure 6 construction is
unitary. See [AradLandau2010]. -/
theorem fig6_gate_unitary {n : ℕ} (a : Fin n) :
    permMatrix (cnotFun a) ∈ Matrix.unitaryGroup (Reg n × Bool) ℂ :=
  permMatrix_unitary (cnotFun_involutive a)

/-- If the zero-input column is normalized, then `p0 Q a` lies between zero and one. -/
theorem fig6_value_mem_unit {n : ℕ} (Q : Matrix (Reg n) (Reg n) ℂ) (a : Fin n)
    (hQ : ∑ s : Reg n, ‖Q s (zeroReg n)‖ ^ 2 = 1) :
    0 ≤ p0 Q a ∧ p0 Q a ≤ 1 :=
  ⟨p0_nonneg Q a, p0_le_one a hQ⟩

/-- For positive `Δ`, an approximation to `Δ * p0` with error below `Δ / 6` lies above `Δ / 2`
when `p0 ≥ 2 / 3` and below it when `p0 ≤ 1 / 3`. -/
theorem corollary4_1_promise_decision
    (Δ p0 r : ℝ) (hΔ : 0 < Δ) (happ : |Δ * p0 - r| < Δ / 6) :
    (2 / 3 ≤ p0 → Δ / 2 < r) ∧ (p0 ≤ 1 / 3 → r < Δ / 2) := by
  obtain ⟨hlow, hhigh⟩ := abs_lt.1 happ
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- Under the stated approximation bound and promise on `p0`, thresholding `r` at `Δ / 2`
identifies the corresponding high or low branch. See [AradLandau2010]. -/
theorem corollary4_1_decides
    (Δ p0 r : ℝ) (hΔ : 0 < Δ) (happ : |Δ * p0 - r| < Δ / 6)
    (hpromise : p0 ≤ 1 / 3 ∨ 2 / 3 ≤ p0) :
    (r > Δ / 2 ∧ 2 / 3 ≤ p0) ∨ (r ≤ Δ / 2 ∧ p0 ≤ 1 / 3) := by
  obtain ⟨hyes, hno⟩ := corollary4_1_promise_decision Δ p0 r hΔ happ
  rcases hpromise with h | h
  · right
    exact ⟨le_of_lt (hno h), h⟩
  · left
    exact ⟨hyes h, h⟩

end Qatlib.Papers.TensorNetwork08.MainResults.Cor41
