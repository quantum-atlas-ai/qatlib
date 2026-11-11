/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.Policy

/-!
# Dynamic programming bounds for erasure survival

This module computes the mass of masks that avoid complete erasure and propagates continuation
bounds through a noise step. Induction on `ErasurePolicy` then bounds its survival by
`bestProduct`, giving the dynamic-programming comparison used in adaptive spacetime estimates
[BhartiHaugTanggara2026].

## Main statements

* `noncomplete_mass`: The noncomplete-erasure mass is 1 - pⁿ.
* `noise_success_le`: A noise step multiplies a uniform continuation bound by 1 - pⁿ.
* `execute_le_best`: Every policy is bounded by the optimal deterministic survival product.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators

namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- The total probability of masks other than the all-true mask is `1 - p ^ n`. -/
theorem noncomplete_mass (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    ∑ mask ∈ Finset.univ.erase (fun _ : Fin n => true), erasureMask n p hp mask =
      (↑(1-p^n : ℝ≥0) : ℝ≥0∞) := by
  have hs : ∑ mask : Fin n → Bool, erasureMask n p hp mask = 1 := by
    simpa only [tsum_fintype] using (erasureMask n p hp).tsum_coe
  have he := Finset.sum_erase_add Finset.univ (erasureMask n p hp)
    (Finset.mem_univ (fun _ : Fin n => true))
  rw [hs, erasureMask_complete] at he
  have hh := ENNReal.eq_sub_of_add_eq (ENNReal.pow_ne_top ENNReal.coe_ne_top) he
  simpa only [ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_pow] using hh

/-- If all continuations have true-outcome probability at most `B`, a width-`n` noise step that
fails on complete erasure has success probability at most `(1 - p ^ n) * B`. -/
theorem noise_success_le {R : Type*} (n : ℕ) (p : ℝ≥0) (hp : p ≤ 1)
    (observe : (Fin n → Bool) → PMF R) (next : (Fin n → Bool) → R → PMF Bool)
    (B : ℝ≥0) (h : ∀ mask r, next mask r true ≤ B) :
    ((erasureMask n p hp).bind (fun mask =>
      if mask = (fun _ => true) then PMF.pure false
      else (observe mask).bind (next mask))) true ≤ ↑((1-p^n)*B) := by
  classical
  rw [PMF.bind_apply, tsum_fintype]
  have hz : (erasureMask n p hp (fun _ => true) *
      (if (fun _ : Fin n => true) = (fun _ => true) then PMF.pure false
      else (observe (fun _ => true)).bind (next (fun _ => true))) true) = 0 := by simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (fun _ : Fin n => true)), hz, add_zero]
  calc
    _ ≤ ∑ mask ∈ Finset.univ.erase (fun _ : Fin n => true),
        erasureMask n p hp mask * (B : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro mask hm
      have hne := (Finset.mem_erase.mp hm).1
      rw [if_neg hne]
      exact mul_le_mul_right (bind_success_le (observe mask) (next mask) B (h mask)) _
    _ = _ := by rw [← Finset.sum_mul, noncomplete_mass, ENNReal.coe_mul]

/-- The survival probability of any erasure policy with `S` steps and budget `C` is at most
`bestProduct p S C`. -/
theorem execute_le_best {R : Type*} (p : ℝ≥0) (hp : p ≤ 1) {S C : ℕ}
    (policy : ErasurePolicy R S C) : execute p hp policy true ≤ (bestProduct p S C : ℝ≥0∞) := by
  induction policy with
  | done => simp [execute, bestProduct]
  | random draw next ih =>
    exact bind_success_le draw (fun r => execute p hp (next r)) _ ih
  | @noise steps budget width observe next ih =>
    apply (noise_success_le width.val p hp observe (fun mask r => execute p hp (next mask r))
      (bestProduct p steps (budget-width.val)) ih).trans
    exact_mod_cast step_le_best p steps budget width

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
