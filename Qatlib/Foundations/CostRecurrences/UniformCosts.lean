/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.CostRecurrences.UniformCosts

theorem cost_induction_closed (P bc : ℕ → ℝ) (c C θ : ℝ)
    (hbc : ∀ N, 0 ≤ bc N)
    (_hθ1 : θ < 1) (hC0 : 0 ≤ C)
    (hC : c ≤ C * (1 - θ))
    (hbase : ∀ N, N < 2 → P N ≤ C * bc N)
    (hstep : ∀ N, 2 ≤ N →
      P N ≤ (∑ p ∈ (N - 1).primeFactors, P p) + c * bc N)
    (hshare : ∀ N, 2 ≤ N →
      (∑ p ∈ (N - 1).primeFactors, bc p) ≤ θ * bc N) :
    ∀ N, P N ≤ C * bc N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · exact hbase N hlt
    · have hstepN := hstep N hge
      have hsum : (∑ p ∈ (N - 1).primeFactors, P p)
          ≤ C * (∑ p ∈ (N - 1).primeFactors, bc p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        have hpdvd : p ∣ N - 1 := (Nat.mem_primeFactors.mp hp).2.1
        have hne : N - 1 ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
        have hple : p ≤ N - 1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hpdvd
        exact ih p (by omega)
      have hshareN := hshare N hge
      have hCsum : C * (∑ p ∈ (N - 1).primeFactors, bc p) ≤ C * (θ * bc N) :=
        mul_le_mul_of_nonneg_left hshareN hC0
      calc P N ≤ (∑ p ∈ (N - 1).primeFactors, P p) + c * bc N := hstepN
        _ ≤ C * (∑ p ∈ (N - 1).primeFactors, bc p) + c * bc N := by linarith
        _ ≤ C * (θ * bc N) + c * bc N := by linarith
        _ = (C * θ + c) * bc N := by ring
        _ ≤ C * bc N := by
            apply mul_le_mul_of_nonneg_right _ (hbc N)
            nlinarith [hC]

theorem card_primeFactors_le_log2 (M : ℕ) (hM : 2 ≤ M) :
    M.primeFactors.card ≤ Nat.log 2 M := by
  have h2 : 2 ^ M.primeFactors.card ≤ ∏ p ∈ M.primeFactors, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)
  have hprod : (∏ p ∈ M.primeFactors, p) ≤ M :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd M)
  exact Nat.le_log_of_pow_le (b := 2) (x := M.primeFactors.card)
    (y := M) (by norm_num) (h2.trans hprod)

end Qatlib.Foundations.CostRecurrences.UniformCosts
