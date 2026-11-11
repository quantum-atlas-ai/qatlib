/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BoolMatMult11.MainResults.SearchCore
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Boolean matrix multiplication upper bound (arXiv:1112.5855v2, Section 4.1)

The algorithm `BMM(A, B)` alternates between `GroverSearch(t)` for a witness
index `k` and `AllGC` on the witness graph.  The paper's proof of Theorem 4.1 is
a two-part cost ledger:

* successful rounds: the `j`-th success has search parameter
  `t_j ≥ T - j + 1`, hence `∑_j √(n/t_j) ≤ 2√(nT)`; the Cauchy--Schwarz step
  `∑_j √(λ_j) ≤ √(Tℓ)` handles the output-sensitive part;
* unsuccessful rounds: `t` halves, so there are at most `log₂ n + 1` of them,
  each costing at most `√n (√n + √ℓ)` because `t ≥ 1` and `m_i ≤ ℓ`.

Both ledgers are formalized here, together with the final `O(n√ℓ)` arithmetic.
The per-round subroutine costs are the paper's Theorem 3.1 bounds, already
formalized in `MainResults.GraphCollision`.
-/

namespace Qatlib.Papers.BoolMatMult11.MainResults.MatrixRounding

open scoped BigOperators
open Qatlib.Papers.BoolMatMult11.MainResults.SearchCore

set_option autoImplicit false

/-- Cauchy--Schwarz step of Theorem 4.1: for `∑_j λ_j = ℓ`,
`∑_j √λ_j ≤ √(Tℓ)`. -/
theorem sum_sqrt_lam_le {T ℓ : ℕ} (lam : ℕ → ℕ)
    (hsum : ∑ j ∈ Finset.range T, lam j = ℓ) :
    (∑ j ∈ Finset.range T, Real.sqrt (lam j : ℝ)) ≤
      Real.sqrt (T : ℝ) * Real.sqrt (ℓ : ℝ) := by
  have h := Real.sum_sqrt_mul_sqrt_le (s := Finset.range T) (f := fun j => (lam j : ℝ))
    (g := fun _ => (1 : ℝ)) (fun j => Nat.cast_nonneg _) (fun _ => zero_le_one)
  have hcast : (∑ j ∈ Finset.range T, (lam j : ℝ)) = (ℓ : ℝ) := by
    rw [← Nat.cast_sum, hsum]
  simpa [hcast, mul_comm] using h

/-- Successful rounds of `BMM`, equation (1)--(3) of the paper: substituting
`GC(n, m_j) ≤ √n + √ℓ` and `GC_all(n, m_j, λ_j) ≤ √(nλ_j) + √ℓ` with
`T ≤ min{n, ℓ}` gives at most `6n√ℓ`. -/
theorem bmm_success_cost_le {n ℓ T : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hTn : T ≤ n) (hTℓ : T ≤ ℓ) (ts : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < T → ts (j + 1) + 1 ≤ ts j) (hlast : 1 ≤ ts (T - 1))
    (lam : ℕ → ℕ) (hlam : ∑ j ∈ Finset.range T, lam j = ℓ) :
    (∑ j ∈ Finset.range T,
        Real.sqrt ((n : ℝ) / (ts j : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) +
      (∑ j ∈ Finset.range T,
        (Real.sqrt ((n : ℝ) * (lam j : ℝ)) + Real.sqrt (ℓ : ℝ))) ≤
      6 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrootN : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrootL : (0 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
  have hsp := success_phase_cost (N := n) ts hstep hlast
  have hsp' : (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) / (ts j : ℝ))) ≤
      2 * Real.sqrt ((n : ℝ) * T) := by
    simpa [mul_comm] using hsp
  have hCS := sum_sqrt_lam_le lam hlam
  have hfirst :
      (∑ j ∈ Finset.range T,
          Real.sqrt ((n : ℝ) / (ts j : ℝ)) *
            (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) =
        (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) / (ts j : ℝ))) *
          (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) := by
    rw [Finset.sum_mul]
  have hsumNlam :
      (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) * (lam j : ℝ))) =
        Real.sqrt (n : ℝ) * ∑ j ∈ Finset.range T, Real.sqrt (lam j : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.sqrt_mul hn']
  have hsecond :
      (∑ j ∈ Finset.range T,
          (Real.sqrt ((n : ℝ) * (lam j : ℝ)) + Real.sqrt (ℓ : ℝ))) =
        (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) * (lam j : ℝ))) +
          (T : ℝ) * Real.sqrt (ℓ : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- The four numeric pieces of equations (4)--(5).
  have hA : Real.sqrt ((n : ℝ) * T) * Real.sqrt (n : ℝ) ≤
      (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have hmul : Real.sqrt ((n : ℝ) * T) * Real.sqrt (n : ℝ) =
        Real.sqrt ((n : ℝ) * T * n) :=
      Eq.symm (Real.sqrt_mul (x := (n : ℝ) * T) (y := (n : ℝ)) (by positivity))
    rw [hmul]
    have hle : (n : ℝ) * T * n ≤ (n : ℝ) * n * ℓ := by
      have hTℓ' : (T : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hTℓ
      have h1 : (n : ℝ) * T ≤ (n : ℝ) * ℓ := mul_le_mul_of_nonneg_left hTℓ' hn'
      have h2 : (n : ℝ) * T * n ≤ (n : ℝ) * ℓ * n :=
        mul_le_mul_of_nonneg_right h1 hn'
      calc
        (n : ℝ) * T * n ≤ (n : ℝ) * ℓ * n := h2
        _ = (n : ℝ) * n * ℓ := by ring
    have hsq : Real.sqrt ((n : ℝ) * n * ℓ) = (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
      rw [show (n : ℝ) * n * ℓ = (n : ℝ) ^ 2 * ℓ by ring, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hn']
    rw [← hsq]
    exact Real.sqrt_le_sqrt hle
  have hB : Real.sqrt ((n : ℝ) * T) * Real.sqrt (ℓ : ℝ) ≤
      (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have hroot : Real.sqrt ((n : ℝ) * T) ≤ (n : ℝ) := by
      have hT' : (T : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTn
      have hle : (n : ℝ) * T ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hT' hn'
      have := Real.sqrt_le_sqrt hle
      rwa [show (n : ℝ) * n = (n : ℝ) ^ 2 by ring, Real.sqrt_sq hn'] at this
    exact mul_le_mul_of_nonneg_right hroot hrootL
  have hCn : Real.sqrt (n : ℝ) * Real.sqrt ((T : ℝ) * ℓ) ≤
      (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have hmul : Real.sqrt (n : ℝ) * Real.sqrt ((T : ℝ) * ℓ) =
        Real.sqrt ((n : ℝ) * T * ℓ) := by
      rw [← Real.sqrt_mul hn']
      congr 1
      ring
    rw [hmul]
    have hle : (n : ℝ) * T * ℓ ≤ (n : ℝ) * n * ℓ := by
      have hT' : (T : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTn
      have h1 : (n : ℝ) * T ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left hT' hn'
      exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg ℓ)
    have hsq : Real.sqrt ((n : ℝ) * n * ℓ) = (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
      rw [show (n : ℝ) * n * ℓ = (n : ℝ) ^ 2 * ℓ by ring, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq hn']
    rw [← hsq]
    exact Real.sqrt_le_sqrt hle
  have hD : (T : ℝ) * Real.sqrt (ℓ : ℝ) ≤ (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have hT' : (T : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTn
    exact mul_le_mul_of_nonneg_right hT' hrootL
  have hterm1 :
      (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) / (ts j : ℝ))) *
        (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) ≤
        4 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have h1 : (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) / (ts j : ℝ))) *
        (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) ≤
        (2 * Real.sqrt ((n : ℝ) * T)) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_right hsp' (by positivity)
    have hexp : (2 * Real.sqrt ((n : ℝ) * T)) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) =
        2 * (Real.sqrt ((n : ℝ) * T) * Real.sqrt (n : ℝ)) +
          2 * (Real.sqrt ((n : ℝ) * T) * Real.sqrt (ℓ : ℝ)) := by ring
    rw [hexp] at h1
    nlinarith [hA, hB]
  have hterm2 :
      (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) * (lam j : ℝ))) +
        (T : ℝ) * Real.sqrt (ℓ : ℝ) ≤ 2 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have hle : (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) * (lam j : ℝ))) ≤
        Real.sqrt (n : ℝ) * (Real.sqrt (T : ℝ) * Real.sqrt (ℓ : ℝ)) := by
      rw [hsumNlam]
      exact mul_le_mul_of_nonneg_left hCS hrootN
    have hsqrtTL : Real.sqrt (T : ℝ) * Real.sqrt (ℓ : ℝ) = Real.sqrt ((T : ℝ) * ℓ) :=
      Eq.symm (Real.sqrt_mul (x := (T : ℝ)) (y := (ℓ : ℝ)) (Nat.cast_nonneg T))
    rw [hsqrtTL] at hle
    nlinarith [hle, hCn, hD]
  calc
    (∑ j ∈ Finset.range T,
        Real.sqrt ((n : ℝ) / (ts j : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) +
      (∑ j ∈ Finset.range T,
        (Real.sqrt ((n : ℝ) * (lam j : ℝ)) + Real.sqrt (ℓ : ℝ)))
        = (∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) / (ts j : ℝ))) *
              (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) +
            ((∑ j ∈ Finset.range T, Real.sqrt ((n : ℝ) * (lam j : ℝ))) +
              (T : ℝ) * Real.sqrt (ℓ : ℝ)) := by
          rw [hfirst, hsecond]
    _ ≤ 4 * (n : ℝ) * Real.sqrt (ℓ : ℝ) + 2 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
          nlinarith [hterm1, hterm2]
    _ = 6 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by ring

/-- Unsuccessful rounds of `BMM`: `t` halves, so there are at most
`log₂ n + 1` of them; each costs at most `√n (√n + √ℓ)`, hence at most
`2 (log₂ n + 1) n√ℓ`. -/
theorem bmm_unsuccessful_cost_le {n ℓ F : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hF : F ≤ Nat.log2 n + 1) :
    (F : ℝ) * (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) ≤
      2 * (Nat.log2 n + 1 : ℝ) * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrootL : (0 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    have := Real.sq_sqrt hn'
    nlinarith
  have hprod : Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)) ≤
      2 * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
    have h1 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ≤ (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
      rw [hsq]
      have h1le : (1 : ℝ) ≤ Real.sqrt (ℓ : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hℓ)
      simpa using mul_le_mul_of_nonneg_left h1le hn'
    have hroot_le : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle : (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hn1 hn'
      have := Real.sqrt_le_sqrt hle
      rw [show (n : ℝ) * n = (n : ℝ) ^ 2 by ring, Real.sqrt_sq hn'] at this
      exact this
    have h2 : Real.sqrt (n : ℝ) * Real.sqrt (ℓ : ℝ) ≤ (n : ℝ) * Real.sqrt (ℓ : ℝ) :=
      mul_le_mul_of_nonneg_right hroot_le hrootL
    nlinarith
  have hcast : (F : ℝ) ≤ (Nat.log2 n + 1 : ℝ) := by exact_mod_cast hF
  calc
    (F : ℝ) * (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ)))
        ≤ (F : ℝ) * (2 * (n : ℝ) * Real.sqrt (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg F)
    _ ≤ (Nat.log2 n + 1 : ℝ) * (2 * (n : ℝ) * Real.sqrt (ℓ : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hcast (by positivity)
    _ = 2 * (Nat.log2 n + 1 : ℝ) * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by ring

/-- **Theorem 4.1 cost ledger.**  The successful rounds plus the unsuccessful
rounds cost at most `(2 log₂ n + 8) n√ℓ`, i.e. `Õ(n√ℓ)` with the paper's
polylogarithmic slack; `T ≤ min{n, ℓ}` and `F ≤ log₂ n + 1` are the round-count
facts supplied by the schedule. -/
theorem bmm_total_cost_le {n ℓ T F : ℕ} (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hTn : T ≤ n) (hTℓ : T ≤ ℓ) (hF : F ≤ Nat.log2 n + 1) (ts : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < T → ts (j + 1) + 1 ≤ ts j) (hlast : 1 ≤ ts (T - 1))
    (lam : ℕ → ℕ) (hlam : ∑ j ∈ Finset.range T, lam j = ℓ) :
    ((∑ j ∈ Finset.range T,
        Real.sqrt ((n : ℝ) / (ts j : ℝ)) *
          (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) +
      (∑ j ∈ Finset.range T,
        (Real.sqrt ((n : ℝ) * (lam j : ℝ)) + Real.sqrt (ℓ : ℝ)))) +
      (F : ℝ) * (Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) + Real.sqrt (ℓ : ℝ))) ≤
      (2 * (Nat.log2 n : ℝ) + 8) * (n : ℝ) * Real.sqrt (ℓ : ℝ) := by
  have hsucc := bmm_success_cost_le hn hℓ hTn hTℓ ts hstep hlast lam hlam
  have hfail := bmm_unsuccessful_cost_le hn hℓ hF
  nlinarith

end Qatlib.Papers.BoolMatMult11.MainResults.MatrixRounding
