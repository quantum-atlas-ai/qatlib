/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.Complexity.Entrance — Proposition 3: entrance complexity for the Newton region

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Proposition 3, Eqs. (B26)/(B30), p. 21–22.

Let `K_enter := min{k ≥ 0 : e_k ≤ r_N}` be the first iteration at which the success-probability
error enters the Newton region.  Before that point Lemma 10 gives
`ϑ_{k+1} - ϑ_k ≥ ω* √(q₀(1-q₀))`, and summing from `k = 0` to `K_enter - 1` yields
`ϑ_{K_enter} - ϑ_0 ≥ K_enter ω* √(q₀(1-q₀))`.  Since `0 < ϑ_k ≤ π/2`,
`K_enter ≤ π / (2ω*√(q₀(1-q₀)))` (Eq. (B30)), and with `q₀ = M/N ≤ 1/2` this is
`K_enter = O(√(N/M))`.

This file formalizes the telescoping sum and the explicit `π/(2ω*u₀)` bound; the final
`O(√(N/M))` specialization is recorded as a separate statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Entrance

/-- **Proposition 3, telescoping estimate** (arXiv:2603.26039v3, Eq. (B30), p. 21–22).
If the Grover angles satisfy `0 < ϑ_k ≤ π/2` and increase by at least `ω u₀ > 0` per step,
then the number of steps `K` needed to reach the top of the range satisfies
`K ω u₀ < π/2` and hence `K ≤ π/(2ω u₀)`. -/
theorem proposition3_entrance_bound
    (ω u0 : ℝ) (hω : 0 < ω) (hu0 : 0 < u0)
    (ϑ : ℕ → ℝ) (K : ℕ)
    (hϑ0 : ∀ k, 0 < ϑ k) (hϑhalf : ∀ k, ϑ k ≤ Real.pi / 2)
    (hinc : ∀ k, k < K → ω * u0 ≤ ϑ (k + 1) - ϑ k) :
    (K : ℝ) * (ω * u0) < Real.pi / 2 ∧ (K : ℝ) ≤ Real.pi / (2 * (ω * u0)) := by
  have hsum : 0 < ω * u0 := mul_pos hω hu0
  -- Telescoping: `K (ω u₀) ≤ ϑ_K - ϑ_0`.
  have htel : ∀ n : ℕ, n ≤ K → (n : ℝ) * (ω * u0) ≤ ϑ n - ϑ 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      have hnK : n < K := Nat.lt_of_succ_le hn
      have h1 : ω * u0 ≤ ϑ (n + 1) - ϑ n := hinc n hnK
      have ih' : (n : ℝ) * (ω * u0) ≤ ϑ n - ϑ 0 := ih (Nat.le_of_lt hnK)
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [ih', h1]
  have hK := htel K le_rfl
  have hbound : (K : ℝ) * (ω * u0) < Real.pi / 2 := by
    have h0 : 0 < ϑ 0 := hϑ0 0
    have hKle : ϑ K ≤ Real.pi / 2 := hϑhalf K
    linarith [hK, h0, hKle]
  refine ⟨hbound, ?_⟩
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (ω * u0))]
  nlinarith [hbound, hsum]

/-- **Proposition 3** (arXiv:2603.26039v3, Proposition 3 / Eq. (B30), p. 21–22).  For
Algorithm 2 with `q₀ = M/N` and `2M ≤ N` (so `q₀ ≤ 1/2`), the first entry time into the
Newton region satisfies the explicit bound
`K_enter ≤ (π/(√2 ω*)) √(N/M)`.  This is the `O(√(N/M))` statement of the paper with the
constant made explicit. -/
theorem proposition3_entrance_complexity
    (ω : ℝ) (hω : 0 < ω) (N M : ℕ) (hM : 0 < M) (hMN : 2 * M ≤ N)
    (K : ℕ) (ϑ : ℕ → ℝ)
    (hϑ0 : ∀ k, 0 < ϑ k) (hϑhalf : ∀ k, ϑ k ≤ Real.pi / 2)
    (hinc : ∀ k, k < K → ω * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N))
              ≤ ϑ (k + 1) - ϑ k) :
    (K : ℝ) ≤ (Real.pi / (Real.sqrt 2 * ω)) * Real.sqrt ((N : ℝ) / M) := by
  -- The paper's derivation: `√(q₀(1-q₀)) ≥ √(q₀/2)` because `q₀ = M/N ≤ 1/2`, and
  -- `1/√(q₀) = √(N/M)`, so the `π/(2ω*u₀)` bound becomes `π/(√2 ω) √(N/M)`.
  have hNpos_nat : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNpos_nat
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hqpos : 0 < (M : ℝ) / N := by positivity
  have hqhalf : (M : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    have h2 : (2 : ℝ) * (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    linarith
  have h1mq : (1 : ℝ) / 2 ≤ 1 - (M : ℝ) / N := by linarith
  have hu0pos : 0 < Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)) :=
    Real.sqrt_pos.mpr (mul_pos hqpos (by linarith))
  have hbase :=
    (proposition3_entrance_bound ω (Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)))
      hω hu0pos ϑ K hϑ0 hϑhalf hinc).2
  -- `√(q₀(1-q₀)) ≥ √(q₀/2) = √(M/(2N))` because `q₀ ≤ 1/2`.
  have hprod : (M : ℝ) / (2 * N) ≤ ((M : ℝ) / N) * (1 - (M : ℝ) / N) := by
    have h := mul_le_mul_of_nonneg_left h1mq (le_of_lt hqpos)
    have he : ((M : ℝ) / N) * ((1 : ℝ) / 2) = (M : ℝ) / (2 * N) := by
      field_simp
    linarith [h, he.le, he.ge]
  have hsle : Real.sqrt ((M : ℝ) / (2 * N))
      ≤ Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)) := Real.sqrt_le_sqrt hprod
  have hsq : (Real.sqrt ((M : ℝ) / (2 * N))) ^ 2 = (M : ℝ) / (2 * N) :=
    Real.sq_sqrt (by positivity)
  -- An exact identity for the reciprocal of `√(M/(2N))`.
  have heq0 : 1 / (2 * Real.sqrt ((M : ℝ) / (2 * N)))
      = (1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M) := by
    have hL : 1 / (2 * Real.sqrt ((M : ℝ) / (2 * N))) = Real.sqrt ((N : ℝ) / (2 * M)) := by
      rw [show 1 / (2 * Real.sqrt ((M : ℝ) / (2 * N)))
            = Real.sqrt ((1 / (2 * Real.sqrt ((M : ℝ) / (2 * N)))) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
      congr 1
      rw [div_pow, one_pow, mul_pow, hsq]
      field_simp
    have hR : (1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M) = Real.sqrt ((N : ℝ) / (2 * M)) := by
      rw [show (1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M)
            = Real.sqrt (((1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M)) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
      congr 1
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ) / M)]
      field_simp
    rw [hL, hR]
  have hrec : 1 / (2 * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)))
      ≤ 1 / (2 * Real.sqrt ((M : ℝ) / (2 * N))) :=
    one_div_le_one_div_of_le (by positivity) (by linarith [hsle])
  have hmain : 1 / (2 * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)))
      ≤ (1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M) := le_trans hrec heq0.le
  have hcalc : Real.pi / (2 * (ω * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N))))
      ≤ (Real.pi / (Real.sqrt 2 * ω)) * Real.sqrt ((N : ℝ) / M) := by
    calc
      Real.pi / (2 * (ω * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N))))
          = (Real.pi / ω) * (1 / (2 * Real.sqrt (((M : ℝ) / N) * (1 - (M : ℝ) / N)))) := by
            field_simp
      _ ≤ (Real.pi / ω) * ((1 / Real.sqrt 2) * Real.sqrt ((N : ℝ) / M)) :=
            mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = (Real.pi / (Real.sqrt 2 * ω)) * Real.sqrt ((N : ℝ) / M) := by
            field_simp
  linarith [hbase, hcalc]

end Qatlib.Papers.QSearchPrec26.RmSearch.Complexity.Entrance
