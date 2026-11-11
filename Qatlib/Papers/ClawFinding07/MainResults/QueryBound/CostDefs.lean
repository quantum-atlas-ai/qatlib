/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ClawFinding07.MainResults.Spectral.JohnsonGap

/-!
# Claw-detection cost expressions

This module defines `szegedyCost` and its claw-detection specializations for the comparison and
standard-query models of [Tani2009]. Algebraic expansions and explicit estimates give separate
bounds for `N ≤ M < N^2` and `N^2 ≤ M`.

## Main statements

* `clawDetectCost_eq` and `clawDetectStandardCost_eq`: expanded detection cost formulas.
* `lemma4_clawDetect_comparison`: comparison cost bounds in both regimes.
* `corollary5_clawDetect_standard`: standard-query cost bounds in both regimes.

## References

* [Tani, 2009][Tani2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ClawFinding07.MainResults.QueryBound

open scoped BigOperators

/-- The Szegedy detection cost expression `CU + (CF + CW)/sqrt (δ*ε)`, with setup, checking, and
walk costs and gap and marked-fraction parameters. -/
def szegedyCost (CU CF CW δ ε : ℝ) : ℝ :=
  CU + (CF + CW) / Real.sqrt (δ * ε)

/-- The comparison cost expression for claw detection with subset sizes `l` and `m`, including
logarithmic setup and walk costs. -/
def clawDetectCost (N M l m : ℝ) : ℝ :=
  szegedyCost ((l + m) * Real.log (l + m)) 0 (Real.log (l + m)) (1 / m) (l * m / (N * M))

/-- The standard-query cost expression for claw detection with subset sizes `l` and `m`, linear
setup cost, and unit walk cost. -/
def clawDetectStandardCost (N M l m : ℝ) : ℝ :=
  szegedyCost (l + m) 0 1 (1 / m) (l * m / (N * M))

/-- For positive subset sizes and positive `N*M`, expands the comparison detection cost as
`(l+m)*log (l+m) + log (l+m)*sqrt (N*M/l)`. -/
theorem clawDetectCost_eq {N M l m : ℝ} (hl : 0 < l) (hm : 0 < m) (hNM : 0 < N * M) :
    clawDetectCost N M l m
      = (l + m) * Real.log (l + m) + Real.log (l + m) * Real.sqrt (N * M / l) := by
  have hratio : (1 / m) * (l * m / (N * M)) = l / (N * M) := by
    field_simp
  have hsl : (0:ℝ) < Real.sqrt l := Real.sqrt_pos.2 hl
  have hsm : (0:ℝ) < Real.sqrt (N * M) := Real.sqrt_pos.2 hNM
  simp only [clawDetectCost, szegedyCost, zero_add]
  rw [hratio, Real.sqrt_div (le_of_lt hl), Real.sqrt_div (le_of_lt hNM)]
  have hsl' : Real.sqrt l ≠ 0 := hsl.ne'
  have hsm' : Real.sqrt (N * M) ≠ 0 := hsm.ne'
  field_simp
  try ring

/-- For positive subset sizes and positive `N*M`, expands the standard detection cost as
`l+m+sqrt (N*M/l)`. -/
theorem clawDetectStandardCost_eq {N M l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hNM : 0 < N * M) :
    clawDetectStandardCost N M l m = (l + m) + Real.sqrt (N * M / l) := by
  have hratio : (1 / m) * (l * m / (N * M)) = l / (N * M) := by
    field_simp
  have hsl : (0:ℝ) < Real.sqrt l := Real.sqrt_pos.2 hl
  have hsm : (0:ℝ) < Real.sqrt (N * M) := Real.sqrt_pos.2 hNM
  simp only [clawDetectStandardCost, szegedyCost]
  rw [hratio, Real.sqrt_div (le_of_lt hl), Real.sqrt_div (le_of_lt hNM)]
  have hsl' : Real.sqrt l ≠ 0 := hsl.ne'
  have hsm' : Real.sqrt (N * M) ≠ 0 := hsm.ne'
  field_simp
  try ring

/-- For positive `N*M`, cubing its real cube root recovers `N*M`. -/
theorem rpow_third_cube {N M : ℝ} (hNM : 0 < N * M) :
    ((N * M) ^ (1/3:ℝ)) ^ 3 = N * M := by
  have h := Real.rpow_mul (le_of_lt hNM) (1/3:ℝ) (3:ℝ)
  have h3 : (3:ℝ) = ((3:ℕ):ℝ) := by norm_num
  rw [show (1/3:ℝ) * 3 = 1 by norm_num, Real.rpow_one, h3, Real.rpow_natCast] at h
  exact h.symm

/-- For positive `N` and `M` with `M < N^2`, the cube root of `N*M` is strictly smaller than
`N`. -/
theorem rpow_third_lt {N M : ℝ} (hN : 0 < N) (hM0 : 0 < M) (hM : M < N ^ 2) :
    (N * M) ^ (1/3:ℝ) < N := by
  have hNM : (0:ℝ) < N * M := by positivity
  have hcube : ((N * M) ^ (1/3:ℝ)) ^ 3 < N ^ 3 := by
    rw [rpow_third_cube hNM]
    have hstep : N * M < N * N ^ 2 := by
      exact mul_lt_mul_of_pos_left hM hN
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 3 (le_of_lt hN) hcube

/-- For `2 ≤ N ≤ M < N^2`, the comparison detection cost at equal subset sizes `(N*M)^(1/3)` is
at most `64*(N*M)^(1/3)*log N`. This is the first regime of [Tani, Lemma 4][Tani2009]. -/
theorem lemma4_clawDetect_regime1 (N M : ℝ) (hN : 2 ≤ N) (hNM' : N ≤ M)
    (hM : M < N ^ 2) :
    clawDetectCost N M ((N * M) ^ (1/3:ℝ)) ((N * M) ^ (1/3:ℝ))
      ≤ 64 * (N * M) ^ (1/3:ℝ) * Real.log N := by
  set x : ℝ := (N * M) ^ (1/3:ℝ)
  have hN0 : (0:ℝ) < N := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hNM : (0:ℝ) < N * M := by positivity
  have hx0 : 0 < x := Real.rpow_pos_of_pos hNM _
  have hx3 : x ^ 3 = N * M := rpow_third_cube hNM
  have hone : x * x / (N * M) = 1 / x := by
    rw [← hx3]
    field_simp
  have hden : (1 / x) * (x * x / (N * M)) = (1 / x) ^ 2 := by
    rw [hone]; ring
  have hcost : clawDetectCost N M x x = 3 * x * Real.log (2 * x) := by
    simp only [clawDetectCost, szegedyCost, zero_add]
    rw [hden, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / x)]
    have hxne : x ≠ 0 := hx0.ne'
    have harg : x + x = 2 * x := by ring
    rw [harg]
    field_simp
    ring
  have hxlt : x < N := rpow_third_lt hN0 hM0 hM
  have hlog : Real.log (2 * x) ≤ 2 * Real.log N := by
    have h2x : (0:ℝ) < 2 * x := by positivity
    have hle : 2 * x ≤ N ^ 2 := by nlinarith
    calc Real.log (2 * x) ≤ Real.log (N ^ 2) := Real.log_le_log h2x hle
      _ = 2 * Real.log N := by rw [Real.log_pow]; try ring
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  calc clawDetectCost N M x x = 3 * x * Real.log (2 * x) := hcost
    _ ≤ 3 * x * (2 * Real.log N) := by
          apply mul_le_mul_of_nonneg_left hlog; positivity
    _ = 6 * x * Real.log N := by ring
    _ ≤ 64 * x * Real.log N := by
          have hxlog : (0:ℝ) ≤ x * Real.log N := mul_nonneg (le_of_lt hx0) hlogN
          nlinarith

/-- For `N ≥ 2` and `N^2 ≤ M`, the comparison detection cost at subset sizes `N` is at most
`64*sqrt M*log N`. This is the second regime of [Tani, Lemma 4][Tani2009]. -/
theorem lemma4_clawDetect_regime2 (N M : ℝ) (hN : 2 ≤ N) (hM : N ^ 2 ≤ M) :
    clawDetectCost N M N N ≤ 64 * Real.sqrt M * Real.log N := by
  have hN0 : (0:ℝ) < N := by linarith
  have hM0 : (0:ℝ) < M := by nlinarith
  have hNM : (0:ℝ) < N * M := by positivity
  have hden : (1 / N) * (N * N / (N * M)) = 1 / M := by
    field_simp
  have hsm : Real.sqrt M ≠ 0 := (Real.sqrt_pos.2 hM0).ne'
  have hsqrt : (0 + Real.log (N + N)) / Real.sqrt (1 / M)
      = Real.sqrt M * Real.log (N + N) := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1)]
    norm_num
    field_simp
  have hcost : clawDetectCost N M N N
      = 2 * N * Real.log (2 * N) + Real.sqrt M * Real.log (2 * N) := by
    simp only [clawDetectCost, szegedyCost]
    rw [hden, hsqrt]
    have harg : N + N = 2 * N := by ring
    rw [harg]
    try ring
  have hNle : N ≤ Real.sqrt M := by
    calc N = Real.sqrt (N ^ 2) := by rw [Real.sqrt_sq (le_of_lt hN0)]
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hM
  have hlog : Real.log (2 * N) ≤ 2 * Real.log N := by
    have h2N : (0:ℝ) < 2 * N := by positivity
    have hle : 2 * N ≤ N ^ 2 := by nlinarith
    calc Real.log (2 * N) ≤ Real.log (N ^ 2) := Real.log_le_log h2N hle
      _ = 2 * Real.log N := by rw [Real.log_pow]; try ring
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hsq0 : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  calc clawDetectCost N M N N = 2 * N * Real.log (2 * N) + Real.sqrt M * Real.log (2 * N) :=
        hcost
    _ ≤ 2 * Real.sqrt M * Real.log (2 * N) + Real.sqrt M * Real.log (2 * N) := by
          have h1 : 2 * N * Real.log (2 * N) ≤ 2 * Real.sqrt M * Real.log (2 * N) := by
            apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg (by linarith))
            linarith
          linarith
    _ = 3 * Real.sqrt M * Real.log (2 * N) := by ring
    _ ≤ 6 * Real.sqrt M * Real.log N := by
          have h1 : 3 * Real.sqrt M * Real.log (2 * N) ≤ 3 * Real.sqrt M * (2 * Real.log N) := by
            apply mul_le_mul_of_nonneg_left hlog; positivity
          nlinarith
    _ ≤ 64 * Real.sqrt M * Real.log N := by
          have : (0:ℝ) ≤ Real.sqrt M * Real.log N := mul_nonneg hsq0 hlogN
          nlinarith

/-- Combines the two comparison detection cost bounds for `N ≤ M < N^2` and `N^2 ≤ M`, assuming
`N ≥ 2`, as in [Tani, Lemma 4][Tani2009]. -/
theorem lemma4_clawDetect_comparison (N M : ℝ) (hN : 2 ≤ N) :
    (N ≤ M → M < N ^ 2 →
        clawDetectCost N M ((N * M) ^ (1/3:ℝ)) ((N * M) ^ (1/3:ℝ))
          ≤ 64 * (N * M) ^ (1/3:ℝ) * Real.log N) ∧
    (N ^ 2 ≤ M → clawDetectCost N M N N ≤ 64 * Real.sqrt M * Real.log N) :=
  ⟨fun hNM hM => lemma4_clawDetect_regime1 N M hN hNM hM,
   fun h => lemma4_clawDetect_regime2 N M hN h⟩

/-- For `2 ≤ N ≤ M < N^2`, bounds the standard detection cost at equal subset sizes
`(N*M)^(1/3)` by `4*(N*M)^(1/3)`, as in [Tani, Corollary 5][Tani2009]. -/
theorem corollary5_clawDetect_standard_regime1 (N M : ℝ) (hN : 2 ≤ N)
    (hNM' : N ≤ M) (_hM : M < N ^ 2) :
    clawDetectStandardCost N M ((N * M) ^ (1/3:ℝ)) ((N * M) ^ (1/3:ℝ))
      ≤ 4 * (N * M) ^ (1/3:ℝ) := by
  set x : ℝ := (N * M) ^ (1/3:ℝ)
  have hN0 : (0:ℝ) < N := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hNM : (0:ℝ) < N * M := by positivity
  have hx0 : 0 < x := Real.rpow_pos_of_pos hNM _
  have hx3 : x ^ 3 = N * M := rpow_third_cube hNM
  have hone : x * x / (N * M) = 1 / x := by
    rw [← hx3]
    field_simp
  have hden : (1 / x) * (x * x / (N * M)) = (1 / x) ^ 2 := by
    rw [hone]; ring
  have hcost : clawDetectStandardCost N M x x = 3 * x := by
    simp only [clawDetectStandardCost, szegedyCost]
    rw [hden, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / x)]
    have hxne : x ≠ 0 := hx0.ne'
    have harg : x + x = 2 * x := by ring
    rw [harg]
    field_simp
    ring
  rw [hcost]
  linarith

/-- For `N ≥ 2` and `N^2 ≤ M`, bounds the standard detection cost at subset sizes `N` by `4*sqrt
M`, as in [Tani, Corollary 5][Tani2009]. -/
theorem corollary5_clawDetect_standard_regime2 (N M : ℝ) (hN : 2 ≤ N)
    (hM : N ^ 2 ≤ M) :
    clawDetectStandardCost N M N N ≤ 4 * Real.sqrt M := by
  have hN0 : (0:ℝ) < N := by linarith
  have hM0 : (0:ℝ) < M := by nlinarith
  have hNM : (0:ℝ) < N * M := by positivity
  have hden : (1 / N) * (N * N / (N * M)) = 1 / M := by
    field_simp
  have hsqrt : (0 + 1 : ℝ) / Real.sqrt (1 / M) = Real.sqrt M := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1)]
    norm_num
  have hcost : clawDetectStandardCost N M N N = 2 * N + Real.sqrt M := by
    simp only [clawDetectStandardCost, szegedyCost]
    rw [hden, hsqrt]
    have harg : N + N = 2 * N := by ring
    rw [harg]
    try ring
  have hNle : N ≤ Real.sqrt M := by
    calc N = Real.sqrt (N ^ 2) := by rw [Real.sqrt_sq (le_of_lt hN0)]
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hM
  rw [hcost]
  linarith

/-- Combines the two standard-query detection cost regimes under `N ≥ 2`, as in [Tani, Corollary
5][Tani2009]. -/
theorem corollary5_clawDetect_standard (N M : ℝ) (hN : 2 ≤ N) :
    (N ≤ M → M < N ^ 2 →
        clawDetectStandardCost N M ((N * M) ^ (1/3:ℝ)) ((N * M) ^ (1/3:ℝ))
          ≤ 4 * (N * M) ^ (1/3:ℝ)) ∧
    (N ^ 2 ≤ M → clawDetectStandardCost N M N N ≤ 4 * Real.sqrt M) :=
  ⟨fun hNM hM => corollary5_clawDetect_standard_regime1 N M hN hNM hM,
   fun h => corollary5_clawDetect_standard_regime2 N M hN h⟩

end Qatlib.Papers.ClawFinding07.MainResults.QueryBound
