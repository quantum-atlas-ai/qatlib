/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabaticEvol00.MainResults.AdiabaticDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Two-dimensional block formulas for ring 2-SAT

This module defines `ringBlock`, its radicand, and the two closed energy expressions
`ringEnergyPlus` and `ringEnergyMinus`, and proves matching trace and determinant formulas. It
minimizes the radicand by completing the square, derives block-gap bounds, and proves that the
expression `ringGapFormula` evaluated at `s = 2 / 3` is asymptotic to `4 * Real.pi / (3 * n)`.
The mathematical context is [FarhiEtAl2000].

## Main statements

* `ringBlockGap_min`: When `Real.cos θ ≥ 0`, the difference of the two block-energy expressions
  is at least `2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ))`.
* `ring_gap_asymptotic`: The ratio of `ringGapFormula n` to `4 * Real.pi / (3 * n)` tends to one
  as `n` tends to infinity.
* `ring_required_time_cubic`: For positive `n`, the assumptions `0 ≤ E ≤ n` and `1 / n ≤ g` give
  the cubic upper bound `E / g ^ 2 ≤ n ^ 3`.

## References

* [Farhi et al., 2000][FarhiEtAl2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabaticEvol00.MainResults
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

/-- The two-dimensional complex Hermitian block with diagonal entries `s + s * Real.cos θ` and
`4 - 3 * s - s * Real.cos θ` and off-diagonal entries `±i * s * Real.sin θ`. -/
def ringBlock (θ s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((s + s * Real.cos θ) : ℝ) : ℂ),
     (Complex.I * (((s * Real.sin θ) : ℝ) : ℂ));
     (-(Complex.I * (((s * Real.sin θ) : ℝ) : ℂ))),
     (((4 - 3 * s - s * Real.cos θ) : ℝ) : ℂ)]

/-- A two-dimensional matrix with real diagonal entries and off-diagonal entries `i * c` and `-i
* c` is Hermitian. -/
theorem hermitian_two (a c d : ℝ) :
    (!![((a : ℝ) : ℂ), (Complex.I * ((c : ℝ) : ℂ));
        (-(Complex.I * ((c : ℝ) : ℂ))), ((d : ℝ) : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Complex.conj_I, Complex.conj_ofReal]

/-- The ring 2-SAT block is Hermitian for every real angle and interpolation parameter. -/
theorem ringBlock_isHermitian (θ s : ℝ) : (ringBlock θ s).IsHermitian :=
  hermitian_two (s + s * Real.cos θ) (s * Real.sin θ) (4 - 3 * s - s * Real.cos θ)

/-- The trace of the ring block equals the real number `4 - 2 * s`, embedded in the complex
numbers. -/
theorem ringBlock_trace (θ s : ℝ) :
    (ringBlock θ s).trace = ((4 - 2 * s : ℝ) : ℂ) := by
  simp [ringBlock, Matrix.trace, Fin.sum_univ_two]
  ring

/-- For every complex `z`, the product `Complex.I * z * (Complex.I * z)` equals `-z ^ 2`. -/
theorem complex_i_mul_self_mul (z : ℂ) : Complex.I * z * (Complex.I * z) = -z ^ 2 := by
  have h : Complex.I * Complex.I = -1 := by
    rw [← pow_two]
    exact Complex.I_sq
  calc Complex.I * z * (Complex.I * z) = (Complex.I * Complex.I) * (z * z) := by ring
    _ = -1 * (z * z) := by rw [h]
    _ = -z ^ 2 := by ring

/-- The ring-block determinant equals the product of its diagonal entries minus `(s * Real.sin
θ) ^ 2`, embedded in the complex numbers. -/
theorem ringBlock_det (θ s : ℝ) :
    (ringBlock θ s).det =
      (((s + s * Real.cos θ) * (4 - 3 * s - s * Real.cos θ) -
        (s * Real.sin θ) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [ringBlock]
  rw [complex_i_mul_self_mul ((s : ℂ) * Complex.sin (θ : ℂ))]
  ring

/-- The real determinant expression simplifies to `4 * s * (1 - s) * (1 + Real.cos θ)`. -/
theorem ringBlock_det_real (θ s : ℝ) :
    (s + s * Real.cos θ) * (4 - 3 * s - s * Real.cos θ) - (s * Real.sin θ) ^ 2 =
      4 * s * (1 - s) * (1 + Real.cos θ) := by
  linear_combination (-(s ^ 2)) * Real.sin_sq_add_cos_sq θ

/-- The ring-block determinant is `4 * s * (1 - s) * (1 + Real.cos θ)`, embedded in the complex
numbers. -/
theorem ringBlock_det_closed (θ s : ℝ) :
    (ringBlock θ s).det = ((4 * s * (1 - s) * (1 + Real.cos θ) : ℝ) : ℂ) := by
  rw [ringBlock_det, ringBlock_det_real]

/-- The real expression `(2 - 3 * s) ^ 2 + 4 * s * (1 - s) * (1 - Real.cos θ)` appearing under
the block-energy square root. -/
def ringRadicand (θ s : ℝ) : ℝ :=
  (2 - 3 * s) ^ 2 + 4 * s * (1 - s) * (1 - Real.cos θ)

/-- The upper block-energy expression `2 - s + Real.sqrt (ringRadicand θ s)`. -/
def ringEnergyPlus (θ s : ℝ) : ℝ := 2 - s + Real.sqrt (ringRadicand θ s)

/-- The lower block-energy expression `2 - s - Real.sqrt (ringRadicand θ s)`. -/
def ringEnergyMinus (θ s : ℝ) : ℝ := 2 - s - Real.sqrt (ringRadicand θ s)

/-- The two block-energy expressions sum to `4 - 2 * s`. -/
theorem ringEnergy_sum (θ s : ℝ) :
    ringEnergyPlus θ s + ringEnergyMinus θ s = 4 - 2 * s := by
  unfold ringEnergyPlus ringEnergyMinus
  ring

/-- When the radicand is nonnegative, the two block-energy expressions have product `4 * s * (1
- s) * (1 + Real.cos θ)`. -/
theorem ringEnergy_product (θ s : ℝ) (hR : 0 ≤ ringRadicand θ s) :
    ringEnergyPlus θ s * ringEnergyMinus θ s = 4 * s * (1 - s) * (1 + Real.cos θ) := by
  unfold ringEnergyPlus ringEnergyMinus
  have h : Real.sqrt (ringRadicand θ s) ^ 2 = ringRadicand θ s := Real.sq_sqrt hR
  unfold ringRadicand at h
  unfold ringRadicand
  nlinarith [h]

/-- For a nonnegative radicand, the ring-block trace and determinant equal the sum and product
of the two defined energy expressions [FarhiEtAl2000]. -/
theorem ringBlock_spectrum (θ s : ℝ) (hR : 0 ≤ ringRadicand θ s) :
    (ringBlock θ s).trace = ((ringEnergyPlus θ s + ringEnergyMinus θ s : ℝ) : ℂ) ∧
    (ringBlock θ s).det = ((ringEnergyPlus θ s * ringEnergyMinus θ s : ℝ) : ℂ) := by
  constructor
  · rw [ringBlock_trace, ringEnergy_sum]
  · rw [ringBlock_det_closed, ringEnergy_product θ s hR]

/-- At `s = 2 / 3`, the ring radicand equals `(8 / 9) * (1 - Real.cos θ)`. -/
theorem ringRadicand_two_thirds (θ : ℝ) :
    ringRadicand θ (2 / 3) = 8 / 9 * (1 - Real.cos θ) := by
  unfold ringRadicand
  ring

/-- The difference of the two block-energy expressions at angle `Real.pi / n` and interpolation
parameter `2 / 3`. -/
def ringGapFormula (n : ℕ) : ℝ :=
  ringEnergyPlus (Real.pi / n) (2 / 3) - ringEnergyMinus (Real.pi / n) (2 / 3)

/-- The defined ring gap expression is twice the square root of the radicand at angle `Real.pi /
n` and parameter `2 / 3`. -/
theorem ringGapFormula_eq (n : ℕ) :
    ringGapFormula n = 2 * Real.sqrt (ringRadicand (Real.pi / n) (2 / 3)) := by
  unfold ringGapFormula ringEnergyPlus ringEnergyMinus
  ring

/-- The difference of the upper and lower block-energy expressions equals twice the square root
of the radicand. -/
theorem ringEnergy_gap (θ s : ℝ) :
    ringEnergyPlus θ s - ringEnergyMinus θ s = 2 * Real.sqrt (ringRadicand θ s) := by
  unfold ringEnergyPlus ringEnergyMinus
  ring

/-- If `Real.cos θ ≠ 1`, the ring radicand is strictly positive for every `s ∈ [0, 1]`. -/
theorem ringRadicand_pos {θ : ℝ} (hθ : Real.cos θ ≠ 1) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < ringRadicand θ s := by
  intro s hs
  have hc : 0 < 1 - Real.cos θ := by
    have hlt : Real.cos θ < 1 := lt_of_le_of_ne (Real.cos_le_one θ) hθ
    linarith
  have hs0 : 0 ≤ s := hs.1
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  unfold ringRadicand
  rcases lt_or_eq_of_le hs0 with h | h
  · rcases lt_or_eq_of_le hs1 with h1 | h1
    · have hprod : 0 < 4 * s * (1 - s) * (1 - Real.cos θ) := by
        have h4s : 0 < 4 * s := by linarith
        exact mul_pos (mul_pos h4s h1) hc
      have hsq : 0 ≤ (2 - 3 * s) ^ 2 := sq_nonneg _
      linarith
    · have hseq : s = 1 := by linarith
      subst hseq
      norm_num
  · have hseq : s = 0 := by linarith
    subst hseq
    norm_num

/-- The ring radicand is the sum of its quadratic coefficient times the squared displacement
from its vertex and its explicit vertex value. -/
theorem ringRadicand_complete_square (θ s : ℝ) :
    ringRadicand θ s =
      (9 - 4 * (1 - Real.cos θ)) *
          (s - (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ^ 2 +
        4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) := by
  unfold ringRadicand
  have hA : 9 - 4 * (1 - Real.cos θ) ≠ 0 := by
    have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  field_simp
  ring

/-- At `s = (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))`, the radicand equals `4 *
(1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))`. -/
theorem ringRadicand_vertex (θ : ℝ) :
    ringRadicand θ ((6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) =
      4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) := by
  rw [ringRadicand_complete_square]
  simp

/-- When `Real.cos θ ≥ 0`, the quadratic vertex parameter of the ring radicand belongs to `[0,
1]`. -/
theorem ring_vertex_mem {θ : ℝ} (hcos : 0 ≤ Real.cos θ) :
    (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
  constructor
  · apply div_nonneg <;> nlinarith
  · rw [div_le_one (by nlinarith)]
    nlinarith

/-- When `Real.cos θ ≥ 0`, the ring radicand at its vertex is at most its value at any real `s`. -/
theorem ringRadicand_vertex_le {θ s : ℝ} (hcos : 0 ≤ Real.cos θ) :
    ringRadicand θ ((6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ≤
      ringRadicand θ s := by
  rw [ringRadicand_vertex]
  have hA : 0 ≤ 9 - 4 * (1 - Real.cos θ) := by
    have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    nlinarith
  have hsq : 0 ≤ (s - (6 - 2 * (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ))) ^ 2 :=
    sq_nonneg _
  have h := mul_nonneg hA hsq
  rw [ringRadicand_complete_square]
  linarith

/-- The explicit vertex value of the ring radicand equals `4 * Real.sin θ ^ 2 / (5 + 4 *
Real.cos θ)`. -/
theorem ringRadicand_vertex_sin (θ : ℝ) :
    4 * (1 - Real.cos θ) * (2 - (1 - Real.cos θ)) / (9 - 4 * (1 - Real.cos θ)) =
      4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ) := by
  have hsin : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  have hd : 9 - 4 * (1 - Real.cos θ) = 5 + 4 * Real.cos θ := by ring
  have hden : 5 + 4 * Real.cos θ ≠ 0 := by
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  rw [hd, hsin]
  field_simp [hden]
  ring

/-- When `Real.cos θ ≥ 0`, the difference of the two block-energy expressions is at least `2 *
Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ))` [FarhiEtAl2000]. -/
theorem ringBlockGap_min (θ : ℝ) (hcos : 0 ≤ Real.cos θ) (s : ℝ) :
    2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ)) ≤
      ringEnergyPlus θ s - ringEnergyMinus θ s := by
  rw [ringEnergy_gap]
  have hv := ringRadicand_vertex_le (θ := θ) (s := s) hcos
  rw [ringRadicand_vertex] at hv
  rw [ringRadicand_vertex_sin] at hv
  have := Real.sqrt_le_sqrt hv
  linarith

/-- For `0 ≤ θ ≤ Real.pi`, the square-root form of the vertex gap equals `4 * Real.sin θ /
Real.sqrt (5 + 4 * Real.cos θ)`. -/
theorem ringBlockGap_min_exact (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    2 * Real.sqrt (4 * Real.sin θ ^ 2 / (5 + 4 * Real.cos θ)) =
      4 * Real.sin θ / Real.sqrt (5 + 4 * Real.cos θ) := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
  have hden : 0 < 5 + 4 * Real.cos θ := by
    have hge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith
  have hsq : 4 * Real.sin θ ^ 2 = (2 * Real.sin θ) ^ 2 := by ring
  rw [hsq, Real.sqrt_div' _ (le_of_lt hden), Real.sqrt_sq (by positivity)]
  ring

/-- At `s = 2 / 3`, the radicand equals `((4 / 3) * Real.sin (θ / 2)) ^ 2`. -/
theorem ringRadicand_two_thirds_sq (θ : ℝ) :
    ringRadicand θ (2 / 3) = ((4 / 3) * Real.sin (θ / 2)) ^ 2 := by
  rw [ringRadicand_two_thirds]
  have h : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have hc := Real.cos_two_mul_eq_one_sub (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at hc
    linarith
  rw [h]
  ring

/-- For `n ≥ 1`, the defined ring gap expression equals `(8 / 3) * Real.sin (Real.pi / (2 * n))`
[FarhiEtAl2000]. -/
theorem ringGapFormula_eq_sin (n : ℕ) (hn : 1 ≤ n) :
    ringGapFormula n = 8 / 3 * Real.sin (Real.pi / (2 * (n : ℝ))) := by
  rw [ringGapFormula_eq, ringRadicand_two_thirds_sq]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpipos : 0 < Real.pi := Real.pi_pos
  have hx0 : 0 ≤ Real.pi / (n : ℝ) / 2 := by positivity
  have hxπ : Real.pi / (n : ℝ) / 2 ≤ Real.pi := by
    have h1 : Real.pi / (n : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ hnpos]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using mul_le_mul_of_nonneg_left hn1 (le_of_lt Real.pi_pos)
    linarith
  have hsin : 0 ≤ Real.sin (Real.pi / (n : ℝ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxπ
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (4 / 3) * Real.sin (Real.pi / (n : ℝ) / 2))]
  have harg : Real.pi / (n : ℝ) / 2 = Real.pi / (2 * (n : ℝ)) := by
    field_simp
  rw [harg]
  ring

/-- The ratio `Real.sin (Real.pi / (2 * n)) / (Real.pi / (2 * n))` tends to one as the natural
number `n` tends to infinity. -/
theorem tendsto_sin_div_pi :
    Filter.Tendsto
      (fun n : ℕ => Real.sin (Real.pi / (2 * (n : ℝ))) / (Real.pi / (2 * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  have harg : Filter.Tendsto (fun n : ℕ => Real.pi / (2 * (n : ℝ))) Filter.atTop (nhds 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (Real.pi / 2)
    refine h.congr' ?_
    filter_upwards with n
    field_simp
  have hsinc : Filter.Tendsto (fun x : ℝ => Real.sinc x) (nhds 0) (nhds 1) := by
    simpa using Real.continuous_sinc.tendsto (0 : ℝ)
  have hcomp := hsinc.comp harg
  refine hcomp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hne : Real.pi / (2 * (n : ℝ)) ≠ 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  change Real.sinc (Real.pi / (2 * (n : ℝ))) =
    Real.sin (Real.pi / (2 * (n : ℝ))) / (Real.pi / (2 * (n : ℝ)))
  rw [Real.sinc_of_ne_zero hne]

/-- The ratio of `ringGapFormula n` to `4 * Real.pi / (3 * n)` tends to one as `n` tends to
infinity [FarhiEtAl2000]. -/
theorem ring_gap_asymptotic :
    Filter.Tendsto
      (fun n : ℕ => ringGapFormula n / (4 * Real.pi / (3 * (n : ℝ))))
      Filter.atTop (nhds 1) := by
  refine (tendsto_sin_div_pi).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpipos : 0 < Real.pi := Real.pi_pos
  rw [ringGapFormula_eq_sin n hn]
  field_simp
  ring

/-- For positive `n`, the assumptions `0 ≤ E ≤ n` and `1 / n ≤ g` give the cubic upper bound `E
/ g ^ 2 ≤ n ^ 3` [FarhiEtAl2000]. -/
theorem ring_required_time_cubic {E g : ℝ} {n : ℕ} (hn : 0 < (n : ℝ))
    (hE : E ≤ (n : ℝ)) (hg : 1 / (n : ℝ) ≤ g) (hE0 : 0 ≤ E) :
    E / g ^ 2 ≤ (n : ℝ) ^ 3 :=
  ring_time_is_cubic hn hE hg hE0

end Qatlib.Papers.AdiabaticEvol00.MainResults.Ring2SAT
