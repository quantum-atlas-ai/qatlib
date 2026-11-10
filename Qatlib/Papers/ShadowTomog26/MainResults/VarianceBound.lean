/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ShadowTomog26.MainResults

variable {V : Type*} [Fintype V]

def varForm (c : V → ℝ) (Cov Tij : V → V → ℝ) (T : V → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * Cov i j * Tij i j / (T i * T j)

def ampVec (c σ T : V → ℝ) (i : V) : ℝ := |c i| * σ i / Real.sqrt (T i)

def ampBound (c σ T : V → ℝ) : ℝ := (∑ i, ampVec c σ T i) ^ 2

omit [Fintype V] in

lemma ampVec_nonneg {c σ T : V → ℝ} (hσ : ∀ i, 0 ≤ σ i) (hT : ∀ i, 0 < T i) (i : V) :
    0 ≤ ampVec c σ T i := by
  unfold ampVec
  exact div_nonneg (mul_nonneg (abs_nonneg _) (hσ i)) (Real.sqrt_pos.mpr (hT i)).le

omit [Fintype V] in

lemma ampVec_mul_eq {c σ T : V → ℝ} (hT : ∀ i, 0 < T i) (i j : V) :
    ampVec c σ T i * ampVec c σ T j
      = |c i| * |c j| * (σ i * σ j) / Real.sqrt (T i * T j) := by
  unfold ampVec
  rw [Real.sqrt_mul (hT i).le]
  have hi : Real.sqrt (T i) ≠ 0 := (Real.sqrt_pos.mpr (hT i)).ne'
  have hj : Real.sqrt (T j) ≠ 0 := (Real.sqrt_pos.mpr (hT j)).ne'
  field_simp

omit [Fintype V] in

lemma term_le_amp {c σ T : V → ℝ} {Cov Tij : V → V → ℝ}
    (hσ : ∀ i, 0 ≤ σ i) (hT : ∀ i, 0 < T i)
    (hTij0 : ∀ i j, 0 ≤ Tij i j) (hTij : ∀ i j, Tij i j ≤ Real.sqrt (T i * T j))
    (hCov : ∀ i j, |Cov i j| ≤ σ i * σ j) (i j : V) :
    c i * c j * Cov i j * Tij i j / (T i * T j) ≤ ampVec c σ T i * ampVec c σ T j := by
  have hden : 0 < T i * T j := mul_pos (hT i) (hT j)
  rw [ampVec_mul_eq hT i j]
  refine le_trans (le_abs_self _) ?_
  rw [abs_div, abs_of_pos hden]
  simp only [abs_mul, abs_of_nonneg (hTij0 i j)]

  have hnum1 : |c i| * |c j| * |Cov i j| * Tij i j
      ≤ |c i| * |c j| * (σ i * σ j) * Tij i j := by
    have hK : 0 ≤ |c i| * |c j| * Tij i j :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hTij0 i j)
    have h := mul_le_mul_of_nonneg_left (hCov i j) hK
    nlinarith [h]

  have hnum2 : |c i| * |c j| * (σ i * σ j) * Tij i j
      ≤ |c i| * |c j| * (σ i * σ j) * Real.sqrt (T i * T j) := by
    have hK : 0 ≤ |c i| * |c j| * (σ i * σ j) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (hσ i) (hσ j))
    have h := mul_le_mul_of_nonneg_left (hTij i j) hK
    nlinarith [h]
  have hdiv1 : |c i| * |c j| * |Cov i j| * Tij i j / (T i * T j)
      ≤ |c i| * |c j| * (σ i * σ j) * Tij i j / (T i * T j) :=
    div_le_div_of_nonneg_right hnum1 hden.le
  have hdiv2 : |c i| * |c j| * (σ i * σ j) * Tij i j / (T i * T j)
      ≤ |c i| * |c j| * (σ i * σ j) * Real.sqrt (T i * T j) / (T i * T j) :=
    div_le_div_of_nonneg_right hnum2 hden.le
  have h3 : |c i| * |c j| * (σ i * σ j) * Real.sqrt (T i * T j) / (T i * T j)
      = |c i| * |c j| * (σ i * σ j) / Real.sqrt (T i * T j) := by
    have hs : Real.sqrt (T i * T j) * Real.sqrt (T i * T j) = T i * T j :=
      Real.mul_self_sqrt hden.le
    have hsne : Real.sqrt (T i * T j) ≠ 0 := (Real.sqrt_pos.mpr hden).ne'
    have key : Real.sqrt (T i * T j) / (T i * T j) = 1 / Real.sqrt (T i * T j) := by
      rw [div_eq_div_iff hden.ne' hsne, one_mul]
      exact hs
    rw [mul_div_assoc, key, mul_one_div]
  exact le_trans hdiv1 (le_trans hdiv2 (le_of_eq h3))

theorem source_eq67 {c σ T : V → ℝ} {Cov Tij : V → V → ℝ}
    (hσ : ∀ i, 0 ≤ σ i) (hT : ∀ i, 0 < T i)
    (hTij0 : ∀ i j, 0 ≤ Tij i j) (hTij : ∀ i j, Tij i j ≤ Real.sqrt (T i * T j))
    (hCov : ∀ i j, |Cov i j| ≤ σ i * σ j) :
    varForm c Cov Tij T ≤ ampBound c σ T := by
  unfold varForm ampBound
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
  exact term_le_amp hσ hT hTij0 hTij hCov i j

theorem conditional_allocation_bound {c : V → ℝ} {Cov Tij : V → V → ℝ} {T : V → ℝ}
    {N Tsub chif : ℝ}
    (hT : ∀ i, 0 < T i) (hTij0 : ∀ i j, 0 ≤ Tij i j)
    (hTij : ∀ i j, Tij i j ≤ Real.sqrt (T i * T j))
    (hCov : ∀ i j, |Cov i j| ≤ 1)
    (hsub : ampBound c (fun _ => 1) T
      = (∑ i, Real.rpow |c i| (2 / 3)) ^ 3 / Tsub)
    (hlp : Tsub = N / chif) :
    varForm c Cov Tij T ≤ chif * (∑ i, Real.rpow |c i| (2 / 3)) ^ 3 / N := by
  have hvar := source_eq67 (c := c) (σ := fun _ => (1 : ℝ)) (T := T)
    (Cov := Cov) (Tij := Tij) (fun _ => zero_le_one) hT hTij0 hTij
    (fun i j => by simpa using hCov i j)
  calc varForm c Cov Tij T
      ≤ ampBound c (fun _ => (1 : ℝ)) T := hvar
    _ = (∑ i, Real.rpow |c i| (2 / 3)) ^ 3 / Tsub := hsub
    _ = (∑ i, Real.rpow |c i| (2 / 3)) ^ 3 / (N / chif) := by rw [hlp]
    _ = chif * (∑ i, Real.rpow |c i| (2 / 3)) ^ 3 / N := by
        rw [div_div_eq_mul_div]; ring

end Qatlib.Papers.ShadowTomog26.MainResults
