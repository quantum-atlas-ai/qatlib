/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Noncommuting projections and small amplification overlap

This module constructs two real rank-one projections in dimension two whose amplification
overlap can be arbitrarily small, illustrating the noncommutativity issue discussed in
[PoulinWocjan2009]. It also proves that a matrix commuting with `Q` preserves vectors fixed by
`Q`.

## Main statements

* `noncommuting_failure`: noncommuting projections with overlap below any positive tolerance.
* `commuting_case_preserves_range`: preservation of the fixed-vector condition under
  commutation.

## References

* [Poulin and Wocjan, 2009][PoulinWocjan2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.GroundState08.MainResults.NaiveFailure

/-- The first coordinate vector in real dimension two. -/
def e0 : Fin 2 → ℝ := ![1, 0]

/-- The orthogonal projection onto the first coordinate axis in real dimension two. -/
def qProj : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]

/-- The unit vector with coordinates `cos θ` and `sin θ`. -/
def tiltVec (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- The rank-one orthogonal projection onto the line spanned by `tiltVec θ`. -/
def rProj (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => tiltVec θ i * tiltVec θ j

/-- The real coordinatewise inner product of two vectors in dimension two. -/
def innerVec (u v : Fin 2 → ℝ) : ℝ := ∑ i, u i * v i

/-- The ratio of the inner product of `rProj θ *ᵥ e0` with its `qProj` image to its squared
norm. -/
def amplificationOverlap (θ : ℝ) : ℝ :=
  innerVec (rProj θ *ᵥ e0) (qProj *ᵥ (rProj θ *ᵥ e0)) /
    innerVec (rProj θ *ᵥ e0) (rProj θ *ᵥ e0)

/-- The projection `qProj` fixes the first coordinate vector. -/
lemma qProj_mulVec_e0 : qProj *ᵥ e0 = e0 := by
  funext i
  fin_cases i <;>
    simp [qProj, e0, Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- Projecting the first coordinate vector onto the tilted line yields `cos θ` times `tiltVec
θ`. -/
lemma rProj_mulVec_e0 (θ : ℝ) :
    rProj θ *ᵥ e0 = Real.cos θ • tiltVec θ := by
  funext i
  fin_cases i <;>
    simp [rProj, tiltVec, e0, Matrix.mulVec, dotProduct]
  ring

/-- Projecting the tilted unit vector onto the first coordinate axis yields `cos θ` times `e0`. -/
lemma qProj_mulVec_tiltVec (θ : ℝ) :
    qProj *ᵥ tiltVec θ = Real.cos θ • e0 := by
  funext i
  fin_cases i <;>
    simp [qProj, tiltVec, e0, Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- The tilted vector has squared norm one. -/
lemma innerVec_tiltVec_self (θ : ℝ) : innerVec (tiltVec θ) (tiltVec θ) = 1 := by
  simp [innerVec, tiltVec]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- The amplification overlap of the two projections equals `cos θ ^ 2` [PoulinWocjan2009]. -/
lemma amplificationOverlap_eq_cos_sq (θ : ℝ) :
    amplificationOverlap θ = Real.cos θ ^ 2 := by
  have hnum : innerVec (rProj θ *ᵥ e0) (qProj *ᵥ (rProj θ *ᵥ e0)) =
      Real.cos θ ^ 2 * Real.cos θ ^ 2 := by
    rw [rProj_mulVec_e0, Matrix.mulVec_smul, qProj_mulVec_tiltVec]
    simp only [innerVec, tiltVec, e0, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have hden : innerVec (rProj θ *ᵥ e0) (rProj θ *ᵥ e0) = Real.cos θ ^ 2 := by
    rw [rProj_mulVec_e0]
    simp only [innerVec, tiltVec, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  unfold amplificationOverlap
  rw [hnum, hden]
  by_cases hc : Real.cos θ = 0
  · simp [hc]
  · field_simp

/-- The coordinate and tilted projections do not commute when `0 < θ < π/2` [PoulinWocjan2009]. -/
lemma qProj_rProj_ne_comm (θ : ℝ) (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    qProj * rProj θ ≠ rProj θ * qProj := by
  intro heq
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hle : (qProj * rProj θ) 0 1 = (rProj θ * qProj) 0 1 := by rw [heq]
  simp [qProj, rProj, tiltVec, Matrix.mul_apply, Matrix.diagonal,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hle
  have hpos : 0 < Real.cos θ * Real.sin θ := mul_pos hc hs
  rcases hle with h | h
  · rw [h] at hpos; linarith
  · rw [h] at hpos; linarith

/-- For every positive `δ`, some angle strictly between zero and `π/2` has squared cosine less
than `δ`. -/
lemma exists_angle_cos_sq_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧ Real.cos θ ^ 2 < δ := by
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / Real.sqrt δ)
  have hNpos : 0 < N := by
    have : 0 < 1 / Real.sqrt δ := by positivity
    exact_mod_cast lt_trans this hN
  refine ⟨Real.pi / 2 - 1 / ((N : ℝ) + 1), ?_, ?_, ?_⟩
  · have hxle : 1 / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    nlinarith [Real.pi_gt_three]
  · have hxpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  · have hxlt : 1 / ((N : ℝ) + 1) < Real.sqrt δ := by
      rw [div_lt_iff₀ (by positivity)]
      have hN' : (N : ℝ) < (N : ℝ) + 1 := by linarith
      have hprod : 1 < Real.sqrt δ * (N + 1) := by
        have h1 : 1 / Real.sqrt δ < (N : ℝ) := hN
        rw [div_lt_iff₀ hsqrt] at h1
        nlinarith
      linarith
    rw [Real.cos_pi_div_two_sub]
    have hxnonneg : 0 ≤ 1 / ((N : ℝ) + 1) := le_of_lt (by positivity)
    have hsinle : Real.sin (1 / ((N : ℝ) + 1)) ≤ 1 / ((N : ℝ) + 1) :=
      Real.sin_le hxnonneg
    have hsinpos : 0 ≤ Real.sin (1 / ((N : ℝ) + 1)) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hxnonneg (by
        have : 1 / ((N : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [Nat.cast_nonneg (α := ℝ) N]
        linarith [Real.pi_gt_three])
    have hsq : Real.sin (1 / ((N : ℝ) + 1)) ^ 2 ≤ (1 / ((N : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ hsinpos hsinle 2
    have hsq2 : (1 / ((N : ℝ) + 1)) ^ 2 < δ := by
      rw [← Real.sq_sqrt hδ.le]
      exact pow_lt_pow_left₀ hxlt (by positivity) (by norm_num)
    linarith

/-- For every positive tolerance, there are noncommuting coordinate and tilted projections whose
amplification overlap equals a squared cosine below that tolerance [PoulinWocjan2009]. -/
theorem noncommuting_failure (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      qProj * rProj θ ≠ rProj θ * qProj ∧
      amplificationOverlap θ = Real.cos θ ^ 2 ∧
      Real.cos θ ^ 2 < δ := by
  obtain ⟨θ, h0, h1, hlt⟩ := exists_angle_cos_sq_lt δ hδ
  exact ⟨θ, h0, h1, qProj_rProj_ne_comm θ h0 h1, amplificationOverlap_eq_cos_sq θ, hlt⟩

/-- If `Q` and `R` commute and `Q` fixes `ψ`, then `Q` also fixes `R *ᵥ ψ` [PoulinWocjan2009]. -/
theorem commuting_case_preserves_range
    {n : ℕ} (Q R : Matrix (Fin n) (Fin n) ℝ) (hQR : Q * R = R * Q)
    (ψ : Fin n → ℝ) (hQ : Q *ᵥ ψ = ψ) :
    Q *ᵥ (R *ᵥ ψ) = R *ᵥ ψ := by
  rw [Matrix.mulVec_mulVec, hQR, ← Matrix.mulVec_mulVec, hQ]

/-- If `Q` and `R` commute, applying `R` to a vector fixed by `Q` produces another vector fixed
by `Q`. -/
theorem commuting_overlap_eq_one
    {n : ℕ} (Q R : Matrix (Fin n) (Fin n) ℝ) (hQR : Q * R = R * Q)
    (ψ : Fin n → ℝ) (hQ : Q *ᵥ ψ = ψ) :
    Q *ᵥ (R *ᵥ ψ) = R *ᵥ ψ :=
  commuting_case_preserves_range Q R hQR ψ hQ

end Qatlib.Papers.GroundState08.MainResults.NaiveFailure
