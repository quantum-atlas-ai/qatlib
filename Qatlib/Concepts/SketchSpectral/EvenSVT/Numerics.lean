/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.NumericsDefs
import Qatlib.Concepts.SketchSpectral.EvenSVT.RationalMachineBridge

/-!
# Numerical bounds and cost identities for even SVT

The module verifies row and column tail budgets, normalized frame identities, and spectral
bounds for the numerical constructions in `NumericsDefs`. It also proves fixed-point value
identities and explicit access, RAM-operation, bit-time, and workspace formulas for the
sampling-based matrix arithmetic of [ChiaEtAl2022].

## Main statements

* `rowTailBudget`: The row budget bounds the Lipschitz-weighted row tail scale, including its
  rank logarithm factor, by `ε / 2`.
* `frameOperator_eq_gram`: The weighted frame operator equals the Gram matrix `Ccᴴ * Cc`.
* `clause8_endpoint`: Combines the two half-error tail budgets, the frame Gram identity, the
  Rayleigh bound, and the exact two-stage runtime formula.
* `clause9_endpoint`: Combines the explicit repeated-sketch read, multiplication, RAM,
  workspace, and bit-time formulas with the RAM-to-bit-time bound.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.Difference
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CacheOp
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SketchSpectral.MatrixFunctions

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.EvenSVT
namespace ConstructionStageB
namespace StageBSQNUMERICS

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

/-- The rank logarithm factor `1 + log (1 + r)` is at least one. -/
theorem rankLogFactor_ge_one (r : ℕ) : 1 ≤ rankLogFactor r := by
  unfold rankLogFactor
  have h := Real.log_nonneg (show (1 : ℝ) ≤ 1 + (r : ℝ) by
    exact le_add_of_nonneg_right (Nat.cast_nonneg r))
  linarith

/-- The rank logarithm factor is strictly positive. -/
theorem rankLogFactor_pos (r : ℕ) : 0 < rankLogFactor r :=
  lt_of_lt_of_le zero_lt_one (rankLogFactor_ge_one r)

/-- The rank logarithm factor is monotone in its natural-number argument. -/
theorem rankLogFactor_mono : Monotone rankLogFactor := by
  intro m n hmn
  unfold rankLogFactor
  have hR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlog : Real.log (1 + (m : ℝ)) ≤ Real.log (1 + (n : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  linarith

/-- For `0 < δ < 1`, the concentration logarithm `log (2 / (δ / 3))` is positive. -/
theorem log_two_over_delta_third_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 / (δ / 3)) := by
  have h : 1 < 2 / (δ / 3) := by
    have hδ3 : 0 < δ / 3 := div_pos hδ (by norm_num)
    have heq : 2 / (δ / 3) = 6 / δ := by
      field_simp
      ring
    rw [heq]
    exact (lt_div_iff₀ hδ).2 (by linarith)
  exact Real.log_pos h

/-- A bound on the radicand by the square of nonnegative `s` bounds the corresponding tail
square root by `s`. -/
theorem tailRoot_le {φ δ n s : ℝ} (hs : 0 ≤ s)
    (h : 8 * φ ^ 2 * Real.log (2 / (δ / 3)) / n ≤ s ^ 2) :
    Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / n) ≤ s := by
  rw [Real.sqrt_le_iff]
  exact ⟨hs, h⟩

/-- For positive `ε`, the required row-sample inequality is equivalent to the
denominator-cleared row budget. -/
theorem requiredRowSamples_le_iff {L ε φ δ E : ℝ} {rank r : ℕ} (hε : 0 < ε) :
    requiredRowSamples L ε φ δ E rank ≤ (r : ℝ) ↔ rowBudgetMul L ε φ δ E rank r := by
  unfold requiredRowSamples rowBudgetMul
  rw [div_le_iff₀ (sq_pos_of_pos hε)]
  constructor
  · intro h
    rw [mul_comm (r : ℝ) (ε ^ 2)] at h
    exact h
  · intro h
    rw [mul_comm (r : ℝ) (ε ^ 2)]
    exact h

/-- For positive `ε`, the required column-sample inequality is equivalent to the
denominator-cleared column budget. -/
theorem requiredColSamples_le_iff {M Lbar ε φ δ E : ℝ} {rank c : ℕ} (hε : 0 < ε) :
    requiredColSamples M Lbar ε φ δ E rank ≤ (c : ℝ) ↔ colBudgetMul M Lbar ε φ δ E rank c := by
  unfold requiredColSamples colBudgetMul
  rw [div_le_iff₀ (sq_pos_of_pos hε)]
  constructor
  · intro h
    rw [mul_comm (c : ℝ) (ε ^ 2)] at h
    exact h
  · intro h
    rw [mul_comm (c : ℝ) (ε ^ 2)]
    exact h

/-- The row budget bounds the Lipschitz-weighted row tail scale, including its rank logarithm
factor, by `ε / 2`. -/
theorem rowTailBudget {L ε φ δ E : ℝ} {rank r : ℕ}
    (hL : 0 < L) (hε : 0 < ε) (hφ : 1 ≤ φ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hE : 0 ≤ E) (hr : 0 < r)
    (hbudget : rowBudgetMul L ε φ δ E rank r) :
    L * rankLogFactor rank * rowTailScale φ δ r E ≤ ε / 2 := by
  have hlog : 0 < Real.log (2 / (δ / 3)) := log_two_over_delta_third_pos hδ hδ1
  have hrl : 0 < rankLogFactor rank := rankLogFactor_pos rank
  have hφpos : 0 < φ := lt_of_lt_of_le zero_lt_one hφ
  by_cases hE0 : E = 0
  · simp [hE0, rowTailScale]
    linarith
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
    have hLR : 0 < L * rankLogFactor rank := mul_pos hL hrl
    have hLRE : 0 < L * rankLogFactor rank * E := mul_pos hLR hEpos
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
    have hC0 : 0 < 4 * (L * rankLogFactor rank) ^ 2 * E ^ 2 := by positivity
    have hCne : 4 * (L * rankLogFactor rank) ^ 2 * E ^ 2 ≠ 0 := ne_of_gt hC0
    have hkey : 8 * φ ^ 2 * Real.log (2 / (δ / 3))
          * (4 * (L * rankLogFactor rank) ^ 2 * E ^ 2)
        ≤ ε ^ 2 * (r : ℝ) := by
      have h := hbudget
      unfold rowBudgetMul at h
      calc 8 * φ ^ 2 * Real.log (2 / (δ / 3))
            * (4 * (L * rankLogFactor rank) ^ 2 * E ^ 2)
          = 32 * φ ^ 2 * Real.log (2 / (δ / 3))
            * (L * rankLogFactor rank) ^ 2 * E ^ 2 := by ring
        _ ≤ ε ^ 2 * (r : ℝ) := h
    have hA : 8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ)
        ≤ ε ^ 2 / (4 * (L * rankLogFactor rank) ^ 2 * E ^ 2) := by
      rw [div_le_iff₀ hrpos, div_mul_eq_mul_div, le_div_iff₀ hC0]
      exact hkey
    set s : ℝ := ε / (2 * (L * rankLogFactor rank) * E) with hs
    have hs0 : 0 < s := div_pos hε (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hLR) hEpos)
    have hseq : ε ^ 2 / (4 * (L * rankLogFactor rank) ^ 2 * E ^ 2) = s ^ 2 := by
      dsimp [s]
      have hne : 2 * (L * rankLogFactor rank) * E ≠ 0 := by
        have h1 : 0 < 2 * (L * rankLogFactor rank) * E := by
          calc 0 < (2 : ℝ) * (L * rankLogFactor rank * E) := mul_pos (by norm_num) hLRE
            _ = 2 * (L * rankLogFactor rank) * E := by ring
        exact ne_of_gt h1
      rw [div_pow]
      have hsq : (2 * (L * rankLogFactor rank) * E) ^ 2
          = 4 * (L * rankLogFactor rank) ^ 2 * E ^ 2 := by
        have hA : (2 * (L * rankLogFactor rank) * E) ^ 2
            = 4 * ((L * rankLogFactor rank) * E) ^ 2 := by
          have hx : 2 * (L * rankLogFactor rank) * E
              = 2 * ((L * rankLogFactor rank) * E) := by ring
          rw [hx, mul_pow]
          congr 1
          norm_num
        rw [hA, mul_pow]
        ring
      rw [hsq]
    have hroot : Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ)) ≤ s := by
      apply tailRoot_le hs0.le
      linarith
    have hmul : L * rankLogFactor rank * E
          * Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ))
        ≤ L * rankLogFactor rank * E * s :=
      mul_le_mul_of_nonneg_left hroot hLRE.le
    have hscale : L * rankLogFactor rank * E * s = ε / 2 := by
      dsimp [s]
      have hne : 2 * (L * rankLogFactor rank) * E ≠ 0 := by
        have h1 : 0 < 2 * (L * rankLogFactor rank) * E := by
          calc 0 < (2 : ℝ) * (L * rankLogFactor rank * E) := mul_pos (by norm_num) hLRE
            _ = 2 * (L * rankLogFactor rank) * E := by ring
        exact ne_of_gt h1
      field_simp
    unfold rowTailScale
    linarith

/-- The column budget bounds the norm- and Lipschitz-weighted column tail scale, including its
rank logarithm factor, by `ε / 2`. -/
theorem colTailBudget {M Lbar ε φ δ E : ℝ} {rank c : ℕ}
    (hM : 0 < M) (hLbar : 0 < Lbar) (hε : 0 < ε) (hφ : 1 ≤ φ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 0 ≤ E) (hc : 0 < c)
    (hbudget : colBudgetMul M Lbar ε φ δ E rank c) :
    M * Lbar * rankLogFactor rank * colTailScale φ δ c E ≤ ε / 2 := by
  have hlog : 0 < Real.log (2 / (δ / 3)) := log_two_over_delta_third_pos hδ hδ1
  have hrl : 0 < rankLogFactor rank := rankLogFactor_pos rank
  have hφpos : 0 < φ := lt_of_lt_of_le zero_lt_one hφ
  by_cases hE0 : E = 0
  · simp [hE0, colTailScale]
    linarith
  · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hE0)
    have hMLR : 0 < M * Lbar * rankLogFactor rank := mul_pos (mul_pos hM hLbar) hrl
    have hMLRE : 0 < M * Lbar * rankLogFactor rank * E := mul_pos hMLR hEpos
    have hcpos : 0 < (c : ℝ) := by exact_mod_cast hc
    have hC0 : 0 < 16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 := by positivity
    have hCne : 16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 ≠ 0 := ne_of_gt hC0
    have hkey : 8 * φ ^ 2 * Real.log (2 / (δ / 3))
          * (16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2)
        ≤ ε ^ 2 * (c : ℝ) := by
      have h := hbudget
      unfold colBudgetMul at h
      calc 8 * φ ^ 2 * Real.log (2 / (δ / 3))
            * (16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2)
          = 128 * φ ^ 2 * Real.log (2 / (δ / 3))
            * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 := by ring
        _ ≤ ε ^ 2 * (c : ℝ) := h
    have hA : 8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)
        ≤ ε ^ 2 / (16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2) := by
      rw [div_le_iff₀ hcpos, div_mul_eq_mul_div, le_div_iff₀ hC0]
      exact hkey
    set s : ℝ := ε / (4 * (M * Lbar * rankLogFactor rank) * E) with hs
    have hs0 : 0 < s :=
      div_pos hε (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hMLR) hEpos)
    have hseq : ε ^ 2 / (16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2) = s ^ 2 := by
      dsimp [s]
      have hne : 4 * (M * Lbar * rankLogFactor rank) * E ≠ 0 := by
        have h1 : 0 < 4 * (M * Lbar * rankLogFactor rank) * E := by
          calc 0 < (4 : ℝ) * (M * Lbar * rankLogFactor rank * E) :=
              mul_pos (by norm_num) hMLRE
            _ = 4 * (M * Lbar * rankLogFactor rank) * E := by ring
        exact ne_of_gt h1
      rw [div_pow]
      have hsq : (4 * (M * Lbar * rankLogFactor rank) * E) ^ 2
          = 16 * (M * Lbar * rankLogFactor rank) ^ 2 * E ^ 2 := by
        have hA : (4 * (M * Lbar * rankLogFactor rank) * E) ^ 2
            = 16 * ((M * Lbar * rankLogFactor rank) * E) ^ 2 := by
          have hx : 4 * (M * Lbar * rankLogFactor rank) * E
              = 4 * ((M * Lbar * rankLogFactor rank) * E) := by ring
          rw [hx, mul_pow]
          congr 1
          norm_num
        rw [hA, mul_pow]
        ring
      rw [hsq]
    have hroot : Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) ≤ s := by
      apply tailRoot_le hs0.le
      linarith
    have hmul : M * Lbar * rankLogFactor rank * (2 * E)
          * Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ))
        ≤ M * Lbar * rankLogFactor rank * (2 * E) * s :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    have hscale : M * Lbar * rankLogFactor rank * (2 * E) * s = ε / 2 := by
      dsimp [s]
      have hne : 4 * (M * Lbar * rankLogFactor rank) * E ≠ 0 := by
        have h1 : 0 < 4 * (M * Lbar * rankLogFactor rank) * E := by
          calc 0 < (4 : ℝ) * (M * Lbar * rankLogFactor rank * E) :=
              mul_pos (by norm_num) hMLRE
            _ = 4 * (M * Lbar * rankLogFactor rank) * E := by ring
        exact ne_of_gt h1
      field_simp
      norm_num
    unfold colTailScale
    linarith

/-- When the column oversampling factor is at most twice the row factor, its tail scale is at
most four times the row tail scale at the same sample count. -/
theorem colTailScale_le_four_mul_row {φrow φcol δ E : ℝ} {c : ℕ}
    (hrow : 0 ≤ φrow) (hcol0 : 0 ≤ φcol) (hcol : φcol ≤ 2 * φrow) (hc : 0 < c)
    (hlog : 0 ≤ Real.log (2 / (δ / 3))) (hE : 0 ≤ E) :
    colTailScale φcol δ c E ≤ 4 * rowTailScale φrow δ c E := by
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast hc
  have hsq : φcol ^ 2 ≤ 4 * φrow ^ 2 := by
    have h2φrow : 0 ≤ 2 * φrow := by linarith
    have h1 : φcol ^ 2 ≤ (2 * φrow) ^ 2 := (sq_le_sq₀ hcol0 h2φrow).2 hcol
    nlinarith [h1]
  have hprod : 8 * φcol ^ 2 * Real.log (2 / (δ / 3))
      ≤ 8 * (4 * φrow ^ 2) * Real.log (2 / (δ / 3)) := by
    have hmul : 8 * φcol ^ 2 ≤ 8 * (4 * φrow ^ 2) := by nlinarith [hsq]
    have h := mul_le_mul_of_nonneg_right hmul hlog
    calc 8 * φcol ^ 2 * Real.log (2 / (δ / 3))
        ≤ (8 * (4 * φrow ^ 2)) * Real.log (2 / (δ / 3)) := h
      _ = 8 * (4 * φrow ^ 2) * Real.log (2 / (δ / 3)) := by ring
  have hkey : 8 * φcol ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)
      ≤ 4 * (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) := by
    calc 8 * φcol ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)
        ≤ (8 * (4 * φrow ^ 2) * Real.log (2 / (δ / 3))) / (c : ℝ) :=
          div_le_div_of_nonneg_right hprod (by positivity)
      _ = 4 * (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) := by ring
  have hnonneg : 0 ≤ 8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ) := by
    have : 0 ≤ 8 * φrow ^ 2 * Real.log (2 / (δ / 3)) := by positivity
    positivity
  have hroot : Real.sqrt (8 * φcol ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ))
      ≤ 2 * Real.sqrt (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) := by
    have hsqs : (2 * Real.sqrt (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ))) ^ 2
        = 4 * (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt hnonneg]
      ring
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    linarith
  unfold colTailScale rowTailScale
  nlinarith

/-- A frame row has zero weight exactly when every entry of that row is zero. -/
theorem frameWeight_eq_zero_iff {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) (i : C) :
    frameWeight Cc i = 0 ↔ ∀ j, Cc i j = 0 := by
  constructor
  · intro h j
    have h0 : (∑ k, Complex.normSq (Cc i k)) = 0 := by
      unfold frameWeight at h
      exact h
    have hall : (∀ k ∈ (Finset.univ : Finset R), Complex.normSq (Cc i k) = 0) :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun k => Complex.normSq (Cc i k))
        (s := (Finset.univ : Finset R)) (fun k _ => Complex.normSq_nonneg _)).mp h0
    exact Complex.normSq_eq_zero.mp (hall j (Finset.mem_univ j))
  · intro h
    simp [frameWeight, h]

/-- For a nonzero row weight, multiplying the normalized row outer product by its weight
recovers the original row outer product. -/
theorem frame_row_scale {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) (i : C) (hw : frameWeight Cc i ≠ 0) (k l : R) :
    (frameWeight Cc i : ℂ) * (star (frameUnit Cc i k) * frameUnit Cc i l)
      = star (Cc i k) * Cc i l := by
  have hwpos : 0 < frameWeight Cc i := lt_of_le_of_ne
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Ne.symm hw)
  have hunit : ∀ j, frameUnit Cc i j = Cc i j * (frameScale Cc i : ℂ) := by
    intro j
    simp [frameUnit, hw]
  have hstar : star (frameScale Cc i : ℂ) = (frameScale Cc i : ℂ) := by
    simp
  have hr : (frameScale Cc i : ℝ) ^ 2 = (frameWeight Cc i)⁻¹ := by
    unfold frameScale
    rw [inv_pow, Real.sq_sqrt hwpos.le]
  have hwr : (frameWeight Cc i : ℂ) * ((frameScale Cc i : ℂ) * (frameScale Cc i : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have hreal : frameWeight Cc i * ((frameScale Cc i : ℝ) * (frameScale Cc i : ℝ)) = 1 := by
      rw [← sq, hr, mul_inv_cancel₀ (ne_of_gt hwpos)]
    exact_mod_cast hreal
  rw [hunit k, hunit l, star_mul, hstar]
  calc (frameWeight Cc i : ℂ)
        * ((frameScale Cc i : ℂ) * star (Cc i k) * (Cc i l * (frameScale Cc i : ℂ)))
      = (frameWeight Cc i : ℂ) * ((frameScale Cc i : ℂ) * (frameScale Cc i : ℂ))
          * (star (Cc i k) * Cc i l) := by ring
    _ = 1 * (star (Cc i k) * Cc i l) := by rw [hwr]
    _ = star (Cc i k) * Cc i l := by ring

/-- The weighted normalized row outer product recovers the original row outer product, including
zero rows. -/
theorem frame_row_outer {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) (i : C) (k l : R) :
    (frameWeight Cc i : ℂ) * (frameProjection (frameUnit Cc i)) k l
      = star (Cc i k) * Cc i l := by
  by_cases hw : frameWeight Cc i = 0
  · have hrow : ∀ j, Cc i j = 0 := (frameWeight_eq_zero_iff Cc i).mp hw
    simp [frameProjection, frameUnit, hw, hrow k, hrow l]
  · simp only [frameProjection]
    exact frame_row_scale Cc i hw k l

/-- The weighted frame operator equals the Gram matrix `Ccᴴ * Cc`. -/
theorem frameOperator_eq_gram {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) : frameOperator Cc = Ccᴴ * Cc := by
  ext k l
  simp only [frameOperator, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact frame_row_outer Cc i k l

/-- A normalized frame row of nonzero weight has squared Euclidean norm one. -/
theorem frameUnit_norm_one {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) (i : C) (hw : frameWeight Cc i ≠ 0) :
    ∑ j, Complex.normSq (frameUnit Cc i j) = 1 := by
  have hwpos : 0 < frameWeight Cc i := lt_of_le_of_ne
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Ne.symm hw)
  have hunit : ∀ j, frameUnit Cc i j = Cc i j * (frameScale Cc i : ℂ) := by
    intro j
    simp [frameUnit, hw]
  have hr : (frameScale Cc i : ℝ) ^ 2 = (frameWeight Cc i)⁻¹ := by
    unfold frameScale
    rw [inv_pow, Real.sq_sqrt hwpos.le]
  have hsum' : (∑ j, Complex.normSq (Cc i j)) = frameWeight Cc i := by
    simp [frameWeight]
  have hmain : (∑ j, Complex.normSq (frameUnit Cc i j))
      = (∑ j, Complex.normSq (Cc i j)) * (frameScale Cc i : ℝ) ^ 2 := by
    simp only [hunit]
    simp only [Complex.normSq_mul]
    rw [← Finset.sum_mul, Complex.normSq_ofReal, sq]
  rw [hmain, hsum', hr]
  exact div_self (ne_of_gt hwpos)

/-- A normalized frame row of zero weight has every entry zero. -/
theorem frameUnit_zero_of_zero_row {C R : Type} [Fintype C] [Fintype R]
    (Cc : Matrix C R ℂ) (i : C) (h : frameWeight Cc i = 0) (j : R) :
    frameUnit Cc i j = 0 := by
  simp [frameUnit, h]

/-- The real quadratic form `numericalEigenvalue H v` is at most `‖H‖ * ‖v‖²`. -/
theorem numericalEigenvalue_le_norm {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    numericalEigenvalue H v ≤ ‖H‖ * ‖v‖ ^ 2 :=
  spectral_rayleigh_norm_bound H v

/-- The Rayleigh quotient of a nonzero vector is at most the operator norm of `H`. -/
theorem numericalRayleigh_le_norm {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) (hv : v ≠ 0) :
    numericalRayleigh H v ≤ ‖H‖ := by
  have hpos : 0 < ‖v‖ ^ 2 := by
    have h0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have h1 : (inner ℂ v (H.toEuclideanLin v)).re ≤ ‖H‖ * ‖v‖ ^ 2 := by
    exact numericalEigenvalue_le_norm H v
  have h2 : (inner ℂ v (H.toEuclideanLin v)).re / ‖v‖ ^ 2 ≤ ‖H‖ := by
    rw [div_le_iff₀ hpos]
    exact h1
  unfold numericalRayleigh
  exact h2

/-- For Hermitian `H`, its real quadratic form is the sum of eigenvalues weighted by squared
coordinates in the ordered eigenbasis. -/
theorem numericalEigenvalue_eq_spectral {I : Type} [Fintype I] [DecidableEq I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (v : EuclideanSpace ℂ I) :
    numericalEigenvalue H v
      = ∑ j, numericalSpectrum H hH j * Complex.normSq ((orderedHermitianBasis hH).repr v j) := by
  unfold numericalEigenvalue numericalSpectrum
  exact orderedHermitian_rayleigh hH v

/-- Corresponding numerical eigenvalues of Hermitian matrices differ by at most their Frobenius
distance. -/
theorem numericalSpectrum_perturbation {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (i : Fin (Fintype.card I)) :
    |numericalSpectrum A hA i - numericalSpectrum B hB i| ≤ spectralFrobenius (A - B) := by
  have hhw := ordered_hermitian_hoffman_wielandt A B hA hB
  have hterm : (numericalSpectrum A hA i - numericalSpectrum B hB i) ^ 2
      ≤ spectralFrobenius (A - B) ^ 2 := by
    have hsum : (numericalSpectrum A hA i - numericalSpectrum B hB i) ^ 2
        ≤ ∑ j, (numericalSpectrum A hA j - numericalSpectrum B hB j) ^ 2 := by
      refine Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin (Fintype.card I))))
        (f := fun j => (numericalSpectrum A hA j - numericalSpectrum B hB j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    simp only [numericalSpectrum] at hsum ⊢
    have hhh : (∑ j, (orderedHermitianValues hA j - orderedHermitianValues hB j) ^ 2)
        ≤ spectralFrobenius (A - B) ^ 2 := hhw
    linarith
  have hsq : 0 ≤ spectralFrobenius (A - B) := Real.sqrt_nonneg _
  have h1 : Real.sqrt ((numericalSpectrum A hA i - numericalSpectrum B hB i) ^ 2)
      ≤ Real.sqrt (spectralFrobenius (A - B) ^ 2) := Real.sqrt_le_sqrt hterm
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at h1
  rw [abs_of_nonneg hsq] at h1
  exact h1

/-- The two-stage access ledger records `r + c` sampler reads. -/
theorem sqTwoStageLedger_samplerReads (r c : ℕ) :
    (sqTwoStageLedger r c).samplerReads = r + c := rfl

/-- The two-stage access ledger records `r + c` probability reads. -/
theorem sqTwoStageLedger_probReads (r c : ℕ) :
    (sqTwoStageLedger r c).probReads = r + c := rfl

/-- The two-stage access ledger records `2 * r * c` point reads. -/
theorem sqTwoStageLedger_pointReads (r c : ℕ) :
    (sqTwoStageLedger r c).pointReads = 2 * r * c := rfl

/-- The total cost of the two-stage access ledger is `4 * r * c + 2 * (r + c)`. -/
theorem sqTwoStageLedger_runtime (r c : ℕ) :
    (sqTwoStageLedger r c).runtime = 4 * r * c + 2 * (r + c) := by
  simp [SqAccessLedger.runtime, sqTwoStageLedger]
  ring

/-- The sampler and probability counters of the two actual compact builders agree with the
two-stage ledger. -/
theorem sqTwoStageLedger_matches_frozen {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (r c : ℕ) (qs : FinDist K)
    (condQ : (Fin r → K) → FinDist C) (v : Fin r → K) (w : Fin c → C) :
    (compactSketchBuild qs r v).2.1 + (compactSketchBuild (condQ v) c w).2.1
      = (sqTwoStageLedger r c).samplerReads ∧
    (compactSketchBuild qs r v).2.2 + (compactSketchBuild (condQ v) c w).2.2
      = (sqTwoStageLedger r c).probReads := by
  rw [compactSketchBuild_eq, compactSketchBuild_eq]
  simp [sqTwoStageLedger]

/-- The absolute fixed-point rounding error multiplied by `2^p` is at most one. -/
theorem abs_sub_fixedRound_mul (p : ℕ) (x : ℝ) :
    |x - fixedRound p x| * pow2 p ≤ 1 := by
  have hpow : 0 < pow2 p := by
    dsimp [pow2]
    positivity
  have hpow0 : pow2 p ≠ 0 := ne_of_gt hpow
  have hfloor : (Int.floor (x * pow2 p) : ℤ) ≤ x * pow2 p := Int.floor_le _
  have hfloor1 : x * pow2 p < (Int.floor (x * pow2 p) : ℤ) + 1 := Int.lt_floor_add_one _
  have habs : |x * pow2 p - (Int.floor (x * pow2 p) : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hmain : (x - fixedRound p x) * pow2 p
      = x * pow2 p - (Int.floor (x * pow2 p) : ℝ) := by
    unfold fixedRound
    field_simp
  calc |x - fixedRound p x| * pow2 p
      = |(x - fixedRound p x) * pow2 p| := by
          rw [abs_mul, abs_of_pos hpow]
    _ = |x * pow2 p - (Int.floor (x * pow2 p) : ℝ)| := by rw [hmain]
    _ ≤ 1 := habs

/-- Multiplying a fixed-point rounded value by `2^p` gives the integer floor used in its
construction. -/
theorem fixedRound_mul_pow2 (p : ℕ) (x : ℝ) :
    fixedRound p x * pow2 p = (Int.floor (x * pow2 p) : ℝ) := by
  unfold fixedRound
  have hpow0 : pow2 p ≠ 0 := by
    dsimp [pow2]
    positivity
  field_simp

/-- Fixed-point word addition represents the sum of the represented real values. -/
theorem SqWord.add_value {p : ℕ} (a b : SqWord p) :
    (SqWord.add a b).value = a.value + b.value := by
  unfold SqWord.add SqWord.value
  push_cast
  have hne : (2 : ℝ) ^ p ≠ 0 := by positivity
  field_simp

/-- Fixed-point word multiplication represents the product of the represented real values at
doubled precision. -/
theorem SqWord.mul_value {p : ℕ} (a b : SqWord p) :
    (SqWord.mul a b).value = a.value * b.value := by
  unfold SqWord.mul SqWord.value
  push_cast
  have hne : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hne2 : (2 : ℝ) ^ (2 * p) ≠ 0 := by positivity
  have hpp : ((2 : ℝ) ^ p) ^ 2 = (2 : ℝ) ^ (2 * p) := by
    rw [← pow_mul]
    congr 1
    ring
  field_simp
  rw [hpp]

/-- Rescaling a fixed-point word to a greater precision preserves its represented value. -/
theorem SqWord.rescaleTo_value {p t : ℕ} (a : SqWord p) (h : p ≤ t) :
    (SqWord.rescaleTo a h).value = a.value := by
  unfold SqWord.rescaleTo SqWord.value
  push_cast
  have hne : (2 : ℝ) ^ t ≠ 0 := by positivity
  have hne2 : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (t - p) * (2 : ℝ) ^ p = (2 : ℝ) ^ t := by
    have hh := Nat.pow_sub_mul_pow 2 h
    exact_mod_cast hh
  field_simp
  rw [mul_assoc, hpow]

/-- The defined addition bit cost is bounded by the sum of operand mantissa widths plus one. -/
theorem SqWord.addBitCost_le {p : ℕ} (a b : SqWord p) :
    SqWord.addBitCost a b
      ≤ intBitWidth a.mantissa + intBitWidth b.mantissa + 1 := by
  unfold SqWord.addBitCost
  exact le_refl _

/-- The defined multiplication bit cost is bounded by the square of the sum of operand mantissa
widths. -/
theorem SqWord.mulBitCost_le {p : ℕ} (a b : SqWord p) :
    SqWord.mulBitCost a b
      ≤ (intBitWidth a.mantissa + intBitWidth b.mantissa) ^ 2 := by
  unfold SqWord.mulBitCost
  nlinarith [Nat.zero_le (intBitWidth a.mantissa),
    Nat.zero_le (intBitWidth b.mantissa)]

/-- The repeated sketch arithmetic ledger records `q * n * r` reads. -/
theorem sketchArithmeticLedger_reads (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).reads = q * n * r := rfl

/-- The repeated sketch arithmetic ledger records `q * 2 * n * r` multiplications. -/
theorem sketchArithmeticLedger_multiplies (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).multiplies = q * 2 * n * r := rfl

/-- The repeated sketch arithmetic ledger records `q * r` cache builds. -/
theorem sketchArithmeticLedger_cacheBuilds (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).cacheBuilds = q * r := rfl

/-- The repeated sketch arithmetic ledger records `q * c` row scalings. -/
theorem sketchArithmeticLedger_rowScales (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).rowScales = q * c := rfl

/-- The repeated sketch arithmetic ledger records `q * c` row additions. -/
theorem sketchArithmeticLedger_rowAdds (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).rowAdds = q * c := rfl

/-- The sketch arithmetic ledger records `q` repetitions. -/
theorem sketchArithmeticLedger_repeats (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).repeats = q := rfl

/-- The bit time of the repeated sketch ledger is `q` times the bit time of one repetition. -/
theorem SqBitLedger.bitTime_repeats (n r c q : ℕ) (w : ℕ) :
    (sketchArithmeticLedger n r c q).bitTime w
      = q * (sketchArithmeticLedger n r c 1).bitTime w := by
  unfold SqBitLedger.bitTime sketchArithmeticLedger
  ring

/-- The sketch ledger's RAM-operation count is `q * (n * r + 2 * n * r + r + c + c)`. -/
theorem SqBitLedger.ramOps_sketch (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).ramOps
      = q * (n * r + 2 * n * r + r + c + c) := by
  unfold SqBitLedger.ramOps sketchArithmeticLedger
  ring

/-- The sketch ledger's workspace count is `q * r` words. -/
theorem SqBitLedger.workspaceWords_sketch (n r c q : ℕ) :
    (sketchArithmeticLedger n r c q).workspaceWords = q * r := by
  unfold SqBitLedger.workspaceWords sketchArithmeticLedger
  rfl

/-- For word width at least one, the ledger's bit time is at least its RAM-operation count. -/
theorem SqBitLedger.bitTime_ge_ramOps (l : SqBitLedger) (w : ℕ) (hw : 1 ≤ w) :
    l.ramOps ≤ l.bitTime w := by
  have hww : w ≤ w * w := by nlinarith
  have hstep : ∀ x : ℕ, x ≤ x * w := by
    intro x
    have h := mul_le_mul_of_nonneg_left (show (1 : ℕ) ≤ w by omega) (Nat.zero_le x)
    simpa using! h
  have hstep2 : ∀ x : ℕ, x ≤ x * w * w := by
    intro x
    have h1 : x ≤ x * w := hstep x
    have h2 : x * w ≤ x * w * w := by
      have h := mul_le_mul_of_nonneg_left (show (1 : ℕ) ≤ w by omega) (Nat.zero_le (x * w))
      simpa using! h
    exact le_trans h1 h2
  have h1 := hstep l.reads
  have h2 := hstep2 l.multiplies
  have h3 := hstep l.cacheBuilds
  have h4 := hstep l.rowScales
  have h5 := hstep l.rowAdds
  unfold SqBitLedger.ramOps SqBitLedger.bitTime
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5

/-- For word width at least two and a positive read or multiplication count, bit time is
strictly greater than the RAM-operation count. -/
theorem SqBitLedger.bitTime_gt_ramOps (l : SqBitLedger) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < l.reads + l.multiplies) :
    l.ramOps < l.bitTime w := by
  have hww : w + 1 ≤ w * w := by nlinarith
  have hstep : ∀ x : ℕ, x ≤ x * w := by
    intro x
    have h := mul_le_mul_of_nonneg_left (show (1 : ℕ) ≤ w by omega) (Nat.zero_le x)
    simpa using! h
  have hstep2 : ∀ x : ℕ, x ≤ x * w * w := by
    intro x
    have h1 : x ≤ x * w := hstep x
    have h2 : x * w ≤ x * w * w := by
      have h := mul_le_mul_of_nonneg_left (show (1 : ℕ) ≤ w by omega) (Nat.zero_le (x * w))
      simpa using! h
    exact le_trans h1 h2
  have h3 := hstep l.cacheBuilds
  have h4 := hstep l.rowScales
  have h5 := hstep l.rowAdds
  unfold SqBitLedger.ramOps SqBitLedger.bitTime
  rcases Nat.lt_or_ge 0 l.reads with hreads | hreads
  · have h1 : l.reads + 1 ≤ l.reads * w := by
      have h2 : l.reads * 2 ≤ l.reads * w :=
        mul_le_mul_of_nonneg_left hw (Nat.zero_le l.reads)
      have h3 : l.reads + 1 ≤ l.reads * 2 := by
        have : (1 : ℕ) ≤ l.reads := hreads
        omega
      exact le_trans h3 h2
    have h2' := hstep2 l.multiplies
    have hchain : (l.reads + 1) + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds
        ≤ (l.reads * w + l.multiplies * w * w) + l.cacheBuilds * w + l.rowScales * w
          + l.rowAdds * w :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2') h3) h4) h5
    have hfin : l.reads + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds + 1
        ≤ (l.reads * w + l.multiplies * w * w) + l.cacheBuilds * w + l.rowScales * w
          + l.rowAdds * w := by
      have hre : l.reads + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds + 1
          = (l.reads + 1) + l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds := by
        omega
      rw [hre]
      exact hchain
    omega
  · have hreads0 : l.reads = 0 := Nat.eq_zero_of_le_zero hreads
    have hmp : 0 < l.multiplies := by
      have : 0 < l.reads + l.multiplies := hpos
      omega
    have h1 : l.multiplies + 1 ≤ l.multiplies * w * w := by
      have h2 : l.multiplies * 4 ≤ l.multiplies * w * w := by
        have h3 : 4 ≤ w * w := by nlinarith
        have h4 := mul_le_mul_of_nonneg_left h3 (Nat.zero_le l.multiplies)
        simpa only [Nat.mul_assoc] using! h4
      have h5 : l.multiplies + 1 ≤ l.multiplies * 4 := by
        have : (1 : ℕ) ≤ l.multiplies := hmp
        omega
      exact le_trans h5 h2
    rw [hreads0]
    have hchain : l.multiplies + 1 + l.cacheBuilds + l.rowScales + l.rowAdds
        ≤ (l.multiplies * w * w) + l.cacheBuilds * w + l.rowScales * w + l.rowAdds * w :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h3) h4) h5
    have hfin : l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds + 1
        ≤ (l.multiplies * w * w) + l.cacheBuilds * w + l.rowScales * w + l.rowAdds * w := by
      have hre : l.multiplies + l.cacheBuilds + l.rowScales + l.rowAdds + 1
          = l.multiplies + 1 + l.cacheBuilds + l.rowScales + l.rowAdds := by
        omega
      rw [hre]
      exact hchain
    omega

/-- A positive cache-build count gives a positive workspace-word count. -/
theorem SqBitLedger.workspaceWords_pos {l : SqBitLedger} (h : 0 < l.cacheBuilds) :
    0 < l.workspaceWords := by
  unfold SqBitLedger.workspaceWords
  exact h

/-- Combines the two half-error tail budgets, the frame Gram identity, the Rayleigh bound, and
the exact two-stage runtime formula. -/
theorem clause8_endpoint {L M Lbar ε φ δ E : ℝ} {rank r c : ℕ}
    {C R : Type} [Fintype C] [Fintype R]
    {I : Type} [Fintype I] [DecidableEq I]
    (Cc : Matrix C R ℂ) (H : Matrix I I ℂ) (v : EuclideanSpace ℂ I) (hv : v ≠ 0)
    (hL : 0 < L) (hM : 0 < M) (hLbar : 0 < Lbar) (hε : 0 < ε) (hφ : 1 ≤ φ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hE : 0 ≤ E) (hr : 0 < r) (hc : 0 < c)
    (hrow : rowBudgetMul L ε φ δ E rank r)
    (hcol : colBudgetMul M Lbar ε φ δ E rank c) :
    L * rankLogFactor rank * rowTailScale φ δ r E ≤ ε / 2 ∧
      M * Lbar * rankLogFactor rank * colTailScale φ δ c E ≤ ε / 2 ∧
      frameOperator Cc = Ccᴴ * Cc ∧
      numericalRayleigh H v ≤ ‖H‖ ∧
      (sqTwoStageLedger r c).runtime = 4 * r * c + 2 * (r + c) := by
  refine ⟨rowTailBudget hL hε hφ hδ hδ1 hE hr hrow, ?_,
    frameOperator_eq_gram Cc, numericalRayleigh_le_norm H v hv,
    sqTwoStageLedger_runtime r c⟩
  exact colTailBudget hM hLbar hε hφ hδ hδ1 hE hc hcol

/-- Combines the explicit repeated-sketch read, multiplication, RAM, workspace, and bit-time
formulas with the RAM-to-bit-time bound. -/
theorem clause9_endpoint (n r c q : ℕ) (w : ℕ) (hw : 1 ≤ w) :
    (sketchArithmeticLedger n r c q).reads = q * n * r ∧
      (sketchArithmeticLedger n r c q).multiplies = q * 2 * n * r ∧
      (sketchArithmeticLedger n r c q).ramOps
        = q * (n * r + 2 * n * r + r + c + c) ∧
      (sketchArithmeticLedger n r c q).workspaceWords = q * r ∧
      (sketchArithmeticLedger n r c q).bitTime w
        = q * (sketchArithmeticLedger n r c 1).bitTime w ∧
      (sketchArithmeticLedger n r c q).ramOps
        ≤ (sketchArithmeticLedger n r c q).bitTime w := by
  refine ⟨sketchArithmeticLedger_reads n r c q, sketchArithmeticLedger_multiplies n r c q,
    SqBitLedger.ramOps_sketch n r c q, SqBitLedger.workspaceWords_sketch n r c q,
    SqBitLedger.bitTime_repeats n r c q w, ?_⟩
  exact SqBitLedger.bitTime_ge_ramOps _ w hw

end

end StageBSQNUMERICS
