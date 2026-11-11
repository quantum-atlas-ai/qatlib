/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.MetricSpace.Lipschitz

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixContour.ContourCalc
open Qatlib.Foundations.OpCalculus.ContourCalc

/-!
# Local polynomial approximation of the actual matrix resolvent

Numerical-range separation supplies the inverse laws and the operator-norm
bound for the literal pseudoinverse resolvent.  A finite geometric telescope
then gives the exact defect of the literal local polynomial.  The argument
uses only positive powers in its norm estimate and includes empty matrices.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Qatlib.Concepts.MatrixContour.ContourCalc

open scoped BigOperators Matrix.Norms.L2Operator

/-- Numerical-range separation certifies the canonical resolvent itself. -/
theorem matrixResolvent_inverse_norm_of_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖) :
    matrixShift A z * matrixResolvent A z = 1 ∧
      matrixResolvent A z * matrixShift A z = 1 ∧
      ‖matrixResolvent A z‖ ≤ r⁻¹ := by
  obtain ⟨R, hZR, hRZ, hnorm, heq⟩ :=
    exists_matrix_resolvent_of_numericalRange_separation A z r hr hsep
  simpa only [matrixShift, matrixResolvent, heq] using ⟨hZR, hRZ, hnorm⟩

/-- The literal coefficient sum is the finite geometric sum with its leading
resolvent factored out.  Complex scalar multiplication is central. -/
theorem localResolventPolynomial_eq_geometric
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z₀ : ℂ) (m : ℕ) (z : ℂ) :
    localResolventPolynomial A z₀ m z =
      matrixResolvent A z₀ *
        ∑ n ∈ Finset.range (m + 1), (-(z - z₀) • matrixResolvent A z₀) ^ n := by
  unfold localResolventPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [_root_.smul_pow, mul_smul_comm, ← pow_succ']

/-- The finite telescope needs no commutativity between resolvents at distinct
points.  Its inverse-law hypotheses are discharged by separation below. -/
theorem localResolventPolynomial_defect_of_inverse
    {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (z₀ z : ℂ) (m : ℕ)
    (h₀ : matrixShift A z₀ * matrixResolvent A z₀ = 1)
    (hz : matrixResolvent A z * matrixShift A z = 1) :
    matrixResolvent A z - localResolventPolynomial A z₀ m z =
      matrixResolvent A z * (-(z - z₀) • matrixResolvent A z₀) ^ (m + 1) := by
  let S := -(z - z₀) • matrixResolvent A z₀
  have hshift : matrixShift A z = matrixShift A z₀ + (z - z₀) • 1 := by
    simp only [matrixShift, sub_smul]
    abel
  have hZR₀ : matrixShift A z * matrixResolvent A z₀ = 1 - S := by
    rw [hshift, add_mul, h₀, smul_mul_assoc, one_mul]
    simp [S]
  have hZP : matrixShift A z * localResolventPolynomial A z₀ m z =
      1 - S ^ (m + 1) := by
    rw [localResolventPolynomial_eq_geometric, ← mul_assoc, hZR₀]
    exact mul_neg_geom_sum S (m + 1)
  have hP := congrArg (fun B => matrixResolvent A z * B) hZP
  rw [← mul_assoc, hz, one_mul, mul_sub, mul_one] at hP
  change matrixResolvent A z - localResolventPolynomial A z₀ m z =
    matrixResolvent A z * S ^ (m + 1)
  rw [hP]
  abel

/-- G18: separation bounds the exact finite local-resolvent defect by a
geometric tail, for the actual canonical pseudoinverse target. -/
theorem local_resolvent_approximation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (z₀ z : ℂ) (r : ℝ) (m : ℕ)
    (hr : 0 < r)
    (hsep₀ : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z₀ - w‖)
    (hsepz : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖)
    (hnear : ‖z - z₀‖ ≤ r / 8) :
    matrixResolvent A z - localResolventPolynomial A z₀ m z =
      matrixResolvent A z * (-(z - z₀) • matrixResolvent A z₀) ^ (m + 1) ∧
    ‖matrixResolvent A z - localResolventPolynomial A z₀ m z‖ ≤
      r⁻¹ * (1 / 8 : ℝ) ^ (m + 1) := by
  obtain ⟨h₀, _hR₀, hnorm₀⟩ :=
    matrixResolvent_inverse_norm_of_separation A z₀ r hr hsep₀
  obtain ⟨_hz, hRz, hnormz⟩ :=
    matrixResolvent_inverse_norm_of_separation A z r hr hsepz
  have hdefect := localResolventPolynomial_defect_of_inverse A z₀ z m h₀ hRz
  let S := -(z - z₀) • matrixResolvent A z₀
  have hS : ‖S‖ ≤ (1 / 8 : ℝ) := by
    calc
      ‖S‖ = ‖z - z₀‖ * ‖matrixResolvent A z₀‖ := by simp [S, norm_smul]
      _ ≤ (r / 8) * r⁻¹ :=
        mul_le_mul hnear hnorm₀ (norm_nonneg _) (by positivity)
      _ = (r * r⁻¹) / 8 := by ring
      _ = 1 / 8 := by rw [mul_inv_cancel₀ hr.ne']
  refine ⟨hdefect, ?_⟩
  rw [hdefect]
  change ‖matrixResolvent A z * S ^ (m + 1)‖ ≤ r⁻¹ * (1 / 8 : ℝ) ^ (m + 1)
  calc
    ‖matrixResolvent A z * S ^ (m + 1)‖ ≤
        ‖matrixResolvent A z‖ * ‖S ^ (m + 1)‖ := norm_mul_le _ _
    _ ≤ r⁻¹ * ‖S‖ ^ (m + 1) :=
      mul_le_mul hnormz (norm_pow_le' S (Nat.succ_pos m))
        (norm_nonneg _) (inv_nonneg.mpr hr.le)
    _ ≤ r⁻¹ * (1 / 8 : ℝ) ^ (m + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hS _)
        (inv_nonneg.mpr hr.le)

/-- The actual resolvents satisfy the resolvent identity wherever both points
have numerical-range separation; no local-distance hypothesis is needed. -/
theorem matrixResolvent_sub_of_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (w z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsepw : ∀ u ∈ matrixNumericalRange A, r ≤ ‖w - u‖)
    (hsepz : ∀ u ∈ matrixNumericalRange A, r ≤ ‖z - u‖) :
    matrixResolvent A z - matrixResolvent A w =
      -(z - w) • (matrixResolvent A z * matrixResolvent A w) := by
  obtain ⟨hw, _hRw, _hnormw⟩ :=
    matrixResolvent_inverse_norm_of_separation A w r hr hsepw
  obtain ⟨_hz, hRz, _hnormz⟩ :=
    matrixResolvent_inverse_norm_of_separation A z r hr hsepz
  have h := localResolventPolynomial_defect_of_inverse A w z 0 hw hRz
  simpa [localResolventPolynomial, mul_smul_comm] using h

/-- Uniform separation gives a dimension-free operator-norm Lipschitz bound
for the actual canonical resolvent. -/
theorem matrixResolvent_norm_sub_le_of_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (w z : ℂ) (r : ℝ) (hr : 0 < r)
    (hsepw : ∀ u ∈ matrixNumericalRange A, r ≤ ‖w - u‖)
    (hsepz : ∀ u ∈ matrixNumericalRange A, r ≤ ‖z - u‖) :
    ‖matrixResolvent A z - matrixResolvent A w‖ ≤
      (r⁻¹ * r⁻¹) * ‖z - w‖ := by
  obtain ⟨_hw, _hRw, hnormw⟩ :=
    matrixResolvent_inverse_norm_of_separation A w r hr hsepw
  obtain ⟨_hz, _hRz, hnormz⟩ :=
    matrixResolvent_inverse_norm_of_separation A z r hr hsepz
  rw [matrixResolvent_sub_of_separation A w z r hr hsepw hsepz]
  calc
    ‖-(z - w) • (matrixResolvent A z * matrixResolvent A w)‖ =
        ‖z - w‖ * ‖matrixResolvent A z * matrixResolvent A w‖ := by
      simp only [norm_smul, norm_neg]
    _ ≤ ‖z - w‖ * (‖matrixResolvent A z‖ * ‖matrixResolvent A w‖) :=
      mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ‖z - w‖ * (r⁻¹ * r⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hnormz hnormw (norm_nonneg _) (inv_nonneg.mpr hr.le))
        (norm_nonneg _)
    _ = (r⁻¹ * r⁻¹) * ‖z - w‖ := mul_comm _ _

/-- The resolvent is Lipschitz on the full set certified by a fixed positive
numerical-range separation. -/
theorem matrixResolvent_lipschitzOn_of_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (r : ℝ) (hr : 0 < r) :
    LipschitzOnWith ⟨r⁻¹ * r⁻¹, mul_self_nonneg _⟩ (matrixResolvent A)
      {z | ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖} := by
  refine LipschitzOnWith.of_dist_le_mul (K := ⟨r⁻¹ * r⁻¹, mul_self_nonneg _⟩) ?_
  intro z hz w hw
  rw [dist_eq_norm,dist_eq_norm]
  change ‖matrixResolvent A z - matrixResolvent A w‖ ≤ (r⁻¹ * r⁻¹) * ‖z-w‖
  exact matrixResolvent_norm_sub_le_of_separation A w z r hr hw hz

/-- Uniform separation supplies the continuity needed by a contour panel. -/
theorem matrixResolvent_continuousOn_of_separation
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ)
    (r : ℝ) (hr : 0 < r) :
    ContinuousOn (matrixResolvent A)
      {z | ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖} :=
  (matrixResolvent_lipschitzOn_of_separation A r hr).continuousOn

end Qatlib.Concepts.MatrixContour.ContourCalc
