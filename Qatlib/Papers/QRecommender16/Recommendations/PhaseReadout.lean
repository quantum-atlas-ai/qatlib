/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.WalkActions
public import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualReadout
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Phase estimation on a singular-plane eigenbranch

[KerenidisPrakash2017], Algorithm 5.1, estimates the phase of the double
reflection and then takes the half-angle cosine. For a nonnegative normalized
singular value, this module runs the powered phase-estimation word on the
positive-angle eigenbranch in the singular plane and proves its finite
nearest-grid readout bound. Both full-register branches admit the same
singular-value decoder, which uses the absolute half-angle cosine on the
phase circle.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open scoped Matrix.Norms.Frobenius BigOperators

/-- The nonnegative singular-plane eigenphase, in units of one revolution. -/
noncomputable def positivePhase (overlap : ℝ) : ℝ :=
  Real.arccos overlap / Real.pi

/-- Normalize the eigenbranch with components one and negative imaginary unit. -/
noncomputable def positiveBranch : QState Bool :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • phaseBranch false

/-- The scaled eigenbranch has unit squared norm. -/
theorem positive_branch_normalized : Normalized positiveBranch := by
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  unfold Normalized
  norm_num [positiveBranch, phaseBranch, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hTwo]

/-- The eigenphase lies in the half revolution appropriate to a nonnegative singular value. -/
theorem positive_phase_bounds (overlap : ℝ) (h : 0 ≤ overlap) :
    0 ≤ positivePhase overlap ∧ positivePhase overlap < 1 := by
  refine ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le, ?_⟩
  apply (div_lt_one Real.pi_pos).2
  exact lt_of_le_of_lt (Real.arccos_le_pi_div_two.mpr h) (by linarith [Real.pi_pos])

/-- The explicit eigenvalue is the complex exponential of twice the arccosine. -/
theorem positive_phase_eigenvalue (overlap : ℝ) (h : 0 ≤ overlap) (hOne : overlap ≤ 1) :
    phaseEigenvalue overlap false =
      Complex.exp (2 * Real.pi * Complex.I * positivePhase overlap) := by
  have hReal : 2 * Real.pi * positivePhase overlap = 2 * Real.arccos overlap := by
    unfold positivePhase
    field_simp [Real.pi_ne_zero]
  have hArg : (2 * Real.pi * Complex.I * positivePhase overlap : ℂ) =
      ((2 * Real.pi * positivePhase overlap : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hArg, hReal, Complex.exp_ofReal_mul_I, Real.cos_two_mul, Real.sin_two_mul,
    Real.cos_arccos (by linarith) hOne, Real.sin_arccos]
  simp only [phaseEigenvalue, Bool.false_eq_true, ite_false, rotationDiagonal, rotationOffDiagonal]
  push_cast
  ring

/-- The conjugate eigenphase is represented in the same unit interval as the positive
branch when the overlap is strictly below one. -/
noncomputable def singularBranchPhase (overlap : ℝ) (negative : Bool) : ℝ :=
  if negative then 1 - positivePhase overlap else positivePhase overlap

/-- Both branches use phases in the unit interval when the overlap is in `[0, 1)`. -/
theorem singular_branch_phase_bounds (overlap : ℝ) (h : 0 ≤ overlap) (hLt : overlap < 1)
    (negative : Bool) :
    0 ≤ singularBranchPhase overlap negative ∧ singularBranchPhase overlap negative < 1 := by
  have hh := positive_phase_bounds overlap h
  cases negative
  · exact hh
  · change 0 ≤ 1 - positivePhase overlap ∧ 1 - positivePhase overlap < 1
    have hPos : 0 < positivePhase overlap := div_pos (Real.arccos_pos.mpr hLt) Real.pi_pos
    exact ⟨sub_nonneg.mpr hh.2.le, by linarith⟩

/-- The conjugate eigenvalue is the exponential of the complementary phase. -/
theorem branch_phase_eigenvalue (overlap : ℝ) (h : 0 ≤ overlap) (hOne : overlap ≤ 1)
    (negative : Bool) :
    phaseEigenvalue overlap negative =
      Complex.exp (2 * Real.pi * Complex.I * singularBranchPhase overlap negative) := by
  cases negative
  · exact positive_phase_eigenvalue overlap h hOne
  · have hConj : phaseEigenvalue overlap true = (starRingEnd ℂ) (phaseEigenvalue overlap false) := by
      simp [phaseEigenvalue, Complex.conj_I]
    rw [hConj, positive_phase_eigenvalue overlap h hOne, ← Complex.exp_conj]
    have hShift :
        (2 * Real.pi * Complex.I * singularBranchPhase overlap true : ℂ) =
          2 * Real.pi * Complex.I + (starRingEnd ℂ) (2 * Real.pi * Complex.I * positivePhase overlap) := by
      have hTwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one]
      simp [singularBranchPhase, Complex.conj_I, hTwo]
      ring
    rw [hShift, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

/-- Decode a phase to a normalized nonnegative singular value. The absolute value
identifies the complementary phase and makes the decoder periodic. -/
noncomputable def foldedCosine (phase : ℝ) : ℝ := |Real.cos (Real.pi * phase)|

/-- The decoder is invariant under adding an integer number of revolutions. -/
theorem folded_cosine_add_int (phase : ℝ) (k : ℤ) :
    foldedCosine (phase + k) = foldedCosine phase := by
  have hArg : Real.pi * (phase + k) = Real.pi * phase + k * Real.pi := by ring
  rw [foldedCosine, hArg, Real.cos_add_int_mul_pi, abs_mul, abs_zpow]
  norm_num [foldedCosine]

/-- A perturbation of a circular phase changes the normalized singular estimate by
at most pi times the circular distance. -/
theorem folded_cosine_error_le (u v : ℝ) :
    |foldedCosine u - foldedCosine v| ≤ Real.pi * bhmt11CircleDist u v := by
  let k := round (v - u)
  let shifted := v + ((-k : ℤ) : ℝ)
  have he : foldedCosine shifted = foldedCosine v := folded_cosine_add_int v (-k)
  have hd : bhmt11CircleDist u v = |u - shifted| := by
    rw [bhmt_phase_estimation_theorem11_distance_round, ← abs_neg (u - shifted)]
    congr 1
    simp only [shifted, Int.cast_neg, k]
    ring
  rw [← he, hd]
  calc
    _ ≤ |Real.cos (Real.pi * u) - Real.cos (Real.pi * shifted)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ |Real.pi * u - Real.pi * shifted| := Real.abs_cos_sub_cos_le _ _
    _ = _ := by rw [← mul_sub, abs_mul, abs_of_pos Real.pi_pos]

/-- Either exact phase returns the same normalized singular value. -/
theorem folded_cosine_branch_phase (overlap : ℝ) (h : 0 ≤ overlap) (hOne : overlap ≤ 1)
    (negative : Bool) : foldedCosine (singularBranchPhase overlap negative) = overlap := by
  have hArg : Real.pi * positivePhase overlap = Real.arccos overlap := by
    unfold positivePhase
    field_simp [Real.pi_ne_zero]
  have hCos := Real.cos_arccos (by linarith : -1 ≤ overlap) hOne
  cases negative
  · change |Real.cos (Real.pi * positivePhase overlap)| = overlap
    rw [hArg, hCos, abs_of_nonneg h]
  · change |Real.cos (Real.pi * (1 - positivePhase overlap))| = overlap
    have hs : Real.pi * (1 - positivePhase overlap) = Real.pi - Real.arccos overlap := by
      rw [mul_sub, mul_one, hArg]
    rw [hs, Real.cos_pi_sub, hCos, abs_neg, abs_of_nonneg h]

/-- The executed phase-estimation word has a nearest-grid outcome with the standard probability. -/
theorem singular_phase_readout (bits : ℕ) (hBits : 2 < 2 ^ bits) (overlap : ℝ)
    (h : 0 ≤ overlap) (hOne : overlap ≤ 1) :
    ∃ outcome : Reg bits,
      bhmt11CircleDist (((bitVecEquiv bits outcome).val : ℝ) / (2 ^ bits : ℝ))
        (positivePhase overlap) ≤ 1 / (2 * (2 ^ bits : ℝ)) ∧
      4 / Real.pi ^ 2 ≤
        MeasureProb (PoweredProgram.execute (singularPlaneWalk overlap) (PoweredProgram.word bits)
          (TensorState (Ket (ZeroStr bits)) positiveBranch)) ({outcome} ×ˢ (Finset.univ : Finset Bool)) := by
  have hEigen : singularPlaneWalk overlap *ᵥ positiveBranch =
      Complex.exp (2 * Real.pi * Complex.I * positivePhase overlap) • positiveBranch := by
    unfold positiveBranch
    rw [Matrix.mulVec_smul, singular_plane_eigenbranch, ← positive_phase_eigenvalue overlap h hOne,
      smul_comm]
  exact actual_nearest_readout bits hBits _ _ (positive_phase_bounds overlap h).1
    (positive_phase_bounds overlap h).2 _ positive_branch_normalized hEigen

/-- An orthonormal real frame preserves the sum of squared coordinates. -/
private theorem sum_sq_mulVec {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    (P : Matrix R C ℝ) (hP : Pᵀ * P = 1) (v : C → ℝ) :
    ∑ i, (P *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
  simp only [pow_two]
  change (P *ᵥ v) ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ v
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

/-- The two embeddings of a unit singular pair remain unit and have inner product equal to
the singular value divided by the matrix Frobenius norm. -/
theorem singular_images_geometry {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) :
    let a := isometryP A *ᵥ left
    let b := isometryQ A *ᵥ right
    (∑ i, a i ^ 2) = 1 ∧ (∑ i, b i ^ 2) = 1 ∧ (∑ i, a i * b i) = (‖A‖)⁻¹ * singular := by
  refine ⟨(sum_sq_mulVec _ (isometryP_orthonormal A hRows) left).trans hLeft,
    (sum_sq_mulVec _ (isometryQ_orthonormal A hA) right).trans hRight, ?_⟩
  simpa [div_eq_mul_inv, mul_comm] using
    singular_cosine_relation A left right singular hRows hA hLeft hPair

/-- Normalization removes the sine scale from each full-register eigenbranch. -/
noncomputable def fullNormalizedBranch {rows columns : ℕ} (overlap : ℝ) (negative : Bool)
    (leftImage rightImage : Fin rows × Fin columns → ℝ) : QState (Fin rows × Fin columns) :=
  ((Real.sqrt (2 * (1 - overlap ^ 2)) : ℝ) : ℂ)⁻¹ •
    fullPhaseBranch overlap negative leftImage rightImage

/-- The full-register branch with the nonnegative eigenphase. -/
noncomputable def fullPositiveBranch {rows columns : ℕ} (overlap : ℝ)
    (leftImage rightImage : Fin rows × Fin columns → ℝ) : QState (Fin rows × Fin columns) :=
  fullNormalizedBranch overlap false leftImage rightImage

/-- For two unit real images with inner product `overlap`, either full-register branch
has unit norm whenever the overlap has magnitude strictly less than one. -/
theorem full_normalized_branch_normalized {rows columns : ℕ} (overlap : ℝ) (negative : Bool)
    (a b : Fin rows × Fin columns → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = overlap) (hOverlap : overlap ^ 2 < 1) :
    Normalized (fullNormalizedBranch overlap negative a b) := by
  let s := Real.sqrt (1 - overlap ^ 2)
  have hs : s ^ 2 = 1 - overlap ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hOverlap.le)
  have hResidual : (∑ i, (a i - overlap * b i) ^ 2) = 1 - overlap ^ 2 := by
    simp_rw [sub_sq, mul_pow, show ∀ i, 2 * a i * (overlap * b i) =
      (2 * overlap) * (a i * b i) from fun i => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ha, hb, hab]
    ring
  have hBranch : ∀ i, ‖fullPhaseBranch overlap negative a b i‖ ^ 2 =
      (s * b i) ^ 2 + (a i - overlap * b i) ^ 2 := by
    intro i
    rw [← Complex.normSq_eq_norm_sq]
    cases negative
    · have hAmp : fullPhaseBranch overlap false a b i =
          ((s * b i : ℝ) : ℂ) + ((-(a i - overlap * b i) : ℝ) : ℂ) * Complex.I := by
        simp only [fullPhaseBranch, s, Bool.false_eq_true, ite_false, Complex.ofReal_neg]
        ring
      rw [hAmp, Complex.normSq_add_mul_I, neg_sq]
    · have hAmp : fullPhaseBranch overlap true a b i =
          ((s * b i : ℝ) : ℂ) + ((a i - overlap * b i : ℝ) : ℂ) * Complex.I := by
        simp only [fullPhaseBranch, s, ite_true]
        ring
      rw [hAmp, Complex.normSq_add_mul_I]
  have hScale : 0 < 2 * (1 - overlap ^ 2) := mul_pos (by norm_num) (sub_pos.mpr hOverlap)
  unfold Normalized
  simp only [fullNormalizedBranch, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt hScale.le, hBranch]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hb, hResidual, hs, mul_one, ← two_mul]
  exact inv_mul_cancel₀ hScale.ne'

/-- The positive full-register eigenbranch is normalized. -/
theorem full_positive_branch_normalized {rows columns : ℕ} (overlap : ℝ)
    (a b : Fin rows × Fin columns → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = overlap) (hOverlap : overlap ^ 2 < 1) :
    Normalized (fullPositiveBranch overlap a b) :=
  full_normalized_branch_normalized overlap false a b ha hb hab hOverlap

/-- The powered phase-estimation word on the actual reflection product resolves the positive
eigenphase of an interior singular pair with the nearest-grid guarantee. -/
theorem full_walk_phase_readout {rows columns : ℕ} (bits : ℕ) (hBits : 2 < 2 ^ bits)
    (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) (hTransposePair : Aᵀ *ᵥ left = singular • right)
    (hNonneg : 0 ≤ (‖A‖)⁻¹ * singular) (hLt : (‖A‖)⁻¹ * singular < 1) :
    let overlap := (‖A‖)⁻¹ * singular
    let branch := fullPositiveBranch overlap (isometryP A *ᵥ left) (isometryQ A *ᵥ right)
    ∃ outcome : Reg bits,
      bhmt11CircleDist (((bitVecEquiv bits outcome).val : ℝ) / (2 ^ bits : ℝ))
        (positivePhase overlap) ≤ 1 / (2 * (2 ^ bits : ℝ)) ∧
      4 / Real.pi ^ 2 ≤ MeasureProb
        (PoweredProgram.execute ((bireflectionWalk A).map Complex.ofReal) (PoweredProgram.word bits)
          (TensorState (Ket (ZeroStr bits)) branch))
        ({outcome} ×ˢ (Finset.univ : Finset (Fin rows × Fin columns))) := by
  let overlap := (‖A‖)⁻¹ * singular
  let a := isometryP A *ᵥ left
  let b := isometryQ A *ᵥ right
  have hOverlap : overlap ^ 2 < 1 := by
    have hNonneg' : 0 ≤ overlap := hNonneg
    have hLt' : overlap < 1 := hLt
    nlinarith [mul_nonneg hNonneg' (sub_nonneg.mpr hLt'.le)]
  have hg := singular_images_geometry A hRows hA left right singular hLeft hRight hPair
  have hNorm : Normalized (fullPositiveBranch overlap a b) :=
    full_positive_branch_normalized overlap a b hg.1 hg.2.1 hg.2.2 hOverlap
  have hRaw : (bireflectionWalk A).map Complex.ofReal *ᵥ fullPhaseBranch overlap false a b =
      phaseEigenvalue overlap false • fullPhaseBranch overlap false a b :=
    walk_mulVec_phase_branch A hRows hA left right singular hPair hTransposePair false hOverlap.le
  have hEigen : (bireflectionWalk A).map Complex.ofReal *ᵥ fullPositiveBranch overlap a b =
      Complex.exp (2 * Real.pi * Complex.I * positivePhase overlap) • fullPositiveBranch overlap a b := by
    unfold fullPositiveBranch fullNormalizedBranch
    rw [Matrix.mulVec_smul, hRaw, positive_phase_eigenvalue overlap hNonneg hLt.le, smul_comm]
  exact actual_nearest_readout bits hBits _ _ (positive_phase_bounds overlap hNonneg).1
    (positive_phase_bounds overlap hNonneg).2 _ hNorm hEigen

end Qatlib.Papers.QRecommender16.Recommendations
