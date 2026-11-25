/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.PhaseReadout
public import Qatlib.Papers.QRecommender16.Recommendations.ThresholdFlag
public import Qatlib.Papers.QRecommender16.Recommendations.ThresholdSampling
public import Qatlib.Foundations.BornMetrics.EventProbability
public import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualDyadicReadout
public import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualWindowMass

@[expose] public section

/-!
# Singular-value estimates on an embedded right singular vector

[KerenidisPrakash2017], Algorithm 5.1, starts the walk from the image of
the right singular vector. At normalized singular value below one,
the image is the equal superposition of two orthogonal phase branches.
The actual counting register estimates their common singular value
with the circular-window success bound. At zero overlap the two phases
coincide. At unit overlap the right image is fixed by the walk, giving
an exact zero phase. A separated cutoff converts readout accuracy to a
correct threshold decision.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability (measureProb_le_one)
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open scoped Matrix.Norms.Frobenius Classical BigOperators

variable {rows columns : ℕ}

/-- The residual of the left image after projection onto the right image has squared norm
`1 - overlap^2` and is orthogonal to the right image. -/
private theorem singular_image_remainder (overlap : ℝ) (a b : Fin rows × Fin columns → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = overlap) :
    (∑ i, (a i - overlap * b i) ^ 2) = 1 - overlap ^ 2 ∧
      (∑ i, b i * (a i - overlap * b i)) = 0 := by
  constructor
  · simp_rw [sub_sq, mul_pow, show ∀ i, 2 * a i * (overlap * b i) =
        (2 * overlap) * (a i * b i) from fun i => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ha, hb, hab]
    ring
  · simp_rw [show ∀ i, b i * (a i - overlap * b i) = a i * b i - overlap * b i ^ 2
        from fun i => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hab, hb, mul_one, sub_self]

/-- The conjugate branches are orthogonal, even at the endpoint where their eigenvalues
coincide. Their equal real and imaginary squared norms cancel in the cross inner product. -/
private theorem inner_normalized_branches_zero (overlap : ℝ) (a b : Fin rows × Fin columns → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = overlap) (hOverlap : overlap ^ 2 < 1) :
    Inner (fullNormalizedBranch overlap false a b) (fullNormalizedBranch overlap true a b) = 0 := by
  let s := Real.sqrt (1 - overlap ^ 2)
  let r := fun i => a i - overlap * b i
  let d : ℂ := ((Real.sqrt (2 * (1 - overlap ^ 2)) : ℝ) : ℂ)⁻¹
  have hs : s ^ 2 = 1 - overlap ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hOverlap.le)
  obtain ⟨hNorm, hInner⟩ := singular_image_remainder overlap a b ha hb hab
  have hPoint (i : Fin rows × Fin columns) :
      (starRingEnd ℂ) (fullNormalizedBranch overlap false a b i) *
        fullNormalizedBranch overlap true a b i =
      d ^ 2 * (((s ^ 2 * b i ^ 2 - r i ^ 2 : ℝ) : ℂ) +
        ((2 * s * (b i * r i) : ℝ) : ℂ) * Complex.I) := by
    simp only [fullNormalizedBranch, fullPhaseBranch, d, s, r, Pi.smul_apply, smul_eq_mul,
      Bool.false_eq_true, ite_false, ite_true, map_mul, map_add, map_inv₀, map_neg,
      Complex.conj_ofReal, Complex.conj_I, neg_neg]
    push_cast
    linear_combination d ^ 2 * ((a i : ℂ) - (overlap : ℂ) * (b i : ℂ)) ^ 2 * Complex.I_sq
  have hReal : (∑ i, (s ^ 2 * b i ^ 2 - r i ^ 2)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hb, mul_one, hs, hNorm, sub_self]
  have hImag : (∑ i, 2 * s * (b i * r i)) = 0 := by
    rw [← Finset.mul_sum, hInner, mul_zero]
  rw [inner_apply]
  simp_rw [hPoint]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp_rw [← Complex.ofReal_sum, hReal, hImag]
  simp

/-- The two full-register branches form an orthonormal family. -/
theorem full_branches_orthonormal (overlap : ℝ) (a b : Fin rows × Fin columns → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hab : ∑ i, a i * b i = overlap) (hOverlap : overlap ^ 2 < 1) :
    ∀ j k : Bool, Inner (fullNormalizedBranch overlap j a b) (fullNormalizedBranch overlap k a b) =
      if j = k then 1 else 0 := by
  have hOff := inner_normalized_branches_zero overlap a b ha hb hab hOverlap
  have hDiag (j : Bool) : Inner (fullNormalizedBranch overlap j a b) (fullNormalizedBranch overlap j a b) = 1 :=
    (normalized_iff_inner_self _).mp (full_normalized_branch_normalized overlap j a b ha hb hab hOverlap)
  intro j k
  cases j <;> cases k
  · simpa only [ite_true] using hDiag false
  · simpa only [Bool.false_eq_true, ite_false] using hOff
  · rw [Qatlib.Foundations.PureStateMath.BornBridge.inner_conj_symm, hOff]
    simp
  · simpa only [ite_true] using hDiag true

/-- The two orthonormal branches with equal real weights reconstruct the unmodified
right singular image. -/
theorem right_image_eq_phase_sum (overlap : ℝ) (a b : Fin rows × Fin columns → ℝ)
    (hOverlap : overlap ^ 2 < 1) :
    (fun i => (b i : ℂ)) =
      ∑ j : Bool, ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • fullNormalizedBranch overlap j a b := by
  let s : ℂ := (Real.sqrt (1 - overlap ^ 2) : ℝ)
  let t : ℂ := (Real.sqrt 2 : ℝ)
  have hDen : (Real.sqrt (2 * (1 - overlap ^ 2)) : ℂ) = t * s := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Complex.ofReal_mul]
  have hs : s ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hOverlap)).ne'
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have htSq : t ^ 2 = 2 := by
    change ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : t⁻¹ * (t * s)⁻¹ * (2 * s) = 1 := by
    rw [← htSq]
    field_simp [ht, hs]
  funext i
  rw [Fintype.sum_bool]
  simp only [fullNormalizedBranch, fullPhaseBranch, hDen, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Bool.false_eq_true, ite_false, ite_true, Complex.ofReal_mul]
  change (b i : ℂ) = t⁻¹ * ((t * s)⁻¹ * (s * (b i : ℂ) + Complex.I * _)) +
    t⁻¹ * ((t * s)⁻¹ * (s * (b i : ℂ) + -Complex.I * _))
  calc
    (b i : ℂ) = (t⁻¹ * (t * s)⁻¹ * (2 * s)) * (b i : ℂ) := by rw [hc, one_mul]
    _ = _ := by ring

/-- Convert a measured counting-register label to its phase in revolutions. -/
noncomputable def registerPhase {bits : ℕ} (label : Reg bits) : ℝ :=
  ((bitVecEquiv bits label).val : ℝ) / (2 ^ bits : ℝ)

/-- Decode a measured label to a singular value in the units of the original matrix. -/
noncomputable def singularReadoutValue {bits : ℕ} (scale : ℝ) (label : Reg bits) : ℝ :=
  scale * foldedCosine (registerPhase label)

/-- For an embedded right singular vector, the actual powered circuit has the expected
singular-value accuracy on a counting-register event with the circular-window success bound. -/
theorem right_singular_readout_success (bits : ℕ) (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) (hTransposePair : Aᵀ *ᵥ left = singular • right)
    (hNonneg : 0 ≤ (‖A‖)⁻¹ * singular) (hLt : (‖A‖)⁻¹ * singular < 1)
    (window : ℝ) (hWindow : 1 < window) :
    let U := (bireflectionWalk A).map Complex.ofReal
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    let good := Finset.univ.filter fun label : Reg bits =>
      |singularReadoutValue ‖A‖ label - singular| ≤ ‖A‖ * (Real.pi * (window / (2 ^ bits : ℝ)))
    1 - 1 / (2 * (window - 1)) ≤ MeasureProb
      (PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ))
      (good ×ˢ (Finset.univ : Finset (Fin rows × Fin columns))) := by
  intro U ψ good
  let overlap := (‖A‖)⁻¹ * singular
  let a := isometryP A *ᵥ left
  let b := isometryQ A *ᵥ right
  let branch := fun negative => fullNormalizedBranch overlap negative a b
  let coefficient : Bool → ℂ := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  let phase := singularBranchPhase overlap
  have hOverlap : overlap ^ 2 < 1 := by
    have h0 : 0 ≤ overlap := hNonneg
    have h1 : overlap < 1 := hLt
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1.le)]
  obtain ⟨ha, hb, hab⟩ := singular_images_geometry A hRows hA left right singular hLeft hRight hPair
  have hGram (j k : Bool) : Inner (branch j) (branch k) =
      @ite ℂ (j = k) (Classical.propDecidable (j = k)) 1 0 := by
    have h := full_branches_orthonormal overlap a b ha hb hab hOverlap j k
    by_cases heq : j = k <;> simpa [heq] using h
  have hEigen (j : Bool) : U *ᵥ branch j = Complex.exp (2 * Real.pi * Complex.I * phase j) • branch j := by
    have hRaw := walk_mulVec_phase_branch A hRows hA left right singular hPair hTransposePair j hOverlap.le
    change U *ᵥ (((Real.sqrt (2 * (1 - overlap ^ 2)) : ℝ) : ℂ)⁻¹ •
      fullPhaseBranch overlap j a b) = _
    rw [Matrix.mulVec_smul, hRaw, branch_phase_eigenvalue overlap hNonneg hLt.le j]
    exact smul_comm _ _ _
  have hScale : ‖A‖ * overlap = singular := by
    unfold overlap
    rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  have hEach (j : Bool) :
      1 - 1 / (2 * (window - 1)) ≤
        MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
          (TensorState (Ket (ZeroStr bits)) (branch j))) (good ×ˢ Finset.univ) := by
    have hn := full_normalized_branch_normalized overlap j a b ha hb hab hOverlap
    refine (actual_window_tail bits U (phase j) (branch j) hn (hEigen j) window hWindow).trans ?_
    unfold actualWindowMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [good, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
      have hDecode := folded_cosine_error_le (registerPhase p.1) (phase j)
      rw [folded_cosine_branch_phase overlap hNonneg hLt.le j] at hDecode
      rw [singularReadoutValue, ← hScale, ← mul_sub, abs_mul, abs_of_pos hA]
      exact mul_le_mul_of_nonneg_left
        (hDecode.trans (mul_le_mul_of_nonneg_left hp Real.pi_pos.le)) hA.le
    · intro p _ _
      exact bornProb_nonneg _ _
  have hInput : ψ = ∑ j, coefficient j • branch j := right_image_eq_phase_sum overlap a b hOverlap
  rw [hInput, powered_word_spectral_event bits U branch coefficient phase hGram hEigen]
  have hWeight (j : Bool) : ‖coefficient j‖ ^ 2 = 1 / 2 := by
    have hTwo : (0 : ℝ) ≤ 2 := by norm_num
    simp [coefficient, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hTwo, one_div]
  calc
    _ = ∑ j, ‖coefficient j‖ ^ 2 * (1 - 1 / (2 * (window - 1))) := by
      simp only [Fintype.sum_bool, hWeight]
      ring
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hEach j) (sq_nonneg _)

/-- At unit normalized singular value the embedded right singular vector is fixed by the walk. -/
theorem right_unit_image_fixed (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) (hUnit : (‖A‖)⁻¹ * singular = 1) :
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    (bireflectionWalk A).map Complex.ofReal *ᵥ ψ = ψ := by
  intro ψ
  let a := isometryP A *ᵥ left
  let b := isometryQ A *ᵥ right
  obtain ⟨ha, hb, hab⟩ := singular_images_geometry A hRows hA left right singular hLeft hRight hPair
  have hResidual := (singular_image_remainder 1 a b ha hb (hab.trans hUnit)).1
  simp only [one_mul, one_pow, sub_self] at hResidual
  have hSame : a = b := by
    funext i
    have hTerm : (a i - b i) ^ 2 ≤ 0 :=
      (Finset.single_le_sum (f := fun j => (a j - b j) ^ 2)
        (fun j _ => sq_nonneg (a j - b j)) (Finset.mem_univ i)).trans_eq hResidual
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hTerm (sq_nonneg _)))
  have hFix : bireflectionWalk A *ᵥ b = b := by
    have h := walk_mulVec_right_singular_image A hRows hA left right singular hPair
    change bireflectionWalk A *ᵥ b = 2 • (((‖A‖)⁻¹ * singular) • a) - b at h
    simpa only [hUnit, one_smul, hSame, two_smul, add_sub_cancel_right] using h
  funext i
  exact (RingHom.map_mulVec Complex.ofRealHom (bireflectionWalk A) b i).symm.trans
    (congrArg (fun v : Fin rows × Fin columns → ℝ => (v i : ℂ)) hFix)

/-- At unit normalized singular value the right image is fixed by the walk.
The actual phase word then returns a label whose decoded value is exact. -/
theorem right_singular_readout_unit_overlap (bits : ℕ) (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) (hUnit : (‖A‖)⁻¹ * singular = 1) :
    let U := (bireflectionWalk A).map Complex.ofReal
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    ∃ label : Reg bits, singularReadoutValue ‖A‖ label = singular ∧
      MeasureProb
        (PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ))
        ({label} ×ˢ (Finset.univ : Finset (Fin rows × Fin columns))) = 1 := by
  intro U ψ
  have hFixed : U *ᵥ ψ = ψ :=
    right_unit_image_fixed A hRows hA left right singular hLeft hRight hPair hUnit
  have hb := (singular_images_geometry A hRows hA left right singular hLeft hRight hPair).2.1
  have hn : Normalized ψ := by
    unfold Normalized
    simpa [ψ, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb
  let zero : Fin (2 ^ bits) := ⟨0, Nat.two_pow_pos bits⟩
  have he : U *ᵥ ψ = Complex.exp (2 * Real.pi * Complex.I *
      ((zero.val : ℝ) / (2 ^ bits : ℝ) : ℝ)) • ψ := by
    simpa [zero] using hFixed
  have hScale : ‖A‖ = singular := by
    calc
      _ = ‖A‖ * ((‖A‖)⁻¹ * singular) := by rw [hUnit, mul_one]
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]
  refine ⟨(bitVecEquiv bits).symm zero, ?_, actual_dyadic_readout bits zero U ψ hn he⟩
  simpa [singularReadoutValue, registerPhase, foldedCosine, zero] using hScale

/-- A right null vector gives a single eigenphase of one half, whose folded
value is zero. This includes null vectors without a matching left singular vector. -/
theorem right_null_image_phase (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (right : Fin columns → ℝ) (hNull : A *ᵥ right = 0) :
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    (bireflectionWalk A).map Complex.ofReal *ᵥ ψ =
      Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) • ψ ∧
      foldedCosine (1 / 2) = 0 := by
  intro ψ
  have hPhase : (2 : ℂ) * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  constructor
  · rw [hPhase, Complex.exp_pi_mul_I, neg_one_smul]
    exact walk_mulVec_right_null_image A hRows hA right hNull
  · rw [foldedCosine, show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two, abs_zero]

/-- A measured label classifies an interior right singular vector correctly with the
window success bound whenever the singular value is outside the threshold transition interval. -/
theorem right_singular_threshold_success (bits : ℕ) (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hLeft : ∑ i, left i ^ 2 = 1) (hRight : ∑ i, right i ^ 2 = 1)
    (hPair : A *ᵥ right = singular • left) (hTransposePair : Aᵀ *ᵥ left = singular • right)
    (hNonneg : 0 ≤ (‖A‖)⁻¹ * singular) (hLt : (‖A‖)⁻¹ * singular < 1)
    (window cutoff halfWidth : ℝ) (hWindow : 1 < window)
    (hResolution : ‖A‖ * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hOutside : singular < cutoff - 2 * halfWidth ∨ cutoff ≤ singular) :
    let U := (bireflectionWalk A).map Complex.ofReal
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    let correct := Finset.univ.filter fun label : Reg bits =>
      (cutoff - halfWidth ≤ singularReadoutValue ‖A‖ label) ↔ cutoff ≤ singular
    1 - 1 / (2 * (window - 1)) ≤ MeasureProb
      (PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ))
      (correct ×ˢ (Finset.univ : Finset (Fin rows × Fin columns))) := by
  intro U ψ correct
  refine (right_singular_readout_success bits A hRows hA left right singular hLeft hRight
    hPair hTransposePair hNonneg hLt window hWindow).trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [correct, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    have hError := hp.trans hResolution
    rcases hOutside with hBelow | hAbove
    · have hd := estimate_discards_below _ _ _ _ hError hBelow
      have hWidth : 0 ≤ halfWidth := (abs_nonneg _).trans hError
      exact iff_of_false (not_le_of_gt hd) (not_le_of_gt (by linarith))
    · exact iff_of_true (estimate_keeps_above _ _ _ _ hError hAbove) hAbove
  · intro p _ _
    exact bornProb_nonneg _ _

/-- The decoded counting-register threshold classifies one normalized eigenstate
within the phase-window failure bound, provided its value lies outside the transition interval. -/
theorem threshold_acceptance_on_eigenstate_error {I : Type} [Fintype I] [DecidableEq I]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (phase value : ℝ) (hn : Normalized ψ)
    (hEigen : U *ᵥ ψ = Complex.exp (2 * Real.pi * Complex.I * phase) • ψ)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValue : scale * foldedCosine phase = value)
    (hOutside : value < cutoff - 2 * halfWidth ∨ cutoff ≤ value) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) ψ)) (accepted ×ˢ (Finset.univ : Finset I)) -
        (if cutoff ≤ value then 1 else 0)| ≤ 1 / (2 * (window - 1)) := by
  intro accepted
  let pass := accepted ×ˢ (Finset.univ : Finset I)
  let out := PoweredProgram.execute U (PoweredProgram.word bits) (TensorState (Ket (ZeroStr bits)) ψ)
  let near := (Finset.univ.filter fun z : Reg bits =>
    bhmt11CircleDist (registerPhase z) phase ≤ window / (2 ^ bits : ℝ)) ×ˢ (Finset.univ : Finset I)
  have hTotal : MeasureProb out Finset.univ = 1 :=
    measureProb_univ (PoweredProgram.execute_normalized hU _
      (normalized_tensorState (normalized_ket _) hn))
  have hMono (s t : Finset (Reg bits × I)) (hst : s ⊆ t) :
      MeasureProb out s ≤ MeasureProb out t :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun p _ _ => bornProb_nonneg out p)
  have hNear : 1 - 1 / (2 * (window - 1)) ≤ MeasureProb out near :=
    actual_window_tail bits U phase ψ hn hEigen window hWindow
  have hAccuracy (p : Reg bits × I) (hp : p ∈ near) :
      |singularReadoutValue scale p.1 - value| ≤ halfWidth := by
    simp only [near, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp
    rw [singularReadoutValue, ← hValue, ← mul_sub, abs_mul, abs_of_pos hScale]
    exact (mul_le_mul_of_nonneg_left ((folded_cosine_error_le _ _).trans
      (mul_le_mul_of_nonneg_left hp Real.pi_pos.le)) hScale.le).trans hResolution
  have hWindowNonneg : 0 ≤ window := (zero_lt_one.trans hWindow).le
  have hWidth : 0 ≤ halfWidth := (show 0 ≤ scale * (Real.pi * (window / (2 ^ bits : ℝ))) by
    positivity).trans hResolution
  change |MeasureProb out pass - (if cutoff ≤ value then 1 else 0)| ≤ _
  rcases hOutside with hBelow | hAbove
  · have hNo : ¬ cutoff ≤ value := not_le_of_gt (by linarith)
    have hDisjoint : Disjoint pass near := by
      apply Finset.disjoint_left.mpr
      intro p hp hpn
      have hReject := estimate_discards_below _ _ _ _ (hAccuracy p hpn) hBelow
      simp only [pass, accepted, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true] at hp
      exact (not_le_of_gt hReject) hp
    have hSum : MeasureProb out pass + MeasureProb out near ≤ 1 := by
      have hUnion := hMono (pass ∪ near) Finset.univ (Finset.subset_univ _)
      rw [hTotal] at hUnion
      simpa only [MeasureProb, Finset.sum_union hDisjoint] using hUnion
    rw [ite_eq_right hNo, sub_zero, abs_of_nonneg (measureProb_nonneg _ _)]
    linarith only [hSum, hNear]
  · have hSubset : near ⊆ pass := by
      intro p hp
      simp only [pass, accepted, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true]
      exact estimate_keeps_above _ _ _ _ (hAccuracy p hp) hAbove
    have hLower := hNear.trans (hMono near pass hSubset)
    have hUpper := (hMono pass Finset.univ (Finset.subset_univ _)).trans_eq hTotal
    rw [ite_eq_left hAbove, abs_of_nonpos (sub_nonpos.mpr hUpper)]
    linarith only [hLower]

/-- For a supplied orthonormal spectrum with decoded values separated from the
transition interval, the measured acceptance probability approximates the ideal
weight of the retained components on the entire input superposition. -/
theorem spectral_threshold_weight_error {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, scale * foldedCosine (phase j) = value j)
    (hOutside : ∀ j, value j < cutoff - 2 * halfWidth ∨ cutoff ≤ value j) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        ∑ j, ‖c j‖ ^ 2 * (if cutoff ≤ value j then 1 else 0)| ≤ 1 / (2 * (window - 1)) := by
  intro accepted
  refine powered_spectral_acceptance_error bits U v c phase hOrthogonal hEigen hCoefficients
    accepted (fun j => cutoff ≤ value j) _ ?_
  intro j
  exact threshold_acceptance_on_eigenstate_error bits U hU (v j) (phase j) (value j)
    ((normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)) (hEigen j)
    scale window cutoff halfWidth hScale hWindow hResolution (hValues j) (hOutside j)

/-- Coherently recording a separated threshold and reversing phase estimation
approximates the ideal retained spectral state on the unnormalized success branch. -/
theorem spectral_threshold_flag_error {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, scale * foldedCosine (phase j) = value j)
    (hOutside : ∀ j, value j < cutoff - 2 * halfWidth ∨ cutoff ≤ value j) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    let result := executeThresholdFlag bits U accepted (∑ j, c j • v j)
    let ideal := TensorState (Ket (ZeroStr bits)) (∑ j, (if cutoff ≤ value j then c j else 0) • v j)
    ∑ p : Reg bits × I, ‖result (true, p) - ideal p‖ ^ 2 ≤ 1 / (2 * (window - 1)) := by
  intro accepted result ideal
  have hError := powered_threshold_flag_error bits U hU v c phase hOrthogonal hEigen
    accepted (fun j => cutoff ≤ value j) (fun _ => 1 / (2 * (window - 1))) (fun j =>
      threshold_acceptance_on_eigenstate_error bits U hU (v j) (phase j) (value j)
        ((normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)) (hEigen j)
        scale window cutoff halfWidth hScale hWindow hResolution (hValues j) (hOutside j))
  simpa only [← Finset.sum_mul, hCoefficients, one_mul] using hError

/-- The one-sided transition interval between guaranteed rejection and guaranteed retention. -/
def thresholdTransition (cutoff halfWidth value : ℝ) : Prop :=
  cutoff - 2 * halfWidth ≤ value ∧ value < cutoff

/-- A threshold selection retains all directions at or above the cutoff and discards
all directions below the transition interval. Each direction in the interval is optional. -/
def IsThresholdSelection {J : Type} (value : J → ℝ) (cutoff halfWidth : ℝ) (keep : J → Prop) : Prop :=
  (∀ j, cutoff ≤ value j → keep j) ∧ (∀ j, value j < cutoff - 2 * halfWidth → ¬ keep j)

/-- Keeping exactly the directions at or above the cutoff is an admissible selection. -/
theorem is_threshold_selection_cutoff {J : Type} (value : J → ℝ) (cutoff halfWidth : ℝ)
    (hWidth : 0 ≤ halfWidth) : IsThresholdSelection value cutoff halfWidth (fun j => cutoff ≤ value j) := by
  refine ⟨fun _ h => h, fun j hBelow hKeep => ?_⟩
  linarith only [hWidth, hBelow, hKeep]

/-- The input weight carried by the spectral branches in the threshold transition interval. -/
def spectralTransitionMass {J : Type} [Fintype J] (c : J → ℂ) (value : J → ℝ)
    (cutoff halfWidth : ℝ) : ℝ :=
  ∑ j, ‖c j‖ ^ 2 * (if thresholdTransition cutoff halfWidth (value j) then 1 else 0)

/-- An arbitrary spectrum is allowed at the threshold. Branches outside the transition interval
obey the phase-estimation error bound, and each branch inside contributes at most its own weight
to the squared error of the unnormalized success state relative to any admissible selection. -/
theorem spectral_threshold_band_error {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, scale * foldedCosine (phase j) = value j)
    (keep : J → Prop) (hSelection : IsThresholdSelection value cutoff halfWidth keep) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    let result := executeThresholdFlag bits U accepted (∑ j, c j • v j)
    let ideal := TensorState (Ket (ZeroStr bits)) (∑ j, (if keep j then c j else 0) • v j)
    ∑ p : Reg bits × I, ‖result (true, p) - ideal p‖ ^ 2 ≤
      1 / (2 * (window - 1)) + spectralTransitionMass c value cutoff halfWidth := by
  intro accepted result ideal
  let tail : ℝ := 1 / (2 * (window - 1))
  have hTail : 0 ≤ tail :=
    div_nonneg zero_le_one (mul_nonneg (by norm_num) (sub_nonneg.mpr hWindow.le))
  let bound j := tail + if thresholdTransition cutoff halfWidth (value j) then 1 else 0
  have hDecision (j : J) : |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        (if keep j then 1 else 0)| ≤ bound j := by
    have hn : Normalized (v j) := (normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)
    by_cases hBand : thresholdTransition cutoff halfWidth (value j)
    · have hOutput := PoweredProgram.execute_normalized hU (PoweredProgram.word bits)
        (normalized_tensorState (normalized_ket (ZeroStr bits)) hn)
      have hOne := measureProb_le_one hOutput (accepted ×ˢ (Finset.univ : Finset I))
      have hZero := measureProb_nonneg (PoweredProgram.execute U (PoweredProgram.word bits)
        (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I))
      rw [abs_le]
      simp only [bound, hBand, ite_true]
      by_cases h : keep j <;> simp only [h, ite_true, ite_false] <;>
        exact ⟨by linarith only [hZero, hTail], by linarith only [hOne, hTail]⟩
    · by_cases hUpper : cutoff ≤ value j
      · have hRetained := hSelection.1 j hUpper
        simpa only [bound, hBand, ite_false, add_zero, hUpper, hRetained, ite_true] using
          threshold_acceptance_on_eigenstate_error bits U hU (v j) (phase j) (value j) hn (hEigen j)
            scale window cutoff halfWidth hScale hWindow hResolution (hValues j) (Or.inr hUpper)
      · have hLower : value j < cutoff - 2 * halfWidth :=
          lt_of_not_ge fun h => hBand ⟨h, lt_of_not_ge hUpper⟩
        have hDiscarded := hSelection.2 j hLower
        simpa only [bound, hBand, ite_false, add_zero, hUpper, hDiscarded] using
          threshold_acceptance_on_eigenstate_error bits U hU (v j) (phase j) (value j) hn (hEigen j)
            scale window cutoff halfWidth hScale hWindow hResolution (hValues j) (Or.inl hLower)
  have hError := powered_threshold_flag_error bits U hU v c phase hOrthogonal hEigen
    accepted keep bound hDecision
  have hBudget : (∑ j, ‖c j‖ ^ 2 * bound j) = tail + spectralTransitionMass c value cutoff halfWidth := by
    simp only [bound, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hCoefficients, one_mul,
      spectralTransitionMass]
  exact hError.trans_eq hBudget

/-- Every eigenbranch above the cutoff contributes at least its squared input weight times
the phase-estimation success bound to the actual flag probability. The other branches
contribute nonnegative probability. -/
theorem spectral_threshold_success_lower {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, scale * foldedCosine (phase j) = value j) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    (1 - 1 / (2 * (window - 1))) * (∑ j, ‖c j‖ ^ 2 * (if cutoff ≤ value j then 1 else 0)) ≤
      MeasureProb (executeThresholdFlag bits U accepted (∑ j, c j • v j))
        ({true} ×ˢ (Finset.univ : Finset (Reg bits × I))) := by
  intro accepted
  rw [execute_threshold_flag_probability bits U hU, powered_word_spectral_event bits U v c phase hOrthogonal hEigen,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  let τ : ℝ := 1 / (2 * (window - 1))
  calc
    _ = ‖c j‖ ^ 2 * ((1 - τ) * (if cutoff ≤ value j then 1 else 0)) := by dsimp [τ]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      by_cases h : cutoff ≤ value j
      · have hNear := threshold_acceptance_on_eigenstate_error bits U hU (v j) (phase j) (value j)
          ((normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)) (hEigen j)
          scale window cutoff halfWidth hScale hWindow hResolution (hValues j) (Or.inr h)
        simp only [h, ite_true, mul_one] at hNear ⊢
        change 1 - 1 / (2 * (window - 1)) ≤ _
        linarith only [(abs_le.mp hNear).1]
      · simpa only [h, ite_false, mul_zero] using
          measureProb_nonneg (PoweredProgram.execute U (PoweredProgram.word bits)
            (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I))

end Qatlib.Papers.QRecommender16.Recommendations
