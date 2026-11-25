/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.RightSingularBasis
public import Qatlib.Papers.QRecommender16.Recommendations.RightSingularReadout

@[expose] public section

/-!
# The walk spectrum on embedded column inputs

[KerenidisPrakash2017], Lemma 5.3 and Algorithm 5.1, use the phases of the
reflection product to read singular values. Every right singular vector has
one branch at the null and unit-overlap endpoints, and two conjugate branches
at interior overlap. The constructed orthonormal family spans every real
column input embedded by the second isometry.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {rows columns : ℕ}

/-- A singular value lies strictly between the two one-dimensional endpoint cases. -/
def InteriorSingularValue (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : Prop :=
  0 < rightSingularValue A j ∧ rightSingularValue A j < ‖A‖

/-- Every right direction has a primary branch, and interior directions have one further branch. -/
abbrev WalkBranchIndex (A : Matrix (Fin rows) (Fin columns) ℝ) :=
  Fin columns ⊕ {j : Fin columns // InteriorSingularValue A j}

/-- The right singular index underlying a walk branch. -/
def walkBranchDirection {A : Matrix (Fin rows) (Fin columns) ℝ} : WalkBranchIndex A → Fin columns
  | .inl j => j
  | .inr j => j.val

/-- The further branch takes the conjugate of the primary interior phase. -/
def walkBranchNegative {A : Matrix (Fin rows) (Fin columns) ℝ} : WalkBranchIndex A → Bool
  | .inl _ => false
  | .inr _ => true

/-- The cosine of the angle between the two images for a positive singular value. -/
def singularOverlap (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : ℝ :=
  ‖A‖⁻¹ * rightSingularValue A j

/-- The isometry image of a right singular vector. -/
def rightWalkImage (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : Fin rows × Fin columns → ℝ :=
  isometryQ A *ᵥ rightSingularVector A j

/-- The left isometry image, used in the positive singular planes. -/
def leftWalkImage (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : Fin rows × Fin columns → ℝ :=
  isometryP A *ᵥ leftSingularVectorOfPositive A j

/-- The normalized interior branch or the embedded endpoint vector. -/
def singularDirectionBranch (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns)
    (negative : Bool) : QState (Fin rows × Fin columns) :=
  if InteriorSingularValue A j then
    fullNormalizedBranch (singularOverlap A j) negative (leftWalkImage A j) (rightWalkImage A j)
  else fun i => (rightWalkImage A j i : ℂ)

/-- The eigenphase in revolutions, with the null case at one half and the unit case at zero. -/
def singularDirectionPhase (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) (negative : Bool) : ℝ :=
  if InteriorSingularValue A j then singularBranchPhase (singularOverlap A j) negative
  else if rightSingularValue A j = 0 then 1 / 2 else 0

/-- The complex vector at a walk-spectrum index. -/
def walkSpectrumVector (A : Matrix (Fin rows) (Fin columns) ℝ) (p : WalkBranchIndex A) :
    QState (Fin rows × Fin columns) :=
  singularDirectionBranch A (walkBranchDirection p) (walkBranchNegative p)

/-- The eigenphase at a walk-spectrum index. -/
def walkSpectrumPhase (A : Matrix (Fin rows) (Fin columns) ℝ) (p : WalkBranchIndex A) : ℝ :=
  singularDirectionPhase A (walkBranchDirection p) (walkBranchNegative p)

/-- The singular value associated to a walk-spectrum index. -/
def walkSpectrumValue (A : Matrix (Fin rows) (Fin columns) ℝ) (p : WalkBranchIndex A) : ℝ :=
  rightSingularValue A (walkBranchDirection p)

/-- A two-image pairing is the pullback along the transposed first map. -/
private theorem image_dot_product {R C D : Type} [Fintype R] [Fintype C] [Fintype D]
    (P : Matrix R C ℝ) (Q : Matrix R D ℝ) (x : C → ℝ) (y : D → ℝ) :
    (P *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ ((Pᵀ * Q) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Pᵀ, Matrix.vecMul_transpose]

/-- The right isometry preserves the orthonormal right family. -/
private theorem right_image_dot (A : Matrix (Fin rows) (Fin columns) ℝ) (hA : 0 < ‖A‖)
    (j k : Fin columns) : rightWalkImage A j ⬝ᵥ rightWalkImage A k = if j = k then 1 else 0 := by
  rw [rightWalkImage, rightWalkImage, image_dot_product, isometryQ_orthonormal A hA,
    Matrix.one_mulVec, right_singular_vectors_orthonormal]

/-- The left images for distinct singular indices have zero pairing. -/
private theorem left_image_dot_off (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (j k : Fin columns) (hjk : j ≠ k) :
    leftWalkImage A j ⬝ᵥ leftWalkImage A k = 0 := by
  rw [leftWalkImage, leftWalkImage, image_dot_product, isometryP_orthonormal A hRows, Matrix.one_mulVec]
  by_cases hj : rightSingularValue A j = 0
  · simp [leftSingularVectorOfPositive, hj]
  · have hr : 0 < rightSingularValue A j := lt_of_le_of_ne (right_singular_value_bounds A j).1 (Ne.symm hj)
    simp [positive_left_singular_vectors_orthonormal A j k hr, hjk]

/-- The mixed pairing between distinct singular indices vanishes, including null directions. -/
private theorem left_right_image_dot_off (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖) (j k : Fin columns) (hjk : j ≠ k) :
    leftWalkImage A j ⬝ᵥ rightWalkImage A k = 0 := by
  rw [leftWalkImage, rightWalkImage, image_dot_product, P_transpose_mul_Q A hRows hA, Matrix.smul_mulVec]
  by_cases hk : rightSingularValue A k = 0
  · rw [mulVec_right_singular_vector_eq_zero A k hk, smul_zero, dotProduct_zero]
  · have hPos : 0 < rightSingularValue A k := lt_of_le_of_ne (right_singular_value_bounds A k).1 (Ne.symm hk)
    by_cases hj : rightSingularValue A j = 0
    · simp [leftSingularVectorOfPositive, hj]
    · have hLeft : 0 < rightSingularValue A j := lt_of_le_of_ne (right_singular_value_bounds A j).1 (Ne.symm hj)
      rw [(positive_singular_pair A k hPos).1, smul_smul, dotProduct_smul,
        positive_left_singular_vectors_orthonormal A j k hLeft]
      simp [hjk]

/-- Interior overlaps have the strict numerical bounds needed by the conjugate branches. -/
private theorem interior_overlap_bounds (A : Matrix (Fin rows) (Fin columns) ℝ) (hA : 0 < ‖A‖)
    (j : Fin columns) (hj : InteriorSingularValue A j) :
    0 ≤ singularOverlap A j ∧ singularOverlap A j < 1 ∧ singularOverlap A j ^ 2 < 1 := by
  have h0 : 0 ≤ singularOverlap A j := mul_nonneg (inv_nonneg.mpr hA.le) hj.1.le
  have h1 : singularOverlap A j < 1 := by
    calc
      singularOverlap A j < ‖A‖⁻¹ * ‖A‖ := mul_lt_mul_of_pos_left hj.2 (inv_pos.mpr hA)
      _ = 1 := inv_mul_cancel₀ hA.ne'
  exact ⟨h0, h1, by nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1.le)]⟩

/-- The singular vectors used in an interior plane have unit real squared norms. -/
private theorem singular_pair_norms (A : Matrix (Fin rows) (Fin columns) ℝ)
    (j : Fin columns) (h : 0 < rightSingularValue A j) :
    (∑ i, leftSingularVectorOfPositive A j i ^ 2) = 1 ∧
      (∑ i, rightSingularVector A j i ^ 2) = 1 := by
  constructor
  · simpa only [dotProduct, ← pow_two, ite_true] using positive_left_singular_vectors_orthonormal A j j h
  · simpa only [dotProduct, ← pow_two, ite_true] using right_singular_vectors_orthonormal A j j

/-- Each branch is an eigenvector of the actual walk, and decoding its phase returns the
associated singular value. -/
theorem walk_spectrum_eigenpair (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖) (p : WalkBranchIndex A) :
    (bireflectionWalk A).map Complex.ofReal *ᵥ walkSpectrumVector A p =
      Complex.exp (2 * Real.pi * Complex.I * walkSpectrumPhase A p) • walkSpectrumVector A p ∧
      ‖A‖ * foldedCosine (walkSpectrumPhase A p) = walkSpectrumValue A p := by
  let j := walkBranchDirection p
  let negative := walkBranchNegative p
  change (bireflectionWalk A).map Complex.ofReal *ᵥ singularDirectionBranch A j negative =
    Complex.exp (2 * Real.pi * Complex.I * singularDirectionPhase A j negative) • singularDirectionBranch A j negative ∧
    ‖A‖ * foldedCosine (singularDirectionPhase A j negative) = rightSingularValue A j
  by_cases hInside : InteriorSingularValue A j
  · obtain ⟨h0, h1, hSq⟩ := interior_overlap_bounds A hA j hInside
    obtain ⟨hLeft, hRight⟩ := positive_singular_pair A j hInside.1
    simp only [singularDirectionBranch, singularDirectionPhase, hInside, ite_true]
    constructor
    · have hBranch := walk_mulVec_phase_branch A hRows hA _ _ _ hLeft hRight negative hSq.le
      change (bireflectionWalk A).map Complex.ofReal *ᵥ
          fullPhaseBranch (singularOverlap A j) negative (leftWalkImage A j) (rightWalkImage A j) =
        phaseEigenvalue (singularOverlap A j) negative •
          fullPhaseBranch (singularOverlap A j) negative (leftWalkImage A j) (rightWalkImage A j) at hBranch
      rw [fullNormalizedBranch, Matrix.mulVec_smul, hBranch, branch_phase_eigenvalue _ h0 h1.le]
      exact smul_comm _ _ _
    · rw [folded_cosine_branch_phase _ h0 h1.le, singularOverlap, ← mul_assoc,
        mul_inv_cancel₀ hA.ne', one_mul]
  · simp only [singularDirectionBranch, singularDirectionPhase, hInside, ite_false]
    by_cases hZero : rightSingularValue A j = 0
    · obtain ⟨he, hv⟩ := right_null_image_phase A hRows hA _ (mulVec_right_singular_vector_eq_zero A j hZero)
      simp only [hZero, ite_true, hv, mul_zero, and_true]
      exact he
    · have hPos : 0 < rightSingularValue A j := lt_of_le_of_ne (right_singular_value_bounds A j).1 (Ne.symm hZero)
      have hTop : rightSingularValue A j = ‖A‖ :=
        le_antisymm (right_singular_value_bounds A j).2 (le_of_not_gt fun h => hInside ⟨hPos, h⟩)
      obtain ⟨hLeft, hRight⟩ := singular_pair_norms A j hPos
      have hUnit : ‖A‖⁻¹ * rightSingularValue A j = 1 := by rw [hTop, inv_mul_cancel₀ hA.ne']
      have hFixed := right_unit_image_fixed A hRows hA _ _ _ hLeft hRight (positive_singular_pair A j hPos).1 hUnit
      constructor
      · simpa [hZero, rightWalkImage] using hFixed
      · simp only [ite_eq_right hZero, foldedCosine, mul_zero, Real.cos_zero, abs_one, mul_one]
        exact hTop.symm

/-- Real coordinate inclusion commutes with the ordinary real dot product. -/
private theorem inner_of_real_vectors {I : Type} [Fintype I] (x y : I → ℝ) :
    Inner (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) = (x ⬝ᵥ y : ℝ) := by
  simp only [inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum, dotProduct]

/-- Two linear combinations are orthogonal if all four pairings vanish. -/
private theorem inner_two_smul_add_of_zero {I : Type} [Fintype I]
    (a b c d : QState I) (s t u v : ℂ)
    (hac : Inner a c = 0) (had : Inner a d = 0) (hbc : Inner b c = 0) (hbd : Inner b d = 0) :
    Inner (s • a + t • b) (u • c + v • d) = 0 := by
  simp only [Qatlib.Foundations.PureStateMath.Inner] at *
  simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, hac, had, hbc, hbd, smul_zero, add_zero]

/-- A branch belongs to the complex span of its two singular images. -/
private theorem singular_direction_branch_in_span (A : Matrix (Fin rows) (Fin columns) ℝ)
    (j : Fin columns) (negative : Bool) :
    ∃ s t : ℂ, singularDirectionBranch A j negative =
      s • (fun i => (leftWalkImage A j i : ℂ)) + t • (fun i => (rightWalkImage A j i : ℂ)) := by
  by_cases hInside : InteriorSingularValue A j
  · let ρ := singularOverlap A j
    let k : ℂ := if negative then Complex.I else -Complex.I
    let d : ℂ := ((Real.sqrt (2 * (1 - ρ ^ 2)) : ℝ) : ℂ)⁻¹
    refine ⟨d * k, d * ((Real.sqrt (1 - ρ ^ 2) : ℝ) - k * ρ), ?_⟩
    funext i
    simp only [singularDirectionBranch, hInside, ite_true, fullNormalizedBranch, fullPhaseBranch,
      k, d, ρ, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  · refine ⟨0, 1, ?_⟩
    simp [singularDirectionBranch, hInside]

/-- Distinct singular directions remain orthogonal after choosing either phase branch. -/
private theorem singular_direction_branches_off (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (j k : Fin columns) (hjk : j ≠ k) (negJ negK : Bool) :
    Inner (singularDirectionBranch A j negJ) (singularDirectionBranch A k negK) = 0 := by
  obtain ⟨s, t, hJ⟩ := singular_direction_branch_in_span A j negJ
  obtain ⟨u, v, hK⟩ := singular_direction_branch_in_span A k negK
  rw [hJ, hK]
  apply inner_two_smul_add_of_zero
  · rw [inner_of_real_vectors, left_image_dot_off A hRows j k hjk, Complex.ofReal_zero]
  · rw [inner_of_real_vectors, left_right_image_dot_off A hRows hA j k hjk, Complex.ofReal_zero]
  · rw [inner_of_real_vectors, dotProduct_comm, left_right_image_dot_off A hRows hA k j hjk.symm,
      Complex.ofReal_zero]
  · rw [inner_of_real_vectors, right_image_dot A hA j k, ite_eq_right hjk, Complex.ofReal_zero]

/-- A direction and its branch sign uniquely identify a spectrum index. -/
private theorem walk_branch_ext {A : Matrix (Fin rows) (Fin columns) ℝ} (p q : WalkBranchIndex A)
    (hd : walkBranchDirection p = walkBranchDirection q) (hn : walkBranchNegative p = walkBranchNegative q) :
    p = q := by
  cases p <;> cases q
  · exact congrArg Sum.inl hd
  · simp [walkBranchNegative] at hn
  · simp [walkBranchNegative] at hn
  · exact congrArg Sum.inr (Subtype.ext hd)

/-- An endpoint has only its primary branch. -/
private theorem walk_branch_negative_of_endpoint {A : Matrix (Fin rows) (Fin columns) ℝ} (p : WalkBranchIndex A)
    (h : ¬ InteriorSingularValue A (walkBranchDirection p)) : walkBranchNegative p = false := by
  cases p with
  | inl _ => rfl
  | inr j => exact (h j.property).elim

/-- The spectrum constructed from the full right singular basis is orthonormal. -/
theorem walk_spectrum_orthonormal (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖) (p q : WalkBranchIndex A) :
    Inner (walkSpectrumVector A p) (walkSpectrumVector A q) = if p = q then 1 else 0 := by
  by_cases hd : walkBranchDirection p = walkBranchDirection q
  · let j := walkBranchDirection p
    change Inner (singularDirectionBranch A j (walkBranchNegative p))
      (singularDirectionBranch A (walkBranchDirection q) (walkBranchNegative q)) = _
    rw [← hd]
    change Inner (singularDirectionBranch A j (walkBranchNegative p))
      (singularDirectionBranch A j (walkBranchNegative q)) = _
    by_cases hInside : InteriorSingularValue A j
    · obtain ⟨_, _, hSq⟩ := interior_overlap_bounds A hA j hInside
      obtain ⟨hLeft, hRight⟩ := singular_pair_norms A j hInside.1
      obtain ⟨ha, hb, hab⟩ := singular_images_geometry A hRows hA _ _ _ hLeft hRight
        (positive_singular_pair A j hInside.1).1
      have hGram := full_branches_orthonormal (singularOverlap A j) (leftWalkImage A j) (rightWalkImage A j)
        ha hb hab hSq (walkBranchNegative p) (walkBranchNegative q)
      have hSign : walkBranchNegative p = walkBranchNegative q ↔ p = q :=
        ⟨walk_branch_ext p q hd, fun h => congrArg walkBranchNegative h⟩
      simpa only [singularDirectionBranch, hInside, ite_true, hSign] using hGram
    · have hEnd : ¬ InteriorSingularValue A (walkBranchDirection q) := by rwa [← hd]
      have hpq : p = q := walk_branch_ext p q hd
        ((walk_branch_negative_of_endpoint p hInside).trans (walk_branch_negative_of_endpoint q hEnd).symm)
      simp only [singularDirectionBranch, hInside, ite_false]
      rw [inner_of_real_vectors, right_image_dot A hA j j]
      simp [hpq]
  · have hpq : p ≠ q := fun h => hd (congrArg walkBranchDirection h)
    rw [ite_eq_right hpq]
    exact singular_direction_branches_off A hRows hA _ _ hd _ _

/-- Each of two interior branches carries the reciprocal-square-root weight. -/
def singularBranchWeight (A : Matrix (Fin rows) (Fin columns) ℝ) (j : Fin columns) : ℂ :=
  if InteriorSingularValue A j then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 1

/-- Transport real right-basis coefficients to the walk branches. -/
def walkSpectrumCoefficient (A : Matrix (Fin rows) (Fin columns) ℝ) (d : Fin columns → ℝ)
    (p : WalkBranchIndex A) : ℂ :=
  (d (walkBranchDirection p) : ℂ) * singularBranchWeight A (walkBranchDirection p)

/-- The complete branch expansion agrees with the walk embedding of the associated real
right-basis sum. The same identity applies with some coefficients set to zero. -/
theorem walk_spectrum_expansion (A : Matrix (Fin rows) (Fin columns) ℝ) (hA : 0 < ‖A‖)
    (d : Fin columns → ℝ) :
    (∑ p : WalkBranchIndex A, walkSpectrumCoefficient A d p • walkSpectrumVector A p) =
      fun i => ((isometryQ A *ᵥ (∑ j, d j • rightSingularVector A j)) i : ℂ) := by
  let term (j : Fin columns) (negative : Bool) :=
    ((d j : ℂ) * singularBranchWeight A j) • singularDirectionBranch A j negative
  have hSub : (∑ j : {j : Fin columns // InteriorSingularValue A j}, term j.val true) =
      ∑ j, if InteriorSingularValue A j then term j true else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (InteriorSingularValue A))
      (fun j => by simp) (fun j => term j true)).symm
  rw [Fintype.sum_sum_type]
  change (∑ j, term j false) + (∑ j : {j : Fin columns // InteriorSingularValue A j}, term j.val true) = _
  rw [hSub, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j, (d j : ℂ) • (fun i => (rightWalkImage A j i : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : InteriorSingularValue A j
      · have hSum := right_image_eq_phase_sum (singularOverlap A j) (leftWalkImage A j)
          (rightWalkImage A j) (interior_overlap_bounds A hA j hj).2.2
        rw [Fintype.sum_bool] at hSum
        rw [hSum, ite_eq_left hj]
        simp only [term, singularBranchWeight, singularDirectionBranch, hj, ite_true, mul_smul, smul_add,
          add_comm]
      · simp [term, singularBranchWeight, singularDirectionBranch, hj]
    _ = _ := by
      funext i
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_sum, Complex.ofReal_mul, rightWalkImage]

/-- Applying the same decision to both branches of each direction corresponds to retaining
the matching real right-basis coefficients before the walk embedding. -/
theorem walk_spectrum_retained_expansion (A : Matrix (Fin rows) (Fin columns) ℝ) (hA : 0 < ‖A‖)
    (d : Fin columns → ℝ) (keep : Fin columns → Prop) :
    (∑ p : WalkBranchIndex A, (if keep (walkBranchDirection p) then walkSpectrumCoefficient A d p else 0) •
        walkSpectrumVector A p) =
      fun i => ((isometryQ A *ᵥ (∑ j, (if keep j then d j else 0) • rightSingularVector A j)) i : ℂ) := by
  have hCoefficient (p : WalkBranchIndex A) :
      (if keep (walkBranchDirection p) then walkSpectrumCoefficient A d p else 0) =
        walkSpectrumCoefficient A (fun j => if keep j then d j else 0) p := by
    by_cases hp : keep (walkBranchDirection p) <;> simp [walkSpectrumCoefficient, hp]
  simp_rw [hCoefficient]
  exact walk_spectrum_expansion A hA _

end Qatlib.Papers.QRecommender16.Recommendations
