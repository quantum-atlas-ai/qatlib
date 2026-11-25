/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation.BireflectionFactorization
public import Qatlib.Papers.QRecommender16.Recommendations.SingularPlane
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The reflection product on a right singular image

[KerenidisPrakash2017], Lemma 5.3, forms a walk from the row-state and
row-norm isometries. This file computes the image of a right singular vector
under that walk in the full product register. The calculation uses the
isometries and their compressed product from the published library.
It identifies the conjugate eigenvector formulas in the full register.
Normalizing the branches and reading out their phases are separate steps.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open scoped Matrix.Norms.Frobenius
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation

variable {rows columns : ℕ}

/-- An isometry's own reflection fixes every vector in its image. -/
private theorem reflection_fixes_isometry {Register Column : Type*}
    [Fintype Register] [DecidableEq Register] [Fintype Column] [DecidableEq Column]
    (basis : Matrix Register Column ℝ) (hBasis : basisᵀ * basis = 1) (vector : Column → ℝ) :
    (2 • (basis * basisᵀ) - 1) *ᵥ (basis *ᵥ vector) = basis *ᵥ vector := by
  have hProjection : (basis * basisᵀ) *ᵥ (basis *ᵥ vector) = basis *ᵥ vector := by
    rw [← Matrix.mulVec_mulVec (basis *ᵥ vector), Matrix.mulVec_mulVec vector basisᵀ basis,
      hBasis, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hProjection, Matrix.one_mulVec,
    two_smul, add_sub_cancel_right]

/-- The walk sends the right singular image to twice the scaled left image minus the right image. -/
theorem walk_mulVec_right_singular_image (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hPair : A *ᵥ right = singular • left) :
    bireflectionWalk A *ᵥ (isometryQ A *ᵥ right) =
      2 • (((‖A‖)⁻¹ * singular) • (isometryP A *ᵥ left)) - isometryQ A *ᵥ right := by
  have hCross :
      (isometryP A)ᵀ *ᵥ (isometryQ A *ᵥ right) = ((‖A‖)⁻¹ * singular) • left := by
    rw [Matrix.mulVec_mulVec, P_transpose_mul_Q A hRows hA,
      Matrix.smul_mulVec, hPair, smul_smul]
  have hProjection :
      (isometryP A * (isometryP A)ᵀ) *ᵥ (isometryQ A *ᵥ right) =
        ((‖A‖)⁻¹ * singular) • (isometryP A *ᵥ left) := by
    rw [← Matrix.mulVec_mulVec (isometryQ A *ᵥ right), hCross, Matrix.mulVec_smul]
  rw [bireflectionWalk, ← Matrix.mulVec_mulVec,
    reflection_fixes_isometry _ (isometryQ_orthonormal A hA),
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hProjection]

/-- The walk also preserves the span when applied to the left singular image. -/
theorem walk_mulVec_left_singular_image (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hPair : A *ᵥ right = singular • left) (hTransposePair : Aᵀ *ᵥ left = singular • right) :
    let overlap := (‖A‖)⁻¹ * singular
    bireflectionWalk A *ᵥ (isometryP A *ᵥ left) =
      (4 * overlap ^ 2 - 1) • (isometryP A *ᵥ left) -
        (2 * overlap) • (isometryQ A *ᵥ right) := by
  let overlap := (‖A‖)⁻¹ * singular
  let a := isometryP A *ᵥ left
  let b := isometryQ A *ᵥ right
  have hTranspose : (isometryQ A)ᵀ * isometryP A = (‖A‖)⁻¹ • Aᵀ := by
    simpa [Matrix.transpose_mul, Matrix.transpose_smul] using
      congrArg Matrix.transpose (P_transpose_mul_Q A hRows hA)
  have hCross : (isometryQ A)ᵀ *ᵥ a = overlap • right := by
    unfold a overlap
    rw [Matrix.mulVec_mulVec, hTranspose, Matrix.smul_mulVec, hTransposePair, smul_smul]
  have hProjection : (isometryQ A * (isometryQ A)ᵀ) *ᵥ a = overlap • b := by
    rw [← Matrix.mulVec_mulVec a, hCross, Matrix.mulVec_smul]
  have hRightReflection : (2 • (isometryQ A * (isometryQ A)ᵀ) - 1) *ᵥ a =
      2 • (overlap • b) - a := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hProjection, Matrix.one_mulVec]
  have hLeftReflection : (2 • (isometryP A * (isometryP A)ᵀ) - 1) *ᵥ b =
      2 • (overlap • a) - b := by
    have hWalk := walk_mulVec_right_singular_image A hRows hA left right singular hPair
    rw [bireflectionWalk, ← Matrix.mulVec_mulVec,
      reflection_fixes_isometry _ (isometryQ_orthonormal A hA)] at hWalk
    exact hWalk
  change bireflectionWalk A *ᵥ a = (4 * overlap ^ 2 - 1) • a - (2 * overlap) • b
  rw [bireflectionWalk, ← Matrix.mulVec_mulVec, hRightReflection,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
    reflection_fixes_isometry _ (isometryP_orthonormal A hRows), hLeftReflection]
  funext coordinate
  simp only [two_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Transport a real matrix–vector multiplication through the real-to-complex inclusion. -/
private theorem complex_mulVec {R C : Type*} [Fintype C]
    (A : Matrix R C ℝ) (v : C → ℝ) :
    A.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i
  exact (RingHom.map_mulVec Complex.ofRealHom A v i).symm

/-- The real orthogonal walk induces a unitary on the complex product register. -/
theorem complex_bireflection_walk_unitary (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖) :
    (bireflectionWalk A).map Complex.ofReal ∈ Matrix.unitaryGroup (Fin rows × Fin columns) ℂ := by
  let W := bireflectionWalk A
  have hAdj : (Wᵀ).map Complex.ofRealHom = (W.map Complex.ofReal)ᴴ := by
    funext i j
    simp [Matrix.conjTranspose_apply, RCLike.star_def]
  have hMul := congrArg (fun M : Matrix (Fin rows × Fin columns) (Fin rows × Fin columns) ℝ =>
    M.map Complex.ofRealHom) (bireflectionWalk_orthogonal A hRows hA)
  change (Wᵀ * W).map Complex.ofRealHom =
    (1 : Matrix (Fin rows × Fin columns) (Fin rows × Fin columns) ℝ).map Complex.ofRealHom at hMul
  rw [Matrix.map_mul, hAdj, Matrix.map_one _ (map_zero _) (map_one _)] at hMul
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact hMul

/-- The image of a right null vector has walk eigenvalue minus one. Its proof
requires no matching left null vector, including for wide rectangular matrices. -/
theorem walk_mulVec_right_null_image (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (right : Fin columns → ℝ) (hNull : A *ᵥ right = 0) :
    let ψ := fun i => ((isometryQ A *ᵥ right) i : ℂ)
    (bireflectionWalk A).map Complex.ofReal *ᵥ ψ = -ψ := by
  have hReal : bireflectionWalk A *ᵥ (isometryQ A *ᵥ right) = -(isometryQ A *ᵥ right) := by
    simpa using walk_mulVec_right_singular_image A hRows hA (0 : Fin rows → ℝ) right 0
      (by simpa using hNull)
  intro ψ
  change (bireflectionWalk A).map Complex.ofReal *ᵥ (fun i => ((isometryQ A *ᵥ right) i : ℂ)) = -ψ
  rw [complex_mulVec, hReal]
  funext i
  simp [ψ]

/-- A full-register branch in the singular space, scaled by the sine of the angle between the
two isometry images. This formula is useful before normalizing the eigenvector. -/
noncomputable def fullPhaseBranch (overlap : ℝ) (negative : Bool)
    (leftImage rightImage : Fin rows × Fin columns → ℝ) : Fin rows × Fin columns → ℂ :=
  fun i =>
    ((Real.sqrt (1 - overlap ^ 2) * rightImage i : ℝ) : ℂ) +
      (if negative then Complex.I else -Complex.I) *
        ((leftImage i - overlap * rightImage i : ℝ) : ℂ)

/-- The full reflection product sends either conjugate singular branch to its eigenvalue
multiple, with the same eigenvalues as the two-dimensional model. -/
theorem walk_mulVec_phase_branch (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ row, 0 < rowNormSq A row) (hA : 0 < ‖A‖)
    (left : Fin rows → ℝ) (right : Fin columns → ℝ) (singular : ℝ)
    (hPair : A *ᵥ right = singular • left) (hTransposePair : Aᵀ *ᵥ left = singular • right)
    (negative : Bool) (hOverlap : ((‖A‖)⁻¹ * singular) ^ 2 ≤ 1) :
    let overlap := (‖A‖)⁻¹ * singular
    let branch := fullPhaseBranch overlap negative (isometryP A *ᵥ left) (isometryQ A *ᵥ right)
    (bireflectionWalk A).map Complex.ofReal *ᵥ branch = phaseEigenvalue overlap negative • branch := by
  let ρ := (‖A‖)⁻¹ * singular
  let a := isometryP A *ᵥ left
  let b := isometryQ A *ᵥ right
  let e := a - ρ • b
  let s := Real.sqrt (1 - ρ ^ 2)
  let d := rotationDiagonal ρ
  let W := bireflectionWalk A
  have hB : W *ᵥ b = 2 • (ρ • a) - b :=
    walk_mulVec_right_singular_image A hRows hA left right singular hPair
  have hA' : W *ᵥ a = (4 * ρ ^ 2 - 1) • a - (2 * ρ) • b :=
    walk_mulVec_left_singular_image A hRows hA left right singular hPair hTransposePair
  have hB' : W *ᵥ b = d • b + (2 * ρ) • e := by
    rw [hB]
    funext i
    simp only [d, rotationDiagonal, e, two_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hE : W *ᵥ e = d • e - (2 * ρ * (1 - ρ ^ 2)) • b := by
    change W *ᵥ (a - ρ • b) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hA', hB]
    funext i
    simp only [d, rotationDiagonal, e, two_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let V := W.map Complex.ofReal
  let bC : Fin rows × Fin columns → ℂ := fun i => b i
  let eC : Fin rows × Fin columns → ℂ := fun i => e i
  have hs : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hOverlap)
  have hBC : V *ᵥ bC = (d : ℂ) • bC + (2 * (ρ : ℂ)) • eC := by
    change W.map Complex.ofReal *ᵥ (fun i => (b i : ℂ)) = _
    rw [complex_mulVec, hB']
    funext i
    simp only [bC, eC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hEC : V *ᵥ eC = (d : ℂ) • eC - (2 * (ρ : ℂ) * (s : ℂ) ^ 2) • bC := by
    change W.map Complex.ofReal *ᵥ (fun i => (e i : ℂ)) = _
    rw [complex_mulVec, hE, ← hs]
    funext i
    simp only [bC, eC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  let k : ℂ := if negative then Complex.I else -Complex.I
  have hBranch : fullPhaseBranch ρ negative a b = (s : ℂ) • bC + k • eC := by
    funext i
    simp only [fullPhaseBranch, s, eC, bC, k, e, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Complex.ofReal_mul]
  change V *ᵥ fullPhaseBranch ρ negative a b =
    phaseEigenvalue ρ negative • fullPhaseBranch ρ negative a b
  rw [hBranch, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hBC, hEC]
  funext i
  cases negative <;>
    simp only [phaseEigenvalue, rotationOffDiagonal, ← show d = rotationDiagonal ρ from rfl,
      ← show s = Real.sqrt (1 - ρ ^ 2) from rfl, Complex.ofReal_mul, Complex.ofReal_ofNat, k,
      Bool.false_eq_true, ite_false, ite_true, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;>
    linear_combination (2 * (ρ : ℂ) * (s : ℂ) * eC i) * Complex.I_sq

end Qatlib.Papers.QRecommender16.Recommendations
