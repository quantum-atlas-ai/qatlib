/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.ContourAdapters
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel
import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseLine
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable

open Qatlib.Concepts.BlockEncoding.LCU

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

/-!
# The common reciprocal word for actual numerical-range resolvents

Numerical-range separation supplies the singular gap and identifies the
pseudoinverse target of the normalized joint shift.  The reciprocal source
word is then rescaled with its actual adjoint and exchanged clean frames.
The access input is the normalized joint shifted encoding; its construction
from the original matrix oracle remains a separate consumer.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {I L : Type} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

/-- The normalized shift inherits the actual Rayleigh separation on every
Euclidean input vector. -/
theorem normalized_matrixShift_lower_bound (A : Matrix I I ℂ) (z : ℂ) (B₀ r : ℝ)
    (hB : 0 < B₀) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖)
    (x : EuclideanSpace ℂ I) :
    (r / B₀) * ‖x‖ ≤ ‖(((B₀⁻¹ : ℝ) : ℂ) • matrixShift A z).toEuclideanLin x‖ := by
  let e := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
  have he : e (matrixShift A z) = shiftedOperator (e A) z := by
    simp [matrixShift, shiftedOperator, map_sub, map_smul, map_one]
    rfl
  have hb := shiftedOperator_lower_bound (e A) z r hsep x
  rw [← he] at hb
  change r * ‖x‖ ≤ ‖(matrixShift A z).toEuclideanLin x‖ at hb
  calc
    (r / B₀) * ‖x‖ = B₀⁻¹ * (r * ‖x‖) := by ring
    _ ≤ B₀⁻¹ * ‖(matrixShift A z).toEuclideanLin x‖ :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hB.le)
    _ = ‖(((B₀⁻¹ : ℝ) : ℂ) • matrixShift A z).toEuclideanLin x‖ := by
      simp only [map_smul, LinearMap.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]

/-- Construction for joint Label Fibre in the joint resolvent word model. -/
private def jointLabelFibre (x : EuclideanSpace ℂ (L × I)) (j : L) :
    EuclideanSpace ℂ I := WithLp.toLp 2 (fun i => x (j, i))

/-- The finite construction in `JointResolventWord` satisfies `jointLabelFibre_select_apply` under the displayed hypotheses. -/
private theorem jointLabelFibre_select_apply (V : L → Matrix I I ℂ)
    (x : EuclideanSpace ℂ (L × I)) (j : L) :
    jointLabelFibre ((select V).toEuclideanLin x) j =
      (V j).toEuclideanLin (jointLabelFibre x j) := by
  ext i
  change (select V *ᵥ (fun p => x p)) (j, i) =
    (V j *ᵥ (fun k => x (j, k))) i
  simp [select, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul]

omit [DecidableEq I] [DecidableEq L] in
/-- The finite construction in `JointResolventWord` satisfies `joint_norm_sq` under the displayed hypotheses. -/
private theorem joint_norm_sq (x : EuclideanSpace ℂ (L × I)) :
    ‖x‖ ^ 2 = ∑ j, ‖jointLabelFibre x j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- The common normalized joint shift has a dimension-free lower bound.
The fibre proof includes every label and the entire input space. -/
theorem jointNormalizedShift_lower_bound (A : Matrix I I ℂ) (z : L → ℂ) (B₀ r : ℝ)
    (hB : 0 < B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖)
    (x : EuclideanSpace ℂ (L × I)) :
    (r / B₀) * ‖x‖ ≤ ‖(jointNormalizedShift A z B₀).toEuclideanLin x‖ := by
  have hratio : 0 ≤ r / B₀ := (div_pos hr hB).le
  have hs : (r / B₀) ^ 2 * ‖x‖ ^ 2 ≤
      ‖(jointNormalizedShift A z B₀).toEuclideanLin x‖ ^ 2 := by
    rw [joint_norm_sq x, joint_norm_sq ((jointNormalizedShift A z B₀).toEuclideanLin x),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hf : jointLabelFibre ((jointNormalizedShift A z B₀).toEuclideanLin x) j =
        (((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)).toEuclideanLin (jointLabelFibre x j) :=
      by simpa only [normalized_shift_as_select] using
        (jointLabelFibre_select_apply
          (fun j => ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)) x j)
    rw [hf, ← mul_pow]
    exact (sq_le_sq₀ (mul_nonneg hratio (norm_nonneg _)) (norm_nonneg _)).mpr
      (normalized_matrixShift_lower_bound A (z j) B₀ r hB (hsep j) (jointLabelFibre x j))
  apply (sq_le_sq₀ (mul_nonneg hratio (norm_nonneg _)) (norm_nonneg _)).mp
  simpa only [mul_pow] using hs

/-- Separation bounds every in-range singular value, so no zero mode is
silently removed from the joint inverse problem. -/
theorem jointNormalizedShift_singularValues_lower (A : Matrix I I ℂ) (z : L → ℂ)
    (B₀ r : ℝ) (hB : 0 < B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖)
    (i : Fin (Fintype.card (L × I))) :
    r / B₀ ≤ matrixSingularValues (jointNormalizedShift A z B₀) i := by
  have hb := jointNormalizedShift_lower_bound A z B₀ r hB hr hsep
    (rightSingularBasis (jointNormalizedShift A z B₀) i)
  simpa only [norm_rightSingularBasis, norm_apply_rightSingularBasis, mul_one] using hb

omit [Fintype I] [DecidableEq I] [Fintype L] in
/-- The finite construction in `JointResolventWord` satisfies `select_smul` under the displayed hypotheses. -/
private theorem select_smul (V : L → Matrix I I ℂ) (c : ℂ) :
    select (fun j => c • V j) = c • select V := by
  ext p q
  simp [select, Matrix.smul_apply, smul_eq_mul, mul_ite]

/-- The canonical matrix resolvent, without a supplied inverse witness. -/
theorem joint_matrixResolvent_inverse (A : Matrix I I ℂ) (z : ℂ) (r : ℝ)
    (hr : 0 < r) (hsep : ∀ w ∈ matrixNumericalRange A, r ≤ ‖z - w‖) :
    matrixShift A z * matrixResolvent A z = 1 ∧
      matrixResolvent A z * matrixShift A z = 1 := by
  obtain ⟨R, hSR, hRS, _, hp⟩ :=
    exists_matrix_resolvent_of_numericalRange_separation A z r hr hsep
  have he : matrixResolvent A z = R := by
    simpa only [matrixResolvent, matrixShift] using hp
  rw [he]
  exact ⟨hSR, hRS⟩

/-- The actual joint pseudoinverse is the common scale times the canonical
resolvents; both inverse equations are generated by separation. -/
theorem jointNormalizedShift_pseudoinverse (A : Matrix I I ℂ) (z : L → ℂ)
    (B₀ r : ℝ) (hB : 0 < B₀) (hr : 0 < r)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖) :
    matrixPseudoinverse (jointNormalizedShift A z B₀) =
      (B₀ : ℂ) • jointMatrixResolvent A z := by
  have hscale : ((B₀⁻¹ : ℝ) : ℂ) * (B₀ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hB.ne', Complex.ofReal_one]
  have hf (j : L) :
      (((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)) *
        ((B₀ : ℂ) • matrixResolvent A (z j)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A (z j) r hr (hsep j)).1, hscale, one_smul]
  have hb (j : L) :
      ((B₀ : ℂ) • matrixResolvent A (z j)) *
        (((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      (joint_matrixResolvent_inverse A (z j) r hr (hsep j)).2,
      mul_comm (B₀ : ℂ), hscale, one_smul]
  have hforward : jointNormalizedShift A z B₀ *
      ((B₀ : ℂ) • jointMatrixResolvent A z) = 1 := by
    rw [normalized_shift_as_select, matrix_resolvent_as_select,
      ← select_smul (fun j => matrixResolvent A (z j)) (B₀ : ℂ),
      parallel_select_mul (fun j => ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j))
        (fun j => (B₀ : ℂ) • matrixResolvent A (z j))]
    have he : (fun j => (((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j)) *
        ((B₀ : ℂ) • matrixResolvent A (z j))) = fun _ : L => (1 : Matrix I I ℂ) :=
      funext hf
    rw [he, parallel_select_one]
  have hbackward : ((B₀ : ℂ) • jointMatrixResolvent A z) *
      jointNormalizedShift A z B₀ = 1 := by
    rw [normalized_shift_as_select, matrix_resolvent_as_select,
      ← select_smul (fun j => matrixResolvent A (z j)) (B₀ : ℂ),
      parallel_select_mul (fun j => (B₀ : ℂ) • matrixResolvent A (z j))
        (fun j => ((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j))]
    have he : (fun j => ((B₀ : ℂ) • matrixResolvent A (z j)) *
        (((B₀⁻¹ : ℝ) : ℂ) • matrixShift A (z j))) = fun _ : L => (1 : Matrix I I ℂ) :=
      funext hb
    rw [he, parallel_select_one]
  exact matrixPseudoinverse_eq_of_twoSidedInverse (jointNormalizedShift A z B₀)
    ((B₀ : ℂ) • jointMatrixResolvent A z) hforward hbackward

/-- G20: the actual common reciprocal source word, its true adjoint and
exchanged clean frames, the derived inverse target, and its complete ledger. -/
theorem joint_resolvent_word
    (H I L : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype L] [DecidableEq L] (A : Matrix I I ℂ) (z : L → ℂ) (B₀ r ε : ℝ)
    (U : Matrix H H ℂ) (F G : Matrix H (L × I) ℂ)
    (hB : 0 < B₀) (hr : 0 < r) (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hsep : ∀ j, ∀ w ∈ matrixNumericalRange A, r ≤ ‖z j - w‖)
    (henc : ProjectedUnitaryEncoding (jointNormalizedShift A z B₀) U F G) :
    let κ := jointResolventCondition B₀ r
    let J := Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε
    ∃ Φ : List ℝ, Φ.length = 2 * J + 1 ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) = (2 * J + 1, 2 * J, 2 * J + 2, 2 * J + 1) ∧
      BlockEncoding (jointMatrixResolvent A z)
        (sourceRealWord U (rangeProjector G) (rangeProjector F) Φ)ᴴ
        (sourceAverageClean G) (sourceAverageClean F) (4 * (J : ℝ) / B₀) (2 * ε / B₀) ∧
      (Φ.length : ℝ) ≤ 32 * κ * Real.log (κ / ε) := by
  let κ := jointResolventCondition B₀ r
  let J := Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ κ ε
  let c : ℝ := (4 * (J : ℝ))⁻¹
  let α : ℝ := 4 * (J : ℝ) / B₀
  have hκ2 : 2 ≤ κ := le_max_left _ _
  have hκ : 1 < κ := by linarith
  have hκpos : 0 < κ := by linarith
  have hratio : B₀ / r ≤ κ := le_max_right _ _
  have hκinv : κ⁻¹ ≤ r / B₀ := by
    have hh := (inv_le_inv₀ hκpos (div_pos hB hr)).mpr hratio
    simpa only [inv_div] using hh
  have hgap : ∀ i : Fin (Fintype.card (L × I)),
      0 < matrixSingularValues (jointNormalizedShift A z B₀) i →
        κ⁻¹ ≤ matrixSingularValues (jointNormalizedShift A z B₀) i := by
    intro i _
    exact hκinv.trans (jointNormalizedShift_singularValues_lower A z B₀ r hB hr hsep i)
  have hcut := Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocal_cutoff_bounds κ ε hκ hε hε1.le
  have hJ : 2 ≤ J := hcut.2.1
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hc : 0 < c := by dsimp [c]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨Φ, hlen, _, hcounts, hbe⟩ := Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocal_inverse_word
    H (L × I) (L × I) (jointNormalizedShift A z B₀) U F G κ ε hκ hε hε1 henc hgap
  have hp := jointNormalizedShift_pseudoinverse A z B₀ r hB hr hsep
  rw [hp] at hbe
  have hscale : α * c * B₀ = 1 := by
    dsimp [α, c]
    field_simp [hB.ne', hJpos.ne']
  let W := (sourceRealWord U (rangeProjector G) (rangeProjector F) Φ)ᴴ
  let C := compress (sourceAverageClean G) W (sourceAverageClean F)
  let E := (c : ℂ) • ((B₀ : ℂ) • jointMatrixResolvent A z) - C
  have herr : ‖E‖ ≤ 2 * c * ε := by
    simpa only [one_smul] using hbe.error_le
  have he : jointMatrixResolvent A z - α • C = α • E := by
    have hs : (α : ℂ) * (c : ℂ) * (B₀ : ℂ) = 1 := by exact_mod_cast hscale
    ext i j
    simp only [E, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    calc
      jointMatrixResolvent A z i j - (α : ℂ) * C i j =
          ((α : ℂ) * (c : ℂ) * (B₀ : ℂ)) * jointMatrixResolvent A z i j -
            (α : ℂ) * C i j := by rw [hs]; ring
      _ = (α : ℂ) * ((c : ℂ) * ((B₀ : ℂ) * jointMatrixResolvent A z i j) - C i j) := by
        ring
  have hrescaled : BlockEncoding (jointMatrixResolvent A z) W
      (sourceAverageClean G) (sourceAverageClean F) α (2 * ε / B₀) := by
    refine ⟨hbe.unitary, hbe.left_isometry, hbe.right_isometry, hα, by positivity, ?_⟩
    change ‖jointMatrixResolvent A z - α • C‖ ≤ 2 * ε / B₀
    rw [he, norm_smul, Real.norm_of_nonneg hα.le]
    calc
      α * ‖E‖ ≤ α * (2 * c * ε) := mul_le_mul_of_nonneg_left herr hα.le
      _ = 2 * ε / B₀ := by
        dsimp [α, c]
        field_simp [hB.ne', hJpos.ne']
  refine ⟨Φ, hlen, hcounts, hrescaled, ?_⟩
  rw [hlen]
  simpa only [κ, Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalJ, Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalReciprocalB, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hcut.2.2

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords
