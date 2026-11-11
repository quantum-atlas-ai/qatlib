/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.SquareRootQSVTRobustness
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.QSP

/-!
# Interior robustness of complex QSVT

This module constructs pairs of projected unitary encodings with common frames from midpoint and
difference data. Common row completions and paired frame rotations control the oracle distance
inside the contraction region, supporting the interior robustness analysis of
[GilyenSuLowWiebe2019].

The resulting `interiorRate` bounds parity-dependent complex singular responses. The module also
identifies actual odd-word corners and their query counts.

## Main statements

* `interior_common_projected_pair`: Construct common-frame encodings with a midpoint-dependent
  distance bound.
* `interior_complex_singular_response_stability`: Bound singular-response differences by
  `interiorRate`.
* `interior_complex_actual_word_corner_and_ledger`: Give the actual odd-word error and exact
  query count.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable local instance interiorMatrixCStar {J : Type} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

/-- The scalar primary response of a complex phase list evaluated on real inputs. -/
noncomputable def interiorResponse (base : ℂ) (zs : List ℂ) : ℝ → ℂ :=
  fun x => (responseP base zs).eval (x : ℂ)

/-- The interior perturbation rate `d * √(2 / (1 - ‖(A + B) / 2‖²)) * ‖A - B‖`. -/
noncomputable def interiorRate {I O : Type} [Fintype I] [Fintype O]
    (A B : Matrix O I ℂ) (d : ℕ) : ℝ :=
  d * Real.sqrt (2 / (1 - ‖(2 : ℂ)⁻¹ • (A+B)‖^2)) * ‖A-B‖

/-- The interior perturbation rate is nonnegative. -/
theorem interiorRate_nonneg {I O : Type} [Fintype I] [Fintype O]
    (A B : Matrix O I ℂ) (d : ℕ) : 0 ≤ interiorRate A B d := by
  unfold interiorRate
  positivity

/-- The interior gap condition bounds the weighted common-row budget by one. -/
theorem interior_common_row_budget (m δ : ℝ) (hm : 0 ≤ m) (hmi : m < 1)
    (hδ : 0 ≤ δ) (hgap : δ + m ^ 2 ≤ 1) :
    (2 / (1 + m ^ 2)) * m ^ 2 + (2 / (1 - m ^ 2)) * (δ / 2) ^ 2 ≤ 1 := by
  have hq : 0 < 1 - m ^ 2 := by nlinarith
  have hr : 0 < 1 + m ^ 2 := by positivity
  have hd : δ ≤ 1 - m ^ 2 := by linarith
  have hdsq : δ ^ 2 ≤ (1 - m ^ 2) ^ 2 := (sq_le_sq₀ hδ hq.le).mpr hd
  have hterm : (2 / (1 - m ^ 2)) * (δ / 2) ^ 2 ≤ (1 - m ^ 2) / 2 := by
    have he : (2 / (1 - m ^ 2)) * (δ / 2) ^ 2 = δ ^ 2 / (2 * (1 - m ^ 2)) := by
      field_simp
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  apply (add_le_add_right hterm _).trans
  rw [div_mul_eq_mul_div, div_add_div _ _ hr.ne' (by norm_num)]
  apply (div_le_iff₀ (by positivity : 0 < (1 + m ^ 2) * 2)).mpr
  nlinarith [sq_nonneg (1 - m ^ 2)]

/-- Compute the row Gram matrix of the concatenated blocks `M + D` and `t⁻¹ • M - t • D` for
nonzero `t`. -/
theorem interior_common_row_gram {I O : Type} [Fintype I] [Fintype O]
    (M D : Matrix O I ℂ) (t : ℝ) (ht : t ≠ 0) :
    let T := Matrix.fromCols (M + D) (t⁻¹ • M - t • D)
    T * Tᴴ = (1 + t⁻¹ ^ 2) • (M * Mᴴ) + (1 + t ^ 2) • (D * Dᴴ) := by
  (try dsimp only)
  simp only [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    star_trivial, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul]
  match_scalars <;> field_simp <;> ring

/-- The plus and minus common-row constructions have the same row Gram matrix for nonzero `t`. -/
theorem interior_common_partner_gram {I O : Type} [Fintype I] [Fintype O]
    (M D : Matrix O I ℂ) (t : ℝ) (ht : t ≠ 0) :
    let T₀ := Matrix.fromCols (M + D) (t⁻¹ • M - t • D)
    let T₁ := Matrix.fromCols (M - D) (t⁻¹ • M + t • D)
    T₀ * T₀ᴴ = T₁ * T₁ᴴ := by
  (try dsimp only)
  have h := interior_common_row_gram M (-D) t ht
  simp only [← sub_eq_add_neg, smul_neg, sub_neg_eq_add, Matrix.conjTranspose_neg,
    Matrix.neg_mul, Matrix.mul_neg, neg_neg] at h
  rw [interior_common_row_gram M D t ht, h]

/-- The two completed common rows differ in norm by exactly `2 * √(1 + t²) * ‖D‖`. -/
theorem interior_common_row_distance {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M D : Matrix O I ℂ) (C : Matrix O O ℂ) (t : ℝ) :
    let T₀ := Matrix.fromCols (M + D) (Matrix.fromCols (t⁻¹ • M - t • D) C)
    let T₁ := Matrix.fromCols (M - D) (Matrix.fromCols (t⁻¹ • M + t • D) C)
    ‖T₀ - T₁‖ = 2 * Real.sqrt (1 + t ^ 2) * ‖D‖ := by
  (try dsimp only)
  let N := Matrix.fromCols (M + D) (Matrix.fromCols (t⁻¹ • M - t • D) C) -
    Matrix.fromCols (M - D) (Matrix.fromCols (t⁻¹ • M + t • D) C)
  have hn : N = Matrix.fromCols ((2 : ℝ) • D)
      (Matrix.fromCols ((-2 * t) • D) (0 : Matrix O O ℂ)) := by
    ext i j
    cases j with
    | inl j => simp only [N, Matrix.sub_apply, Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.sub_apply,
          Matrix.smul_apply]; module
    | inr j =>
      cases j with
      | inl j => simp only [N, Matrix.sub_apply, Matrix.fromCols_apply_inr,
          Matrix.fromCols_apply_inl, Matrix.add_apply, Matrix.sub_apply,
          Matrix.smul_apply]; module
      | inr j => simp [N]
  have hgram : N * Nᴴ = (4 * (1 + t ^ 2)) • (D * Dᴴ) := by
    rw [hn]
    simp only [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_zero,
      Matrix.zero_mul, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  have hnorm (X : Matrix O (I ⊕ (I ⊕ O)) ℂ) : ‖X * Xᴴ‖ = ‖X‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      pow_two] using! Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
  have hD : ‖D * Dᴴ‖ = ‖D‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      pow_two] using! Matrix.l2_opNorm_conjTranspose_mul_self Dᴴ
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
  have hsq : ‖N‖ ^ 2 = (4 * (1 + t ^ 2)) * ‖D‖ ^ 2 := by
    rw [← hnorm, hgram, norm_smul, Real.norm_of_nonneg (by positivity), hD]
  change ‖N‖ = _
  apply (sq_eq_sq₀ (norm_nonneg N) (by positivity)).mp
  rw [hsq, mul_pow, mul_pow, hs]
  ring

/-- A weighted norm budget permits a common positive semidefinite block completing both rows to
coisometries. -/
theorem interior_common_row_completion {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M D : Matrix O I ℂ) (t : ℝ) (ht : t ≠ 0)
    (hbudget : (1 + t⁻¹ ^ 2) * ‖M‖ ^ 2 + (1 + t ^ 2) * ‖D‖ ^ 2 ≤ 1) :
    ∃ C : Matrix O O ℂ, C.PosSemidef ∧
      IsIsometry (Matrix.fromCols (M + D) (Matrix.fromCols (t⁻¹ • M - t • D) C))ᴴ ∧
      IsIsometry (Matrix.fromCols (M - D) (Matrix.fromCols (t⁻¹ • M + t • D) C))ᴴ := by
  let T := Matrix.fromCols (M + D) (t⁻¹ • M - t • D)
  have hgram : T * Tᴴ = (1 + t⁻¹ ^ 2) • (M * Mᴴ) + (1 + t ^ 2) • (D * Dᴴ) :=
    interior_common_row_gram M D t ht
  have hnorm (X : Matrix O I ℂ) : ‖X * Xᴴ‖ = ‖X‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      pow_two] using! Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
  have hn : ‖T * Tᴴ‖ ≤ 1 := by
    rw [hgram]
    calc
      _ ≤ ‖(1 + t⁻¹ ^ 2) • (M * Mᴴ)‖ + ‖(1 + t ^ 2) • (D * Dᴴ)‖ := norm_add_le _ _
      _ = (1 + t⁻¹ ^ 2) * ‖M‖ ^ 2 + (1 + t ^ 2) * ‖D‖ ^ 2 := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by positivity), hnorm, hnorm]
      _ ≤ 1 := hbudget
  have hbound : T * Tᴴ ≤ 1 := by
    have h := (Matrix.isHermitian_mul_conjTranspose_self T).isSelfAdjoint.le_algebraMap_norm_self
    apply h.trans
    rw [← map_one (algebraMap ℝ (Matrix O O ℂ)), ← sub_nonneg, ← map_sub,
      Algebra.algebraMap_eq_smul_one]
    exact ((Matrix.PosSemidef.one : (1 : Matrix O O ℂ).PosSemidef).smul
      (by linarith : 0 ≤ 1 - ‖T * Tᴴ‖)).nonneg
  let C := CFC.sqrt (1 - T * Tᴴ)
  have hC : C.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hCsq : C * Cᴴ = 1 - T * Tᴴ := by
    rw [hC.isHermitian]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hbound)
  refine ⟨C, hC, ?_, ?_⟩
  · unfold IsIsometry
    rw [Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
    have he : (M + D) * (M + D)ᴴ +
        (t⁻¹ • M - t • D) * (t⁻¹ • M - t • D)ᴴ = T * Tᴴ := by
      simp [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromCols_mul_fromRows]
    rw [hCsq, ← add_assoc, he]
    exact add_sub_cancel _ _
  · unfold IsIsometry
    rw [Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
    have he : (M - D) * (M - D)ᴴ +
        (t⁻¹ • M + t • D) * (t⁻¹ • M + t • D)ᴴ = T * Tᴴ := by
      have h := interior_common_partner_gram M D t ht
      simpa only [T, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromCols_mul_fromRows] using! h.symm
    rw [hCsq, ← add_assoc, he]
    exact add_sub_cancel _ _

/-- For a skew-Hermitian contraction `K`, the matrices `√(1 + K * K) ± K` are unitary and differ
in norm by `2 * ‖K‖`. -/
theorem interior_skew_rotations {H : Type} [Fintype H] [DecidableEq H]
    (K : Matrix H H ℂ) (hK : Kᴴ = -K) (hn : ‖K‖ ≤ 1) :
    let S := CFC.sqrt (1 + K * K)
    S + K ∈ Matrix.unitaryGroup H ℂ ∧ S - K ∈ Matrix.unitaryGroup H ℂ ∧
      ‖(S + K) - (S - K)‖ = 2 * ‖K‖ := by
  (try dsimp only)
  have hp : 0 ≤ Kᴴ * K := (Matrix.posSemidef_conjTranspose_mul_self K).nonneg
  have hbound : Kᴴ * K ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hp).mp (by
      rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      nlinarith [norm_nonneg K])
  have he : 1 + K * K = 1 - Kᴴ * K := by rw [hK, Matrix.neg_mul]; abel
  have hpos : 0 ≤ 1 + K * K := he ▸ sub_nonneg.mpr hbound
  let S := CFC.sqrt (1 + K * K)
  have hS : Sᴴ = S := (CFC.sqrt_nonneg _).isSelfAdjoint.isHermitian
  have hsq : S * S = 1 + K * K := CFC.sqrt_mul_sqrt_self _ hpos
  have hc : Commute (1 + K * K) K := by change (1 + K * K) * K = K * (1 + K * K); noncomm_ring
  have hcomm : S * K = K * S := (hc.cfcₙ_nnreal NNReal.sqrt).eq
  have hu : S + K ∈ Matrix.unitaryGroup H ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    rw [Matrix.conjTranspose_add, hS, hK]
    calc
      _ = S * S - K * K := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul]
        rw [hcomm]
        abel
      _ = 1 := by rw [hsq]; abel
  refine ⟨hu, ?_, ?_⟩
  · simpa only [Matrix.conjTranspose_add, hS, hK, ← sub_eq_add_neg] using! adjoint_unitary hu
  · have hd : (S + K) - (S - K) = (2 : ℝ) • K := by module
    rw [hd, norm_smul, Real.norm_of_nonneg (by norm_num)]

/-- If an isometric frame is orthogonal to `Y`, the associated skew-Hermitian matrix has norm at
most `‖Y‖`. -/
private theorem interior_frame_skew_norm {H J : Type} [Fintype H] [Fintype J]
    [DecidableEq H] [DecidableEq J] (F Y : Matrix H J ℂ) (hF : IsIsometry F)
    (hFY : Fᴴ * Y = 0) : ‖Y * Fᴴ - F * Yᴴ‖ ≤ ‖Y‖ := by
  have hFF : Fᴴ * F = 1 := hF
  have hYF : Yᴴ * F = 0 := by
    have h := congrArg Matrix.conjTranspose hFY
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using! h
  let P := F * Fᴴ
  let J₀ := (1 : Matrix H H ℂ) - P
  have hPP : P * P = P := by
    simp only [P, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F, hFF, Matrix.one_mul]
  have hPh : Pᴴ = P := by simp [P]
  have hJh : J₀ᴴ = J₀ := by simp [J₀, hPh]
  have hJJ : J₀ * J₀ = J₀ := by
    dsimp only [J₀]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hJY : J₀ * Y = Y := by simp [J₀, P, Matrix.sub_mul, Matrix.mul_assoc, hFY]
  have hYJ : Yᴴ * J₀ = Yᴴ := by
    have h := congrArg Matrix.conjTranspose hJY
    simpa only [Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose] using! h
  have hnorm (X : Matrix H J ℂ) : ‖X * Xᴴ‖ = ‖X‖ ^ 2 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      pow_two] using! Matrix.l2_opNorm_conjTranspose_mul_self Xᴴ
  have hy : Y * Yᴴ ≤ ‖Y‖ ^ 2 • (1 : Matrix H H ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _)
      (Matrix.posSemidef_self_mul_conjTranspose Y).nonneg).mp (hnorm Y).le
  have hgy : Yᴴ * Y ≤ ‖Y‖ ^ 2 • (1 : Matrix J J ℂ) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _)
      (Matrix.posSemidef_conjTranspose_mul_self Y).nonneg).mp (by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self, pow_two])
  have hproj : F * (Yᴴ * Y) * Fᴴ ≤ ‖Y‖ ^ 2 • P := by
    apply sub_nonneg.mp
    have h := (sub_nonneg.mpr hgy).posSemidef.mul_mul_conjTranspose_same F
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, P] using! h.nonneg
  have hperp : Y * Yᴴ ≤ ‖Y‖ ^ 2 • J₀ := by
    apply sub_nonneg.mp
    have h := (sub_nonneg.mpr hy).posSemidef.mul_mul_conjTranspose_same J₀
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hJh, hJJ, Matrix.mul_assoc, hYJ,
      ← Matrix.mul_assoc J₀ Y, hJY] using! h.nonneg
  let K := Y * Fᴴ - F * Yᴴ
  have hgram : Kᴴ * K = F * (Yᴴ * Y) * Fᴴ + Y * Yᴴ := by
    simp only [K, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ Y, ← Matrix.mul_assoc Yᴴ F,
      ← Matrix.mul_assoc Fᴴ F, hFY, hYF, hFF, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.one_mul, sub_zero, zero_sub, sub_neg_eq_add]
  have hbound : Kᴴ * K ≤ ‖Y‖ ^ 2 • (1 : Matrix H H ℂ) := by
    rw [hgram]
    have h := add_le_add hproj hperp
    simpa only [← smul_add, J₀, add_sub_cancel] using! h
  have hn := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ‖Y‖)
    (Matrix.posSemidef_conjTranspose_mul_self K).nonneg).mpr
      (by simpa only [Algebra.algebraMap_eq_smul_one] using! hbound)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two] at hn
  exact (sq_le_sq₀ (norm_nonneg K) (norm_nonneg Y)).mp hn

/-- A positive matrix commuting with a frame's range projector intertwines its square root
through that frame. -/
private theorem interior_sqrt_frame {H J : Type} [Fintype H] [Fintype J]
    [DecidableEq H] [DecidableEq J] (F : Matrix H J ℂ) (hF : IsIsometry F)
    (Q : Matrix H H ℂ) (hQ : 0 ≤ Q) (hc : Commute Q (F * Fᴴ)) :
    CFC.sqrt Q * F = F * CFC.sqrt (Fᴴ * Q * F) := by
  let S := CFC.sqrt Q
  have hFF : Fᴴ * F = 1 := hF
  have hS : S.PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hSP : S * (F * Fᴴ) = (F * Fᴴ) * S := (hc.cfcₙ_nnreal NNReal.sqrt).eq
  have hsq : S * S = Q := CFC.sqrt_mul_sqrt_self Q hQ
  have hZ : (Fᴴ * S * F).PosSemidef := hS.conjTranspose_mul_mul_same F
  have hZsq : (Fᴴ * S * F) * (Fᴴ * S * F) = Fᴴ * Q * F := by
    calc
      _ = Fᴴ * (S * (F * Fᴴ)) * S * F := by simp only [Matrix.mul_assoc]
      _ = Fᴴ * ((F * Fᴴ) * S) * S * F := by rw [hSP]
      _ = Fᴴ * Q * F := by simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ F,
        hFF, Matrix.one_mul, hsq]
  have hroot : CFC.sqrt (Fᴴ * Q * F) = Fᴴ * S * F := CFC.sqrt_unique hZsq hZ.nonneg
  rw [hroot]
  calc
    S * F = S * (F * Fᴴ) * F := by simp only [Matrix.mul_assoc, hFF, Matrix.mul_one]
    _ = (F * Fᴴ) * S * F := by rw [hSP]
    _ = F * (Fᴴ * S * F) := by simp only [Matrix.mul_assoc]

/-- Orthogonal paired frames with complementary Gram matrices and `‖Y‖ < 1` arise from a common
isometry under two unitaries separated by at most `2 * ‖Y‖`. -/
theorem interior_paired_frame_rotations {H J : Type} [Fintype H] [Fintype J]
    [DecidableEq H] [DecidableEq J] (X Y : Matrix H J ℂ)
    (hgram : Xᴴ * X + Yᴴ * Y = 1) (hXY : Xᴴ * Y = 0) (hYn : ‖Y‖ < 1) :
    ∃ (F : Matrix H J ℂ) (U V : Matrix H H ℂ),
      IsIsometry F ∧ U ∈ Matrix.unitaryGroup H ℂ ∧ V ∈ Matrix.unitaryGroup H ℂ ∧
      U * F = X + Y ∧ V * F = X - Y ∧ ‖U - V‖ ≤ 2 * ‖Y‖ := by
  have hG : Xᴴ * X = 1 - Yᴴ * Y := by rw [← hgram]; abel
  have hnorm : ‖Yᴴ * Y‖ < 1 := by
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg Y]
  have hGunit : IsUnit (Xᴴ * X) := hG ▸ isUnit_one_sub_of_norm_lt_one hnorm
  let C := CFC.sqrt (Xᴴ * X)
  have hC : C.PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have hCunit : IsUnit C := (CFC.isUnit_sqrt_iff _
    (Matrix.posSemidef_conjTranspose_mul_self X).nonneg).mpr hGunit
  let Cinv := Ring.inverse C
  have hCi : Cinvᴴ = Cinv := hC.isHermitian.isSelfAdjoint.ringInverse.isHermitian
  have hCCi : C * Cinv = 1 := Ring.mul_inverse_cancel C hCunit
  have hCiC : Cinv * C = 1 := Ring.inverse_mul_cancel C hCunit
  have hCsq : C * C = Xᴴ * X :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  let F := X * Cinv
  have hF : IsIsometry F := by
    change (X * Cinv)ᴴ * (X * Cinv) = 1
    rw [Matrix.conjTranspose_mul, hCi]
    calc
      _ = Cinv * (Xᴴ * X) * Cinv := by simp only [Matrix.mul_assoc]
      _ = Cinv * (C * C) * Cinv := by rw [hCsq]
      _ = 1 := by simp only [← Matrix.mul_assoc, hCiC, Matrix.one_mul, hCCi]
  have hFF : Fᴴ * F = 1 := hF
  have hFC : F * C = X := by simp only [F, Matrix.mul_assoc, hCiC, Matrix.mul_one]
  have hFY : Fᴴ * Y = 0 := by
    simp only [F, Matrix.conjTranspose_mul, hCi, Matrix.mul_assoc, hXY, Matrix.mul_zero]
  have hYF : Yᴴ * F = 0 := by
    have h := congrArg Matrix.conjTranspose hFY
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using! h
  let K := Y * Fᴴ - F * Yᴴ
  have hKh : Kᴴ = -K := by simp only [K, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; abel
  have hKn : ‖K‖ ≤ ‖Y‖ := interior_frame_skew_norm F Y hF hFY
  have hKF : K * F = Y := by
    simp only [K, Matrix.sub_mul, Matrix.mul_assoc, hFF, hYF,
      Matrix.mul_one, Matrix.mul_zero, sub_zero]
  let Q := (1 : Matrix H H ℂ) + K * K
  have hQh : Qᴴ = Q := by simp only [Q, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, hKh, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hQp : 0 ≤ Q := by
    have hb : Kᴴ * K ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (Matrix.posSemidef_conjTranspose_mul_self K).nonneg).mp (by
        rw [Matrix.l2_opNorm_conjTranspose_mul_self]
        have := hKn.trans hYn.le
        nlinarith [norm_nonneg K])
    have he : Q = 1 - Kᴴ * K := by simp only [Q, hKh, Matrix.neg_mul]; abel
    rw [he]
    exact sub_nonneg.mpr hb
  have hQF : Q * F = F * (Xᴴ * X) := by
    simp only [Q, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hKF]
    rw [show K * Y = -(F * (Yᴴ * Y)) by
      simp only [K, Matrix.sub_mul, Matrix.mul_assoc, hFY, Matrix.mul_zero, zero_sub]]
    rw [hG, Matrix.mul_sub, Matrix.mul_one]
    abel
  have hQP : Q * (F * Fᴴ) = F * (Xᴴ * X) * Fᴴ := by
    rw [← Matrix.mul_assoc, hQF]
  have hPQ : (F * Fᴴ) * Q = F * (Xᴴ * X) * Fᴴ := by
    have h := congrArg Matrix.conjTranspose hQP
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hQh,
      Matrix.mul_assoc] using! h
  have hc : Commute Q (F * Fᴴ) := hQP.trans hPQ.symm
  have hSF : CFC.sqrt Q * F = X := by
    rw [interior_sqrt_frame F hF Q hQp hc]
    have he : Fᴴ * Q * F = Xᴴ * X := by
      rw [Matrix.mul_assoc, hQF, ← Matrix.mul_assoc Fᴴ F, hFF, Matrix.one_mul]
    rw [he]
    exact hFC
  obtain ⟨hu, hv, hd⟩ := interior_skew_rotations K hKh (hKn.trans hYn.le)
  refine ⟨F, CFC.sqrt Q + K, CFC.sqrt Q - K, hF, hu, hv, ?_, ?_, ?_⟩
  · rw [Matrix.add_mul, hSF, hKF]
  · rw [Matrix.sub_mul, hSF, hKF]
  · rw [hd]
    exact mul_le_mul_of_nonneg_left hKn (by norm_num)

/-- A completed common row with a small difference block yields encodings of `M ± D` sharing
frames, with oracle distance at most `2 * √(1 + t²) * ‖D‖`. -/
private theorem interior_row_projected_pair {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M D : Matrix O I ℂ) (C : Matrix O O ℂ)
    (t : ℝ) (ht : t ≠ 0)
    (hplus : IsIsometry (Matrix.fromCols (M + D)
      (Matrix.fromCols (t⁻¹ • M - t • D) C))ᴴ)
    (hsmall : Real.sqrt (1 + t ^ 2) * ‖D‖ < 1) :
    ∃ (F : Matrix (I ⊕ (I ⊕ O)) O ℂ) (U V : Matrix (I ⊕ (I ⊕ O)) (I ⊕ (I ⊕ O)) ℂ),
      ProjectedUnitaryEncoding (M + D) U F (dilationLeft (I := I ⊕ O) (O := I))ᴴ ∧
      ProjectedUnitaryEncoding (M - D) V F (dilationLeft (I := I ⊕ O) (O := I))ᴴ ∧
      ‖U - V‖ ≤ 2 * Real.sqrt (1 + t ^ 2) * ‖D‖ := by
  let X := Matrix.fromRows Mᴴ (Matrix.fromRows (t⁻¹ • Mᴴ) Cᴴ)
  let Y := Matrix.fromRows Dᴴ (Matrix.fromRows ((-t) • Dᴴ) (0 : Matrix O O ℂ))
  have hp : X + Y = (Matrix.fromCols (M + D)
      (Matrix.fromCols (t⁻¹ • M - t • D) C))ᴴ := by
    ext k o
    cases k with
    | inl k => simp [X, Y, Matrix.conjTranspose_apply]
    | inr k =>
      cases k with
      | inl k => simp [X, Y, Matrix.conjTranspose_apply]; module
      | inr k => simp [X, Y, Matrix.conjTranspose_apply]
  have hm : X - Y = (Matrix.fromCols (M - D)
      (Matrix.fromCols (t⁻¹ • M + t • D) C))ᴴ := by
    ext k o
    cases k with
    | inl k => simp [X, Y, Matrix.conjTranspose_apply]
    | inr k =>
      cases k with
      | inl k => simp [X, Y, Matrix.conjTranspose_apply]
      | inr k => simp [X, Y, Matrix.conjTranspose_apply]
  have hXY : Xᴴ * Y = 0 := by
    simp only [X, Y, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_zero, add_zero]
    match_scalars
    field_simp
    ring
  have hYX : Yᴴ * X = 0 := by
    have h := congrArg Matrix.conjTranspose hXY
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using! h
  have hgram : Xᴴ * X + Yᴴ * Y = 1 := by
    have h : (X + Y)ᴴ * (X + Y) = 1 := by rw [hp]; exact hplus
    simpa only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
      hXY, hYX, add_zero, zero_add] using! h
  have hd := interior_common_row_distance M D C t
  have hn : ‖Y‖ = Real.sqrt (1 + t ^ 2) * ‖D‖ := by
    have h : ‖(X + Y) - (X - Y)‖ = 2 * Real.sqrt (1 + t ^ 2) * ‖D‖ := by
      rw [hp, hm, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      exact hd
    rw [show (X + Y) - (X - Y) = (2 : ℝ) • Y by module, norm_smul] at h
    norm_num at h
    linarith
  obtain ⟨F, U, V, hF, hU, hV, hUF, hVF, hUV⟩ :=
    interior_paired_frame_rotations X Y hgram hXY (by rw [hn]; exact hsmall)
  refine ⟨F, Uᴴ, Vᴴ, ⟨adjoint_unitary hU, hF, dilationLeft_adjoint_isIsometry, ?_⟩,
    ⟨adjoint_unitary hV, hF, dilationLeft_adjoint_isIsometry, ?_⟩, ?_⟩
  · calc
      _ = (U * F)ᴴ * (dilationLeft (I := I ⊕ O) (O := I))ᴴ := by
        simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = M + D := by
        rw [hUF, hp, Matrix.conjTranspose_conjTranspose]
        simp [dilationLeft, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
          Matrix.fromCols_mul_fromRows]
  · calc
      _ = (V * F)ᴴ * (dilationLeft (I := I ⊕ O) (O := I))ᴴ := by
        simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = M - D := by
        rw [hVF, hm, Matrix.conjTranspose_conjTranspose]
        simp [dilationLeft, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
          Matrix.fromCols_mul_fromRows]
  · rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
    simpa only [hn, mul_assoc] using! hUV

/-- Under the interior midpoint and gap conditions, `A` and `B` have encodings with common
frames and oracle distance at most `√(2 / (1 - ‖(A + B) / 2‖²)) * ‖A - B‖`. -/
theorem interior_common_projected_pair {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A B : Matrix O I ℂ)
    (hm : ‖(2 : ℂ)⁻¹ • (A + B)‖ < 1)
    (hg : ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1) :
    ∃ (F : Matrix (I ⊕ (I ⊕ O)) O ℂ) (U V : Matrix (I ⊕ (I ⊕ O)) (I ⊕ (I ⊕ O)) ℂ),
      ProjectedUnitaryEncoding A U F (dilationLeft (I := I ⊕ O) (O := I))ᴴ ∧
      ProjectedUnitaryEncoding B V F (dilationLeft (I := I ⊕ O) (O := I))ᴴ ∧
      ‖U - V‖ ≤ Real.sqrt (2 / (1 - ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2)) * ‖A - B‖ := by
  let M := (2 : ℂ)⁻¹ • (A + B)
  let D := (2 : ℂ)⁻¹ • (A - B)
  let m := ‖M‖
  let δ := ‖A - B‖
  let q := 1 - m ^ 2
  have hm0 : 0 ≤ m := norm_nonneg M
  have hmi : m < 1 := hm
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hgap : δ + m ^ 2 ≤ 1 := hg
  have hq : 0 < q := by dsimp only [q]; nlinarith
  have hq1 : q ≤ 1 := by dsimp only [q]; nlinarith [sq_nonneg m]
  have hδq : δ ≤ q := by dsimp only [q]; linarith
  let t := Real.sqrt ((1 + m ^ 2) / q)
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos (by positivity) hq)
  have htsq : t ^ 2 = (1 + m ^ 2) / q := Real.sq_sqrt (by positivity)
  have hcoeff : 1 + t ^ 2 = 2 / q := by
    rw [htsq]
    field_simp [hq.ne']
    dsimp only [q]
    ring
  have hinvcoeff : 1 + t⁻¹ ^ 2 = 2 / (1 + m ^ 2) := by
    rw [inv_pow, htsq, inv_div]
    have hr : 1 + m ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hr]
    dsimp only [q]
    ring
  have hDnorm : ‖D‖ = δ / 2 := by dsimp only [D, δ]; rw [norm_smul]; norm_num; ring
  have hbudget : (1 + t⁻¹ ^ 2) * ‖M‖ ^ 2 + (1 + t ^ 2) * ‖D‖ ^ 2 ≤ 1 := by
    rw [hinvcoeff, hcoeff, hDnorm]
    exact interior_common_row_budget m δ hm0 hmi hδ0 hgap
  obtain ⟨C, _, hp, _⟩ := interior_common_row_completion M D t ht.ne' hbudget
  have hdsq : δ ^ 2 ≤ q ^ 2 := (sq_le_sq₀ hδ0 hq.le).mpr hδq
  have hsmall : Real.sqrt (1 + t ^ 2) * ‖D‖ < 1 := by
    apply (sq_lt_sq₀ (by positivity) zero_le_one).mp
    rw [one_pow, mul_pow, Real.sq_sqrt (by positivity), hDnorm, hcoeff]
    have he : (2 / q) * (δ / 2) ^ 2 = δ ^ 2 / (2 * q) := by field_simp
    rw [he]
    have hle : δ ^ 2 / (2 * q) ≤ q / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact hle.trans_lt (by linarith)
  have hA : M + D = A := by
    ext o i
    simp only [M, D, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hB : M - D = B := by
    ext o i
    simp only [M, D, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  obtain ⟨F, U, V, hU, hV, hd⟩ := interior_row_projected_pair M D C t ht.ne' hp hsmall
  refine ⟨F, U, V, hA ▸ hU, hB ▸ hV, ?_⟩
  have he : 2 * Real.sqrt (1 + t ^ 2) * ‖D‖ = Real.sqrt (2 / q) * δ := by
    rw [hcoeff, hDnorm]
    ring
  simpa only [he] using! hd

/-- For an exact encoding and an odd phase list, the compressed alternating word equals the odd
singular response and the compiled query count is the list length. -/
theorem interior_complex_actual_corner_and_query_count :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (B : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (base : ℂ) (zs : List ℂ),
      ProjectedUnitaryEncoding B U L R → zs.length % 2 = 1 →
      compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
        oddSingularTransform B (interiorResponse base zs) ∧
      adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) base zs) =
        zs.length := by
  intro H I O _ _ _ _ _ _ B U L R base zs hB hodd
  exact ⟨qsvt_odd_eq_oddSingularTransform hB base zs hodd,
    queryCount_compileQSVT _ _ _ _⟩

/-- For contractions satisfying the strict midpoint and interior gap conditions, unit-phase
singular responses differ by at most `interiorRate`, in the parity-appropriate transform
[GilyenSuLowWiebe2019]. -/
theorem interior_complex_singular_response_stability :
    ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A B : Matrix O I ℂ) (base : ℂ) (zs : List ℂ),
      IsPhase base → (∀ z ∈ zs, IsPhase z) → ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
      ‖(2 : ℂ)⁻¹ • (A + B)‖ < 1 →
      ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
      (zs.length % 2 = 1 → ‖oddSingularTransform A (interiorResponse base zs) -
        oddSingularTransform B (interiorResponse base zs)‖ ≤ interiorRate A B zs.length) ∧
      (zs.length % 2 = 0 → ‖rightSingularTransform A (interiorResponse base zs) -
        rightSingularTransform B (interiorResponse base zs)‖ ≤ interiorRate A B zs.length) := by
  intro I O _ _ _ _ A B base zs hb hzs _ _ hm hg
  obtain ⟨F, U, V, hA, hB, hd⟩ := interior_common_projected_pair A B hm hg
  have hP := rangeProjector_isOrthogonalProjector hA.right_isometry
  have hQ := rangeProjector_isOrthogonalProjector hA.left_isometry
  have hrate : (zs.length : ℝ) * ‖U - V‖ ≤ interiorRate A B zs.length := by
    simpa only [interiorRate, mul_assoc] using!
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg zs.length : (0 : ℝ) ≤ zs.length)
  constructor
  · intro hodd
    have ha : compress F (phasedAlternating U (rangeProjector
        (dilationLeft (I := I ⊕ O) (O := I))ᴴ) (rangeProjector F) base zs)
        (dilationLeft (I := I ⊕ O) (O := I))ᴴ =
        oddSingularTransform A (interiorResponse base zs) :=
      qsvt_odd_eq_oddSingularTransform hA base zs hodd
    have hbEq : compress F (phasedAlternating V (rangeProjector
        (dilationLeft (I := I ⊕ O) (O := I))ᴴ) (rangeProjector F) base zs)
        (dilationLeft (I := I ⊕ O) (O := I))ᴴ =
        oddSingularTransform B (interiorResponse base zs) :=
      qsvt_odd_eq_oddSingularTransform hB base zs hodd
    rw [← ha, ← hbEq]
    exact (compress_phasedAlternating_oracle_error hA.left_isometry hA.right_isometry
      hA.unitary hB.unitary hP hQ hb zs hzs).trans hrate
  · intro heven
    have ha := qsvt_even_right_eq_rightSingularTransform hA base zs heven
    have hb' := qsvt_even_right_eq_rightSingularTransform hB base zs heven
    change ‖rightSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) -
      rightSingularTransform B (fun x => (responseP base zs).eval (x : ℂ))‖ ≤ _
    rw [← ha, ← hb']
    have h := compress_phasedAlternating_oracle_error hA.right_isometry hA.right_isometry
      (adjoint_unitary hA.unitary) (adjoint_unitary hB.unitary) hQ hP hb zs hzs
    rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] at h
    exact h.trans hrate

/-- An odd unit-phase word encoding `B` approximates the singular response of `A` within
`interiorRate` under the interior conditions, with query count equal to list length
[GilyenSuLowWiebe2019]. -/
theorem interior_complex_actual_word_corner_and_ledger :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A B : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (base : ℂ) (zs : List ℂ),
      ProjectedUnitaryEncoding B U L R → IsPhase base → (∀ z ∈ zs, IsPhase z) →
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : ℂ)⁻¹ • (A + B)‖ < 1 →
      ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 → zs.length % 2 = 1 →
      ‖compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R -
        oddSingularTransform A (interiorResponse base zs)‖ ≤ interiorRate A B zs.length ∧
      adjointQueryCount (compileQSVT (rangeProjector R) (rangeProjector L) base zs) = zs.length := by
  intro H I O _ _ _ _ _ _ A B U L R base zs hB hb hz hnA hnB hm hg hodd
  obtain ⟨hcorner, hqueries⟩ :=
      interior_complex_actual_corner_and_query_count H I O B U L R base zs hB hodd
  refine ⟨?_, hqueries⟩
  rw [hcorner, norm_sub_rev]
  exact (interior_complex_singular_response_stability I O A B base zs hb hz hnA hnB hm hg).1 hodd

end Qatlib.Concepts.QsvtCore.QsVtStability
