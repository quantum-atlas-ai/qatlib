/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
set_option warningAsError false

namespace Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section Basis
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def basisColumns (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) :
    Matrix I J ℂ := (EuclideanSpace.basisFun I ℂ).toBasis.toMatrix b

omit [DecidableEq I] [DecidableEq J] in

@[simp] theorem basisColumns_apply (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (i : I) (j : J) : basisColumns b i j = b j i := rfl

omit [DecidableEq I] in

@[simp] theorem basisColumns_adjoint_mul (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) :
    (basisColumns b)ᴴ * basisColumns b = 1 :=
  (EuclideanSpace.basisFun I ℂ).toMatrix_orthonormalBasis_conjTranspose_mul_self b

omit [DecidableEq J] in

@[simp] theorem basisColumns_mul_adjoint (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) :
    basisColumns b * (basisColumns b)ᴴ = 1 :=
  (EuclideanSpace.basisFun I ℂ).toMatrix_orthonormalBasis_self_mul_conjTranspose b

omit [DecidableEq I] in

theorem basisColumns_norm_le (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) :
    ‖basisColumns b‖ ≤ 1 :=
  IsIsometry.norm_le_one (basisColumns_adjoint_mul b)

noncomputable def spectralDiagonal (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f : J → ℂ) : Matrix I I ℂ := basisColumns b * diagonal f * (basisColumns b)ᴴ

theorem eq_spectralDiagonal_of_action (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (T : Matrix I I ℂ) (f : J → ℂ)
    (h : ∀ j, T.toEuclideanLin (b j) = f j • b j) : T = spectralDiagonal b f := by
  have hc : T * basisColumns b = basisColumns b * diagonal f := by
    ext i j
    rw [Matrix.mul_diagonal]
    change (T.toEuclideanLin (b j)) i = b j i * f j
    have he := congrArg (fun v : EuclideanSpace ℂ I => v i) (h j)
    simpa only [PiLp.smul_apply, smul_eq_mul, mul_comm] using he
  calc
    T = T * (basisColumns b * (basisColumns b)ᴴ) := by simp
    _ = (T * basisColumns b) * (basisColumns b)ᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = spectralDiagonal b f := congrArg (fun M : Matrix I J ℂ => M * (basisColumns b)ᴴ) hc

theorem matrix_aeval_apply_of_action (T : Matrix I I ℂ) (p : Polynomial ℂ)
    (x : EuclideanSpace ℂ I) (c : ℂ) (h : T.toEuclideanLin x = c • x) :
    (aeval T p).toEuclideanLin x = p.eval c • x := by
  change (Matrix.toLpLinAlgEquiv (R := ℂ) (n := I) 2 (aeval T p)) x = _
  rw [← Polynomial.aeval_algHom_apply]
  exact Module.End.aeval_apply_of_mem_apply_eq_smul h

theorem aeval_eq_spectralDiagonal_of_action
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) (T : Matrix I I ℂ)
    (f : J → ℂ) (h : ∀ j, T.toEuclideanLin (b j) = f j • b j) (p : Polynomial ℂ) :
    aeval T p = spectralDiagonal b (fun j => p.eval (f j)) :=
  eq_spectralDiagonal_of_action b _ _ (fun j => matrix_aeval_apply_of_action T p _ _ (h j))

omit [DecidableEq I] in

theorem spectralDiagonal_sub (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f g : J → ℂ) : spectralDiagonal b f - spectralDiagonal b g =
      spectralDiagonal b (fun j => f j - g j) := by
  unfold spectralDiagonal
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem spectralDiagonal_norm_le (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f : J → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ j, ‖f j‖ ≤ ε) :
    ‖spectralDiagonal b f‖ ≤ ε := by
  have hd : ‖diagonal f‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).2 hf
  have hb := basisColumns_norm_le b
  have ha : ‖(basisColumns b)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hb
  have hl : ‖basisColumns b * diagonal f‖ ≤ ε :=
    (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul hb hd (norm_nonneg _) zero_le_one).trans_eq (one_mul ε))
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hl ha (norm_nonneg _) hε).trans_eq (mul_one ε))

theorem spectralDiagonal_error_le (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I))
    (f g : J → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ j, ‖f j - g j‖ ≤ ε) :
    ‖spectralDiagonal b f - spectralDiagonal b g‖ ≤ ε := by
  rw [spectralDiagonal_sub]
  exact spectralDiagonal_norm_le b _ hε hfg

theorem spectralDiagonal_const (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) (c : ℂ) :
    spectralDiagonal b (fun _ => c) = c • (1 : Matrix I I ℂ) := by
  have hd : diagonal (fun _ : J => c) = c • (1 : Matrix J J ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  simp only [spectralDiagonal, hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    basisColumns_mul_adjoint]
end Basis

section Singular
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

noncomputable def rightSingularTransform (A : Matrix O I ℂ) (f : ℝ → ℂ) : Matrix I I ℂ :=
  spectralDiagonal (rightSingularBasis A) (fun i => f (matrixSingularValues A i))

noncomputable def leftSingularTransform (A : Matrix O I ℂ) (f : ℝ → ℂ) : Matrix O O ℂ :=
  spectralDiagonal (leftSingularBasis A) (fun i => f (matrixSingularValues A i))

omit [DecidableEq O] in

theorem rightSingularTransform_error_le (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ i : Fin (Fintype.card I), ‖f (matrixSingularValues A i) -
      g (matrixSingularValues A i)‖ ≤ ε) :
    ‖rightSingularTransform A f - rightSingularTransform A g‖ ≤ ε :=
  spectralDiagonal_error_le _ _ _ hε hfg

theorem leftSingularTransform_error_le (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ i : Fin (Fintype.card O), ‖f (matrixSingularValues A i) -
      g (matrixSingularValues A i)‖ ≤ ε) :
    ‖leftSingularTransform A f - leftSingularTransform A g‖ ≤ ε :=
  spectralDiagonal_error_le _ _ _ hε hfg

omit [DecidableEq O] in

theorem rightSingularTransform_const (A : Matrix O I ℂ) (c : ℂ) :
    rightSingularTransform A (fun _ => c) = c • (1 : Matrix I I ℂ) :=
  spectralDiagonal_const _ _

theorem leftSingularTransform_const (A : Matrix O I ℂ) (c : ℂ) :
    leftSingularTransform A (fun _ => c) = c • (1 : Matrix O O ℂ) :=
  spectralDiagonal_const _ _

omit [DecidableEq O] in

theorem rightSingularTransform_zero (f : ℝ → ℂ) :
    rightSingularTransform (0 : Matrix O I ℂ) f = f 0 • (1 : Matrix I I ℂ) := by
  have hz : matrixSingularValues (0 : Matrix O I ℂ) = 0 := by
    simp [matrixSingularValues]
  simpa only [rightSingularTransform, hz, Finsupp.zero_apply] using
    spectralDiagonal_const (rightSingularBasis (0 : Matrix O I ℂ)) (f 0)

theorem leftSingularTransform_zero (f : ℝ → ℂ) :
    leftSingularTransform (0 : Matrix O I ℂ) f = f 0 • (1 : Matrix O O ℂ) := by
  have hz : matrixSingularValues (0 : Matrix O I ℂ) = 0 := by
    simp [matrixSingularValues]
  simpa only [leftSingularTransform, hz, Finsupp.zero_apply] using
    spectralDiagonal_const (leftSingularBasis (0 : Matrix O I ℂ)) (f 0)

theorem gram_aeval_eq_rightSingularTransform (A : Matrix O I ℂ) (p : Polynomial ℂ) :
    aeval (Aᴴ * A) p = rightSingularTransform A (fun x => p.eval ((x : ℂ) ^ 2)) :=
  aeval_eq_spectralDiagonal_of_action (rightSingularBasis A) _ _
    (gram_apply_rightSingularBasis A) p

theorem leftGram_apply_leftSingularBasis (A : Matrix O I ℂ)
    (j : Fin (Fintype.card O)) :
    (A * Aᴴ).toEuclideanLin (leftSingularBasis A j) =
      ((matrixSingularValues A j : ℂ) ^ 2) • leftSingularBasis A j := by
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.comp_apply]
  by_cases hj : (j : ℕ) < Module.finrank ℂ A.toEuclideanLin.range
  · rw [leftSingularBasis_apply_of_lt A j hj, adjoint_apply_leftSingularVector,
      map_smul, apply_rightSingularBasis_eq_smul_leftSingularVector, smul_smul, pow_two]
  · have hj' : Module.finrank ℂ A.toEuclideanLin.range ≤ (j : ℕ) := le_of_not_gt hj
    have hz : matrixSingularValues A j = 0 :=
      A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr hj'
    rw [adjoint_apply_leftSingularBasis_of_rank_le A j hj', map_zero, hz]
    simp

theorem leftGram_aeval_eq_leftSingularTransform (A : Matrix O I ℂ) (p : Polynomial ℂ) :
    aeval (A * Aᴴ) p = leftSingularTransform A (fun x => p.eval ((x : ℂ) ^ 2)) :=
  aeval_eq_spectralDiagonal_of_action (leftSingularBasis A) _ _
    (leftGram_apply_leftSingularBasis A) p

omit [DecidableEq O] in

theorem matrixSingularValues_le_spectralNorm (A : Matrix O I ℂ) (i : ℕ) :
    matrixSingularValues A i ≤ ‖A‖ := by
  by_cases hi : i < Fintype.card I
  · calc
      matrixSingularValues A i = ‖A.toEuclideanLin (rightSingularBasis A ⟨i, hi⟩)‖ :=
        (norm_apply_rightSingularBasis A ⟨i, hi⟩).symm
      _ ≤ ‖LinearMap.toContinuousLinearMap A.toEuclideanLin‖ * ‖rightSingularBasis A ⟨i, hi⟩‖ :=
        (LinearMap.toContinuousLinearMap A.toEuclideanLin).le_opNorm _
      _ = ‖A‖ := by
        rw [norm_rightSingularBasis, mul_one]
        rfl
  · rw [matrixSingularValues_of_card_le A (le_of_not_gt hi)]
    exact norm_nonneg _

end Singular

section QSVT
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem qsvt_even_right_eq_rightSingularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress R (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R =
      rightSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) := by
  rw [qsvt_even_right_eq_responseFactor h base zs heven,
    gram_aeval_eq_rightSingularTransform, responseP_factor_even base zs heven]
  simp only [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

theorem qsvt_even_left_eq_leftSingularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L =
      leftSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) := by
  rw [qsvt_even_left_eq_responseFactor h base zs heven,
    leftGram_aeval_eq_leftSingularTransform, responseP_factor_even base zs heven]
  simp only [evenSingularPolynomial, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]

theorem qsvt_even_right_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    BlockEncoding (rightSingularTransform A f)
      (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R R 1 ε := by
  refine ⟨phasedAlternating_unitary (adjoint_unitary h.unitary)
    (rangeProjector_isOrthogonalProjector h.left_isometry)
    (rangeProjector_isOrthogonalProjector h.right_isometry) hb zs hzs,
    h.right_isometry, h.right_isometry, by norm_num, hε, ?_⟩
  rw [one_smul, qsvt_even_right_eq_rightSingularTransform h base zs heven]
  exact rightSingularTransform_error_le A _ _ hε
    (fun i => by simpa only [norm_sub_rev] using happrox i)

theorem qsvt_even_left_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card O),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    BlockEncoding (leftSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L L 1 ε := by
  refine ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.left_isometry, by norm_num, hε, ?_⟩
  rw [one_smul, qsvt_even_left_eq_leftSingularTransform h base zs heven]
  exact leftSingularTransform_error_le A _ _ hε
    (fun i => by simpa only [norm_sub_rev] using happrox i)

theorem qsvt_even_right_counted_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding (rightSingularTransform A f) (evaluate U cs) R R 1 ε ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨(compileQSVT (rangeProjector L) (rangeProjector R) base zs).map swapQueries,
    ?_, ?_, ?_⟩
  · rw [evaluate_swapQueries, evaluate_compileQSVT]
    exact qsvt_even_right_approximation h hb zs hzs heven f hε happrox
  · rw [adjointQueryCount_swapQueries, queryCount_compileQSVT]
  · rw [adjointGateCount_swapQueries, gateCount_compileQSVT]

theorem encoded_singularValues_mem_unitInterval
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (i : ℕ) :
    matrixSingularValues A i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨matrixSingularValues_nonneg A i, (matrixSingularValues_le_spectralNorm A i).trans ?_⟩
  rw [← h.encoded]
  exact (compress_norm_le h.left_isometry h.right_isometry U).trans
    (unitary_norm_le_one h.unitary)

theorem qsvt_even_right_uniform_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    BlockEncoding (rightSingularTransform A f)
      (phasedAlternating Uᴴ (rangeProjector L) (rangeProjector R) base zs) R R 1 ε :=
  qsvt_even_right_approximation h hb zs hzs heven f hε
    (fun i => happrox _ (encoded_singularValues_mem_unitInterval h i))

theorem qsvt_even_left_uniform_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    BlockEncoding (leftSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L L 1 ε :=
  qsvt_even_left_approximation h hb zs hzs heven f hε
    (fun i => happrox _ (encoded_singularValues_mem_unitInterval h i))

theorem qsvt_even_left_counted_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card O),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding (leftSingularTransform A f) (evaluate U cs) L L 1 ε ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    queryCount_compileQSVT _ _ _ _, gateCount_compileQSVT _ _ _ _⟩
  rw [evaluate_compileQSVT]
  exact qsvt_even_left_approximation h hb zs hzs heven f hε happrox

end QSVT

end Qatlib.Concepts.WalkSearch.Spectral
