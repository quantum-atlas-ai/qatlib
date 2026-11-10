/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.Approximation
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

section Singular
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

noncomputable def leftSingularColumns (A : Matrix O I ℂ) :
    Matrix O (Fin (Fintype.card I)) ℂ := fun o i => leftSingularVector A i o

omit [DecidableEq O] in

theorem leftSingularColumns_gram (A : Matrix O I ℂ) :
    (leftSingularColumns A)ᴴ * leftSingularColumns A =
      diagonal (fun i : Fin (Fintype.card I) =>
        if matrixSingularValues A i = 0 then (0 : ℂ) else 1) := by
  classical
  ext i j
  have he : ((leftSingularColumns A)ᴴ * leftSingularColumns A) i j =
      inner ℂ (leftSingularVector A i) (leftSingularVector A j) := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, leftSingularColumns,
      PiLp.inner_apply, mul_comm]
  rw [he]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : matrixSingularValues A i = 0
    · rw [if_pos hi, leftSingularVector_eq_zero A i hi]
      simp
    · have hpos : 0 < matrixSingularValues A i :=
        lt_of_le_of_ne (matrixSingularValues_nonneg A i) (Ne.symm hi)
      have hr := (matrixSingularValues_pos_iff_lt_finrank_range A).mp hpos
      rw [if_neg hi, inner_self_eq_norm_sq_to_K, norm_leftSingularVector A i hr]
      simp
  · rw [inner_leftSingularVector_of_ne A hij]
    simp [hij]

omit [DecidableEq O] in

theorem leftSingularColumns_norm_le (A : Matrix O I ℂ) :
    ‖leftSingularColumns A‖ ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg _), pow_two,
    ← Matrix.l2_opNorm_conjTranspose_mul_self, leftSingularColumns_gram,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  split_ifs <;> simp

omit [DecidableEq O] in

theorem mul_rightSingularBasis_columns (A : Matrix O I ℂ) :
    A * basisColumns (rightSingularBasis A) = leftSingularColumns A *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) := by
  ext o i
  rw [Matrix.mul_diagonal]
  change (A.toEuclideanLin (rightSingularBasis A i)) o = _
  have he := congrArg (fun v : EuclideanSpace ℂ O => v o)
    (apply_rightSingularBasis_eq_smul_leftSingularVector A i)
  simpa only [leftSingularColumns, PiLp.smul_apply, smul_eq_mul, mul_comm] using he

noncomputable def oddSingularTransform (A : Matrix O I ℂ) (f : ℝ → ℂ) : Matrix O I ℂ :=
  leftSingularColumns A * diagonal (fun i : Fin (Fintype.card I) => f (matrixSingularValues A i)) *
    (basisColumns (rightSingularBasis A))ᴴ

omit [DecidableEq O] in

theorem oddSingularTransform_sub (A : Matrix O I ℂ) (f g : ℝ → ℂ) :
    oddSingularTransform A f - oddSingularTransform A g =
      oddSingularTransform A (fun x => f x - g x) := by
  unfold oddSingularTransform
  rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq O] in

theorem oddSingularTransform_norm_le (A : Matrix O I ℂ) (f : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ i : Fin (Fintype.card I), ‖f (matrixSingularValues A i)‖ ≤ ε) :
    ‖oddSingularTransform A f‖ ≤ ε := by
  have hd : ‖diagonal (fun i : Fin (Fintype.card I) => f (matrixSingularValues A i))‖ ≤ ε := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hε).2 hf
  have hr : ‖(basisColumns (rightSingularBasis A))ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact basisColumns_norm_le _
  have hl : ‖leftSingularColumns A *
      diagonal (fun i : Fin (Fintype.card I) => f (matrixSingularValues A i))‖ ≤ ε :=
    (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul (leftSingularColumns_norm_le A) hd (norm_nonneg _) zero_le_one).trans_eq
        (one_mul ε))
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul hl hr (norm_nonneg _) hε).trans_eq (mul_one ε))

omit [DecidableEq O] in

theorem oddSingularTransform_error_le (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ i : Fin (Fintype.card I), ‖f (matrixSingularValues A i) -
      g (matrixSingularValues A i)‖ ≤ ε) :
    ‖oddSingularTransform A f - oddSingularTransform A g‖ ≤ ε := by
  rw [oddSingularTransform_sub]
  exact oddSingularTransform_norm_le A _ hε hfg

omit [DecidableEq O] in

theorem oddSingularTransform_congr_positive (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    (hfg : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      f (matrixSingularValues A i) = g (matrixSingularValues A i)) :
    oddSingularTransform A f = oddSingularTransform A g := by
  unfold oddSingularTransform
  apply congrArg (fun M : Matrix O (Fin (Fintype.card I)) ℂ =>
    M * (basisColumns (rightSingularBasis A))ᴴ)
  ext o i
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hi : matrixSingularValues A i = 0
  · simp [leftSingularColumns, leftSingularVector_eq_zero A i hi]
  · rw [hfg i (lt_of_le_of_ne (matrixSingularValues_nonneg A i) (Ne.symm hi))]

omit [DecidableEq O] in

theorem oddSingularTransform_norm_le_positive (A : Matrix O I ℂ) (f : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖f (matrixSingularValues A i)‖ ≤ ε) :
    ‖oddSingularTransform A f‖ ≤ ε := by
  let g : ℝ → ℂ := fun x => if x = 0 then 0 else f x
  have he : oddSingularTransform A f = oddSingularTransform A g :=
    oddSingularTransform_congr_positive A f g
      (fun i hi => by dsimp only [g]; rw [if_neg (ne_of_gt hi)])
  rw [he]
  apply oddSingularTransform_norm_le A g hε
  intro i
  by_cases hi : matrixSingularValues A i = 0
  · dsimp only [g]
    rw [if_pos hi, norm_zero]
    exact hε
  · dsimp only [g]
    rw [if_neg hi]
    exact hf i (lt_of_le_of_ne (matrixSingularValues_nonneg A i) (Ne.symm hi))

omit [DecidableEq O] in

theorem oddSingularTransform_error_le_positive (A : Matrix O I ℂ) (f g : ℝ → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖f (matrixSingularValues A i) - g (matrixSingularValues A i)‖ ≤ ε) :
    ‖oddSingularTransform A f - oddSingularTransform A g‖ ≤ ε := by
  rw [oddSingularTransform_sub]
  exact oddSingularTransform_norm_le_positive A _ hε hfg

omit [DecidableEq O] in

theorem oddSingularTransform_zero_function (A : Matrix O I ℂ) :
    oddSingularTransform A (fun _ => 0) = 0 := by
  simp [oddSingularTransform]

omit [DecidableEq O] in

theorem oddSingularTransform_id (A : Matrix O I ℂ) :
    oddSingularTransform A (fun x => (x : ℂ)) = A := by
  rw [oddSingularTransform, ← mul_rightSingularBasis_columns, Matrix.mul_assoc,
    basisColumns_mul_adjoint, Matrix.mul_one]

omit [DecidableEq O] in

theorem oddSingularTransform_zero (f : ℝ → ℂ) :
    oddSingularTransform (0 : Matrix O I ℂ) f = 0 := by
  have hc : leftSingularColumns (0 : Matrix O I ℂ) = 0 := by
    ext o i
    have hz : matrixSingularValues (0 : Matrix O I ℂ) i = 0 := by
      simp [matrixSingularValues]
    simp [leftSingularColumns, leftSingularVector_eq_zero _ _ hz]
  simp [oddSingularTransform, hc]

theorem mul_gram_aeval_eq_oddSingularTransform (A : Matrix O I ℂ) (p : Polynomial ℂ) :
    A * aeval (Aᴴ * A) p =
      oddSingularTransform A (fun x => (x : ℂ) * p.eval ((x : ℂ) ^ 2)) := by
  rw [gram_aeval_eq_rightSingularTransform]
  unfold rightSingularTransform spectralDiagonal oddSingularTransform
  rw [← Matrix.mul_assoc A, ← Matrix.mul_assoc A, mul_rightSingularBasis_columns]
  rw [Matrix.mul_assoc (leftSingularColumns A), Matrix.diagonal_mul_diagonal]

end Singular

section QSVT
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem qsvt_odd_eq_oddSingularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R =
      oddSingularTransform A (fun x => (responseP base zs).eval (x : ℂ)) := by
  rw [qsvt_odd_eq_responseFactor h base zs hodd,
    mul_gram_aeval_eq_oddSingularTransform, responseP_factor_odd base zs hodd]
  simp only [oddSingularPolynomial, evenSingularPolynomial, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem qsvt_odd_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    BlockEncoding (oddSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R 1 ε := by
  refine ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.right_isometry, by norm_num, hε, ?_⟩
  rw [one_smul, qsvt_odd_eq_oddSingularTransform h base zs hodd]
  exact oddSingularTransform_error_le A _ _ hε
    (fun i => by simpa only [norm_sub_rev] using happrox i)

theorem qsvt_odd_positive_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    BlockEncoding (oddSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R 1 ε := by
  refine ⟨phasedAlternating_unitary h.unitary
    (rangeProjector_isOrthogonalProjector h.right_isometry)
    (rangeProjector_isOrthogonalProjector h.left_isometry) hb zs hzs,
    h.left_isometry, h.right_isometry, by norm_num, hε, ?_⟩
  rw [one_smul, qsvt_odd_eq_oddSingularTransform h base zs hodd]
  exact oddSingularTransform_error_le_positive A _ _ hε
    (fun i hi => by simpa only [norm_sub_rev] using happrox i hi)

theorem qsvt_odd_gapped_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {δ ε : ℝ} (hε : 0 ≤ ε)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      δ ≤ matrixSingularValues A i)
    (happrox : ∀ x ∈ Set.Icc δ 1, ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    BlockEncoding (oddSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R 1 ε :=
  qsvt_odd_positive_approximation h hb zs hzs hodd f hε
    (fun i hi => happrox _ ⟨hgap i hi, (encoded_singularValues_mem_unitInterval h i).2⟩)

theorem qsvt_odd_annihilates_kernel
    {K : Type*} {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) {v : Matrix I K ℂ} (hv : A * v = 0) :
    compress L (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) R * v = 0 := by
  have hf : A * v = (0 : ℂ) • (0 : Matrix O K ℂ) := by simpa using hv
  have hb : Aᴴ * (0 : Matrix O K ℂ) = (0 : ℂ) • v := by simp
  simpa using qsvt_odd h hf hb base zs hodd

theorem qsvt_odd_uniform_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖(responseP base zs).eval (x : ℂ) - f x‖ ≤ ε) :
    BlockEncoding (oddSingularTransform A f)
      (phasedAlternating U (rangeProjector R) (rangeProjector L) base zs) L R 1 ε :=
  qsvt_odd_approximation h hb zs hzs hodd f hε
    (fun i => happrox _ (encoded_singularValues_mem_unitInterval h i))

theorem qsvt_odd_counted_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I),
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    queryCount_compileQSVT _ _ _ _, gateCount_compileQSVT _ _ _ _⟩
  rw [evaluate_compileQSVT]
  exact qsvt_odd_approximation h hb zs hzs hodd f hε happrox

theorem qsvt_odd_counted_positive_approximation
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1)
    (f : ℝ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
      ‖(responseP base zs).eval (matrixSingularValues A i : ℂ) - f (matrixSingularValues A i)‖ ≤ ε) :
    ∃ cs : List (AdjointStep H),
      BlockEncoding (oddSingularTransform A f) (evaluate U cs) L R 1 ε ∧
      adjointQueryCount cs = zs.length ∧ adjointGateCount cs = zs.length + 1 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) base zs, ?_,
    queryCount_compileQSVT _ _ _ _, gateCount_compileQSVT _ _ _ _⟩
  rw [evaluate_compileQSVT]
  exact qsvt_odd_positive_approximation h hb zs hzs hodd f hε happrox

end QSVT
end Qatlib.Concepts.CoherentSim.CoherentOAA
