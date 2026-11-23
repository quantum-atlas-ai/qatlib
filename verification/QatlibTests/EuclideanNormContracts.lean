/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QLinearSys15.MainResults.MainRuntime.SourceVocabulary
public import Qatlib.Papers.QSDPsolver17.MainResults.UpperBound.SparseTrace
public import Qatlib.Papers.QTopEigenvec24.MainResults.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Euclidean norms in paper specifications

Concrete consumers check the normalization of linear-system solutions, the
accuracy of finite-dimensional eigenvector approximations, and spectral
constraints on non-diagonal matrices.
-/

noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QLinearSys15.MainResults.MainRuntime
open Qatlib.Papers.QSDPsolver17.MainResults Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QTopEigenvec24.MainResults
open scoped BigOperators Matrix

namespace QatlibTests.EuclideanNormContracts

/-- The vector with both amplitudes equal to one. -/
def ones : Fin 2 → ℂ := fun _ => 1

/-- The constant-one vector passes the supremum norm test but fails the Euclidean test. -/
theorem ones_pass_sup_not_euclidean : ‖ones‖ = 1 ∧ ‖toEuclidean_fromVec ones‖ ≠ 1 := by
  constructor
  · change ‖fun _ : Fin 2 => (1 : ℂ)‖ = 1
    rw [pi_norm_const, norm_one]
  · intro h
    have hm := norm_toEuclidean_fromVec_sq ones
    rw [h] at hm
    norm_num [ones, Fin.sum_univ_two] at hm

/-- A two-dimensional linear system cannot take the unnormalized all-ones right-hand side. -/
theorem linear_system_rejects_all_ones :
    ¬ ∃ P : LinearSystemProblem, P.N = 2 ∧ P.b = fun _ => 1 := by
  rintro ⟨P, hN, hb⟩
  have hmass : (∑ i, ‖P.b i‖ ^ 2) = 1 := P.b_normalized
  have hcount : (∑ _ : Fin P.N, ‖(1 : ℂ)‖ ^ 2) = (P.N : ℝ) := by simp
  rw [hb, hcount, hN] at hmass
  norm_num at hmass

/-- The identity linear system with a uniform quantum state and exact row lists. -/
def identityProblem : LinearSystemProblem where
  N := 2
  N_pos := by norm_num
  A := 1
  hermitian := by simp
  kappa := 1
  kappa_pos := by norm_num
  spectrum_lower := by intro v _; simp
  spectrum_upper := by intro v; simp
  sparsity := 1
  sparsity_pos := by norm_num
  rowNonzeros i := [(i, 1)]
  rowNonzeros_spec := by
    intro i j a
    by_cases h : j = i
    · subst j
      simp
    · rw [Matrix.one_apply_ne' h]
      simp [h]
  rowNonzeros_nodup := by simp
  rowNonzero_le := by simp
  TA := 1
  TA_pos := by norm_num
  TB := 1
  TB_pos := by norm_num
  b := Uniform (Fin 2)
  b_norm := (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_uniform (by simp))

/-- A fixture returning the right-hand side and norm estimate one for the identity system. -/
def exactIdentitySolver : CostedQlsSolver identityProblem where
  output _ := ⟨identityProblem.b, identityProblem.b_normalized, 1⟩
  cost _ := 0

/-- Identity-system input, target, and exact output satisfy the public contract. -/
theorem identity_system_accepts_normalized_solution :
    Normalized identityProblem.b ∧ Normalized identityProblem.targetAmplitude ∧
      ProducesSolution identityProblem exactIdentitySolver 0 := by
  have hsol : identityProblem.solution = identityProblem.b := by
    change (1 : Matrix (Fin identityProblem.N) (Fin identityProblem.N) ℂ)⁻¹ *ᵥ
      identityProblem.b = identityProblem.b
    rw [inv_one, Matrix.one_mulVec]
  have hnorm : ‖toEuclidean_fromVec identityProblem.solution‖ = 1 := by
    rw [hsol, identityProblem.b_norm]
  have htarget : identityProblem.targetAmplitude = identityProblem.b := by
    funext i
    unfold LinearSystemProblem.targetAmplitude
    rw [hnorm, hsol, Complex.ofReal_one, div_one]
  refine ⟨identityProblem.b_normalized, identityProblem.targetAmplitude_normalized, ?_, ?_⟩
  · change ‖toEuclidean_fromVec (identityProblem.b - identityProblem.targetAmplitude)‖ ≤ 0
    rw [htarget, sub_self]
    simp [toEuclidean_fromVec]
  · change |1 - ‖toEuclidean_fromVec identityProblem.solution‖| ≤ 0
    rw [hnorm]
    norm_num

/-- An identity row must include its diagonal entry, even if its reported length fits. -/
theorem identity_rejects_empty_rows :
    ¬ ∃ P : LinearSystemProblem, P.A = 1 ∧ ∀ i, P.rowNonzeros i = [] := by
  rintro ⟨P, hA, hrows⟩
  let i : Fin P.N := ⟨0, P.N_pos⟩
  have hm := (P.rowNonzeros_spec i i 1).mpr (by simp [hA])
  simp [hrows i] at hm

/-- A listed value must agree with the identity matrix at that column. -/
theorem identity_rejects_wrong_values :
    ¬ ∃ P : LinearSystemProblem, P.A = 1 ∧ ∃ i, (i, (2 : ℂ)) ∈ P.rowNonzeros i := by
  rintro ⟨P, hA, i, hi⟩
  have h := ((P.rowNonzeros_spec i i 2).mp hi).2
  norm_num [hA] at h

/-- The identity cannot claim a sparsity strictly below one. -/
theorem identity_rejects_understated_sparsity :
    ¬ ∃ P : LinearSystemProblem, P.A = 1 ∧ P.sparsity = 1 / 2 := by
  rintro ⟨P, hA, hs⟩
  let i : Fin P.N := ⟨0, P.N_pos⟩
  have hn : 1 ≤ (Finset.univ.filter fun j => P.A i j ≠ 0).card :=
    Finset.one_le_card.mpr ⟨i, by simp [hA]⟩
  have hb := P.row_support_card_le i
  rw [hs] at hb
  have hn' : (1 : ℝ) ≤ ((Finset.univ.filter fun j => P.A i j ≠ 0).card : ℝ) := by
    exact_mod_cast hn
  linarith

/-- The all-ones vector fails the eigenvector interface's unit predicate. -/
theorem ones_rejected_as_unit : ¬ IsUnitVector ones := by
  simpa only [IsUnitVector, ell2C_eq_euclidean_norm] using ones_pass_sup_not_euclidean.2

/-- Both computational basis vectors pass the unit predicate. -/
theorem basis_vectors_are_unit :
    IsUnitVector (Ket (0 : Fin 2)) ∧ IsUnitVector (Ket (1 : Fin 2)) :=
  ⟨(isUnitVector_iff_normalized _).mpr (normalized_ket _),
    (isUnitVector_iff_normalized _).mpr (normalized_ket _)⟩

/-- An exact representative is within zero Euclidean distance of itself. -/
theorem basis_exact_approximation : L2Approximates (Ket (0 : Fin 2)) (Ket 0) 0 := by
  simp [L2Approximates, ell2C]

/-- Orthogonal basis states are at supremum distance at most one but Euclidean distance above one. -/
theorem orthogonal_basis_rejects_tolerance_one :
    ‖Ket (1 : Fin 2) - Ket (0 : Fin 2)‖ ≤ 1 ∧
      ¬ L2Approximates (Ket (0 : Fin 2)) (Ket 1) 1 := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num [Ket]
  · intro h
    have hs : (∑ i : Fin 2, ‖(Ket (1 : Fin 2) - Ket 0 : Fin 2 → ℂ) i‖ ^ 2) = 2 := by
      norm_num [Ket, Fin.sum_univ_two]
    rw [L2Approximates, ell2C, hs] at h
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]

/-- A Hermitian reflection mixing both coordinates. -/
def reflection : Matrix (Fin 2) (Fin 2) ℂ := !![3 / 5, 4 / 5; 4 / 5, -3 / 5]

/-- A Hermitian positive matrix whose smaller eigenvalue is below one. -/
def lowerEnvelope : Matrix (Fin 2) (Fin 2) ℂ := !![4 / 3, 2 / 3; 2 / 3, 4 / 3]

/-- The ℓ² operator constraint accepts the non-diagonal reflection, while the Pi bound fails. -/
theorem reflection_passes_spectral_bound :
    reflection.IsHermitian ∧ OpNormLE reflection 1 ∧
      ¬ (∀ x : Fin 2 → ℂ, ‖reflection.mulVec x‖ ≤ 1 * ‖x‖) := by
  refine ⟨?_, ?_, ?_⟩
  · change reflectionᴴ = reflection
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [reflection]
  · apply (opNormLE_iff_mulVec reflection (c := 1) (by norm_num)).mpr
    intro x
    rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply le_of_eq
    apply congrArg Real.sqrt
    change (∑ i, ‖(reflection.mulVec (WithLp.ofLp x)) i‖ ^ 2) = ∑ i, ‖x i‖ ^ 2
    norm_num [reflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  · intro h
    have hbad := (norm_le_pi_norm (reflection.mulVec ones) (0 : Fin 2)).trans (h ones)
    rw [ones_pass_sup_not_euclidean.1] at hbad
    norm_num [reflection, ones, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hbad

open scoped Matrix.Norms.L2Operator in
/-- The reflection is at spectral operator distance exactly one from zero. -/
theorem reflection_spectral_distance : opDistℂ reflection 0 = 1 := by
  have hunit : reflectionᴴ * reflection = 1 := by
    rw [show reflectionᴴ = reflection from reflection_passes_spectral_bound.1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_two]
  have hnorm : ‖(1 : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal, pi_norm_const, norm_one]
  have hsq := Matrix.l2_opNorm_conjTranspose_mul_self reflection
  rw [hunit, hnorm] at hsq
  rw [opDistℂ, sub_zero, opNormℂ_eq_l2_opNorm]
  nlinarith [norm_nonneg reflection]

/-- The same non-diagonal matrix satisfies the real ℓ² operator-norm bound. -/
theorem real_reflection_passes_spectral_bound :
    OpNormLE_R (!![3 / 5, 4 / 5; 4 / 5, -3 / 5] : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
  apply (opNormLE_R_iff_mulVec _ (c := 1) (by norm_num)).mpr
  intro x
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i, ((!![3 / 5, 4 / 5; 4 / 5, -3 / 5] : Matrix (Fin 2) (Fin 2) ℝ).mulVec
    (WithLp.ofLp x) i) ^ 2) ≤ ∑ i, (x i) ^ 2
  apply le_of_eq
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The spectral lower bound holds with equality for the identity. -/
theorem identity_passes_spectral_lower_bound : PSDMinusOne (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  change PSD ((1 : Matrix (Fin 2) (Fin 2) ℂ) - 1)
  simp [PSD, Matrix.isHermitian_zero]

/-- The old supremum-norm lower-bound test accepts the matrix with eigenvalue two thirds. -/
theorem lower_envelope_passes_sup_bound (x : Fin 2 → ℂ) :
    ‖x‖ ^ 2 ≤ (∑ i, star (x i) * (lowerEnvelope.mulVec x) i).re := by
  let q : ℝ := (∑ i, star (x i) * (lowerEnvelope.mulVec x) i).re
  have hzero : q - ‖x 0‖ ^ 2 = (1 / 3 : ℝ) * ‖x 0 + 2 * x 1‖ ^ 2 := by
    norm_num [q, lowerEnvelope, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hone : q - ‖x 1‖ ^ 2 = (1 / 3 : ℝ) * ‖2 * x 0 + x 1‖ ^ 2 := by
    norm_num [q, lowerEnvelope, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hcoord (i : Fin 2) : ‖x i‖ ^ 2 ≤ q := by
    fin_cases i
    · change ‖x (0 : Fin 2)‖ ^ 2 ≤ q
      rw [← sub_nonneg, hzero]
      positivity
    · change ‖x (1 : Fin 2)‖ ^ 2 ≤ q
      rw [← sub_nonneg, hone]
      positivity
  have hq : 0 ≤ q := (sq_nonneg _).trans (hcoord 0)
  have hsup : ‖x‖ ≤ Real.sqrt q := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg q)).mpr
    intro i
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg q), Real.sq_sqrt hq]
    exact hcoord i
  calc
    ‖x‖ ^ 2 ≤ (Real.sqrt q) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg q)).mpr hsup
    _ = q := Real.sq_sqrt hq

/-- The quadratic form of the shifted matrix is negative at the antisymmetric vector. -/
theorem lower_envelope_rejected : ¬ PSDMinusOne lowerEnvelope := by
  intro h
  let x : Fin 2 → ℂ := fun i => if i = 0 then 1 else -1
  have hx := h.2 x
  norm_num [lowerEnvelope, x, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hx

end QatlibTests.EuclideanNormContracts
