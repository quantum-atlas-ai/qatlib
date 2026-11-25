/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.ReciprocalReadout

@[expose] public section

/-!
# Common normalization for the spectral-bin reciprocals

[ChenXueChenEtAl2022], Appendix C.3, invokes the variable-time linear
solver of [ChildsKothariSomma2017], Section 5. Each spectral bin may use its
own Chebyshev degree. Two identity selections with opposite coefficients
adjust the preparation mass to a common positive value. They cancel in
the clean block, so the relative scale of the accepted bins is preserved.
The construction describes exact unitary matrices and their compressed
blocks. Finite-precision synthesis of preparation and selection is separate.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding.EncodingCore
  (coefficientMass coefficientLCUUnitary coefficientLCUUnitary_compress coefficientLCUUnitary_unitary)
open Qatlib.Concepts.BlockEncoding.LCU (prepareLift)
open Qatlib.Concepts.Execution.WorkspaceCP (compress)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (compressed_chebyshev signal walk walk_unitary)
open Qatlib.Concepts.QsvtCore.LinearSystems (nearOptimalReciprocalPolynomial)
open Qatlib.Concepts.WalkSearch.Spectral
  (aeval_eq_spectralDiagonal_of_action basisColumns spectralDiagonal spectralDiagonal_error_le)
open Qatlib.Papers.LinearSystems15.MainResults.Reciprocal (lemma14_chebyshev_reciprocal)
open Qatlib.Foundations.PureStateMath (Ket)
open scoped BigOperators Classical Matrix.Norms.L2Operator

/-- Extend the coefficient register by two selections with opposite real weights. -/
def commonMassCoefficients {J : Type} [Fintype J] (c : J → ℂ) (mass : ℝ) : J ⊕ Bool → ℂ :=
  Sum.elim c fun b =>
    let halfExtra := ((mass - coefficientMass c) / 2 : ℝ)
    if b then (halfExtra : ℂ) else -(halfExtra : ℂ)

/-- Both padding labels select the same identity matrix. -/
def commonMassSelections {J M : Type} [DecidableEq M] (V : J → Matrix M M ℂ) :
    J ⊕ Bool → Matrix M M ℂ :=
  Sum.elim V fun _ => 1

/-- Nonnegative padding makes the extended coefficient mass equal to the requested value. -/
theorem common_mass_coefficients_mass {J : Type} [Fintype J] (c : J → ℂ) (mass : ℝ)
    (hMass : coefficientMass c ≤ mass) :
    coefficientMass (commonMassCoefficients c mass) = mass := by
  let extra := (mass - coefficientMass c) / 2
  have hNonneg : 0 ≤ extra := div_nonneg (sub_nonneg.mpr hMass) (by norm_num)
  rw [coefficientMass, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [commonMassCoefficients, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
    ite_false, ite_true, norm_neg]
  change coefficientMass c + (‖(extra : ℂ)‖ + ‖(extra : ℂ)‖) = mass
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNonneg]
  dsimp [extra]
  ring

variable {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-- With the padded mass, scaling the clean corner back by that mass recovers the original
coefficient sum. The extra identity selections cancel exactly. -/
theorem common_mass_lcu_clean {J : Type} [Fintype J] [DecidableEq J] (c : J → ℂ)
    (V : J → Matrix M M ℂ) (seed : J) (mass : ℝ) (hPos : 0 < mass)
    (hMass : coefficientMass c ≤ mass) :
    let frame := prepareLift (I := M) (Ket (Sum.inl seed : J ⊕ Bool))
    (mass : ℂ) • compress frame
      (coefficientLCUUnitary (commonMassCoefficients c mass) (commonMassSelections V) (Sum.inl seed)) frame =
        ∑ j, c j • V j := by
  intro frame
  have hExtended := common_mass_coefficients_mass c mass hMass
  have hExtendedPos : 0 < coefficientMass (commonMassCoefficients c mass) := by
    rw [hExtended]
    exact hPos
  have hMassComplex : (mass : ℂ) ≠ 0 := by exact_mod_cast hPos.ne'
  change (mass : ℂ) • compress (prepareLift (Ket (Sum.inl seed : J ⊕ Bool))) _
    (prepareLift (Ket (Sum.inl seed : J ⊕ Bool))) = _
  rw [coefficientLCUUnitary_compress _ _ _ hExtendedPos, hExtended, Finset.smul_sum]
  have hTerm (j : J ⊕ Bool) :
      (mass : ℂ) • ((commonMassCoefficients c mass j / (mass : ℂ)) • commonMassSelections V j) =
        commonMassCoefficients c mass j • commonMassSelections V j := by
    rw [smul_smul, mul_div_cancel₀ _ hMassComplex]
  simp_rw [hTerm]
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  simp [commonMassCoefficients, commonMassSelections, neg_smul]

/-- A bin's reciprocal coefficient register includes two canceling padding labels. -/
abbrev BinReciprocalTerm (condition precision : ℝ) := ReciprocalTerm condition precision ⊕ Bool

/-- The coefficient-preparation, selection, and unpreparation operation at the common mass. -/
def binReciprocalUnitary (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    Matrix (BinReciprocalTerm condition precision × M) (BinReciprocalTerm condition precision × M) ℂ :=
  coefficientLCUUnitary (commonMassCoefficients
    (fun j => (reciprocalCoefficient condition precision j : ℂ)) mass)
    (commonMassSelections (reciprocalWalkPower condition precision C U)) (Sum.inl 0)

/-- The bin reciprocal with common mass is a unitary for a valid walk and positive
normalization that dominates the bin's coefficient mass. -/
theorem bin_reciprocal_unitary (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSelf : Uᴴ = U) (hSq : U * U = 1)
    (hPos : 0 < mass) (hMass : reciprocalMass condition precision ≤ mass) :
    binReciprocalUnitary condition precision mass C U ∈ Matrix.unitaryGroup _ ℂ := by
  have hWalk : walk C U ∈ Matrix.unitaryGroup M ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hSelf hSq)
  unfold binReciprocalUnitary
  apply coefficientLCUUnitary_unitary
  · rw [common_mass_coefficients_mass _ _ hMass]
    exact hPos
  · intro term
    cases term with
    | inl j => exact (Matrix.unitaryGroup M ℂ).pow_mem hWalk (2 * (j : ℕ) + 1)
    | inr b => exact Submonoid.one_mem _

/-- The unnormalized clean block is the Chebyshev series of the bin, with no factor depending
on the bin's own preparation mass. -/
theorem bin_reciprocal_clean (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hPos : 0 < mass)
    (hMass : reciprocalMass condition precision ≤ mass) :
    let frame := prepareLift (I := M) (Ket (Sum.inl 0 : BinReciprocalTerm condition precision))
    (mass : ℂ) • (Cᴴ * compress frame (binReciprocalUnitary condition precision mass C U) frame * C) =
      ∑ j : ReciprocalTerm condition precision, (reciprocalCoefficient condition precision j : ℂ) •
        Polynomial.aeval (signal C U) (Polynomial.Chebyshev.T ℂ ((2 * (j : ℕ) + 1 : ℕ) : ℤ)) := by
  intro frame
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  change Cᴴ * ((mass : ℂ) • compress _ (binReciprocalUnitary condition precision mass C U) _) * C = _
  unfold binReciprocalUnitary
  rw [common_mass_lcu_clean _ _ _ mass hPos hMass, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul, Matrix.smul_mul, reciprocalWalkPower, compressed_chebyshev C U hC hSq]

/-- The signal-sized corner with the coefficient register prepared and read at its clean label. -/
def compressedBinReciprocal (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ) : Matrix N N ℂ :=
  let frame := prepareLift (I := M) (Ket (Sum.inl 0 : BinReciprocalTerm condition precision))
  Cᴴ * compress frame (binReciprocalUnitary condition precision mass C U) frame * C

/-- In the signal eigenbasis the scaled clean corner evaluates the bin polynomial at each eigenvalue. -/
theorem bin_reciprocal_spectral {J : Type} [Fintype J] [DecidableEq J]
    (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hPos : 0 < mass) (hMass : reciprocalMass condition precision ≤ mass)
    (basis : OrthonormalBasis J ℂ (EuclideanSpace ℂ N)) (eigenvalue : J → ℝ)
    (hEigen : ∀ j, (signal C U).toEuclideanLin (basis j) = (eigenvalue j : ℂ) • basis j) :
    (mass : ℂ) • compressedBinReciprocal condition precision mass C U =
      spectralDiagonal basis (fun j => (↑((nearOptimalReciprocalPolynomial condition precision).eval (eigenvalue j)) : ℂ)) := by
  let polynomial := (nearOptimalReciprocalPolynomial condition precision).map Complex.ofRealHom
  have hPolynomial : (mass : ℂ) • compressedBinReciprocal condition precision mass C U =
      Polynomial.aeval (signal C U) polynomial := by
    unfold compressedBinReciprocal
    rw [bin_reciprocal_clean condition precision mass C U hC hSq hPos hMass]
    unfold polynomial
    rw [reciprocal_map_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, Polynomial.aeval_C, Algebra.smul_def]
  rw [hPolynomial, aeval_eq_spectralDiagonal_of_action basis _ _ hEigen]
  congr 1
  funext j
  exact Polynomial.eval_map_apply Complex.ofRealHom (eigenvalue j)

/-- Projecting onto a bin before applying its reciprocal gives an operator-norm error of at
most twice the precision, even if eigenvalues outside that bin fall below its cutoff. -/
theorem bin_reciprocal_masked_error {J : Type} [Fintype J] [DecidableEq J]
    (condition precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hPos : 0 < mass)
    (hMass : reciprocalMass condition precision ≤ mass)
    (hCondition : 1 < condition) (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (basis : OrthonormalBasis J ℂ (EuclideanSpace ℂ N)) (eigenvalue : J → ℝ) (inBin : J → Prop)
    (hEigen : ∀ j, (signal C U).toEuclideanLin (basis j) = (eigenvalue j : ℂ) • basis j)
    (hGap : ∀ j, inBin j → |eigenvalue j| ∈ Set.Icc condition⁻¹ 1) :
    ‖((mass : ℂ) • compressedBinReciprocal condition precision mass C U) *
      spectralDiagonal basis (fun j => if inBin j then 1 else 0) -
      spectralDiagonal basis (fun j => if inBin j then (eigenvalue j : ℂ)⁻¹ else 0)‖ ≤ 2 * precision := by
  rw [bin_reciprocal_spectral condition precision mass C U hC hSq hPos hMass basis eigenvalue hEigen,
    spectral_diagonal_mul]
  apply spectralDiagonal_error_le basis _ _ (by positivity)
  intro j
  by_cases hj : inBin j
  · simp only [hj, ite_true, mul_one]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact lemma14_chebyshev_reciprocal condition precision hCondition hPrecision hHalf _ (hGap j hj)
  · simp [hj, hPrecision.le]

/-- The first threshold at which a spectral component would accept in the ideal decision tape. -/
def firstThresholdBin {n : ℕ} (threshold : Fin n → ℝ) (value : ℝ)
    (hCovered : ∃ t, threshold t ≤ |value|) : Fin n :=
  let accepted := Finset.univ.filter fun t => threshold t ≤ |value|
  accepted.min' (by
    obtain ⟨t, ht⟩ := hCovered
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩)

/-- The ideal bin accepts its spectral component and every preceding threshold rejects it. -/
theorem first_threshold_bin_spec {n : ℕ} (threshold : Fin n → ℝ) (value : ℝ)
    (hCovered : ∃ t, threshold t ≤ |value|) :
    threshold (firstThresholdBin threshold value hCovered) ≤ |value| ∧
      ∀ t < firstThresholdBin threshold value hCovered, |value| < threshold t := by
  let accepted := Finset.univ.filter fun t => threshold t ≤ |value|
  have hNonempty : accepted.Nonempty := by
    obtain ⟨t, ht⟩ := hCovered
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
  change threshold (accepted.min' hNonempty) ≤ |value| ∧ ∀ t < accepted.min' hNonempty, |value| < threshold t
  refine ⟨(Finset.mem_filter.mp (accepted.min'_mem hNonempty)).2, ?_⟩
  intro t ht
  apply lt_of_not_ge
  intro hAccept
  exact (not_le_of_gt ht) (accepted.min'_le t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAccept⟩))

/-- In the ideal threshold schedule each spectral component uses precisely its first accepting
polynomial. Orthogonality gives one uniform error bound independent of the number of bins. -/
theorem bin_reciprocal_partition_error {J : Type} [Fintype J] [DecidableEq J] {n : ℕ}
    (condition threshold : Fin n → ℝ) (precision mass : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hSq : U * U = 1) (hPos : 0 < mass)
    (hMass : ∀ t, reciprocalMass (condition t) precision ≤ mass) (hCondition : ∀ t, 1 < condition t)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2)
    (basis : OrthonormalBasis J ℂ (EuclideanSpace ℂ N)) (eigenvalue : J → ℝ)
    (hEigen : ∀ j, (signal C U).toEuclideanLin (basis j) = (eigenvalue j : ℂ) • basis j)
    (hCovered : ∀ j, ∃ t, threshold t ≤ |eigenvalue j|) (hBound : ∀ j, |eigenvalue j| ≤ 1)
    (hCutoff : ∀ t, (condition t)⁻¹ ≤ threshold t) :
    let bin := fun j => firstThresholdBin threshold (eigenvalue j) (hCovered j)
    ‖(∑ t : Fin n, ((mass : ℂ) • compressedBinReciprocal (condition t) precision mass C U) *
        spectralDiagonal basis (fun j => if bin j = t then 1 else 0)) -
      spectralDiagonal basis (fun j => (eigenvalue j : ℂ)⁻¹)‖ ≤ 2 * precision := by
  intro bin
  have hGap (j : J) : |eigenvalue j| ∈ Set.Icc (condition (bin j))⁻¹ 1 :=
    ⟨(hCutoff (bin j)).trans (first_threshold_bin_spec threshold (eigenvalue j) (hCovered j)).1, hBound j⟩
  let coefficients (t : Fin n) (j : J) : ℂ :=
    if bin j = t then ↑((nearOptimalReciprocalPolynomial (condition t) precision).eval (eigenvalue j)) else 0
  have hBin (t : Fin n) :
      ((mass : ℂ) • compressedBinReciprocal (condition t) precision mass C U) *
        spectralDiagonal basis (fun j => if bin j = t then 1 else 0) = spectralDiagonal basis (coefficients t) := by
    rw [bin_reciprocal_spectral (condition t) precision mass C U hC hSq hPos (hMass t) basis eigenvalue hEigen,
      spectral_diagonal_mul]
    congr 1
    funext j
    by_cases h : bin j = t <;> simp [coefficients, h]
  simp_rw [hBin]
  have hDiagonal : (∑ t : Fin n, spectralDiagonal basis (coefficients t)) =
      spectralDiagonal basis (fun j => ∑ t : Fin n, coefficients t j) := by
    have hSum : (∑ t : Fin n, diagonal (coefficients t)) = diagonal (fun j => ∑ t : Fin n, coefficients t j) := by
      change (∑ t, Matrix.diagonalAddMonoidHom J ℂ (coefficients t)) =
        Matrix.diagonalAddMonoidHom J ℂ (fun j => ∑ t, coefficients t j)
      rw [← map_sum]
      congr 1
      funext j
      rw [Finset.sum_apply]
    simp only [spectralDiagonal, ← Matrix.sum_mul, ← Matrix.mul_sum, hSum]
  rw [hDiagonal]
  apply spectralDiagonal_error_le basis _ _ (by positivity)
  intro j
  rw [Finset.sum_eq_single (bin j)]
  · simp only [coefficients, ite_true, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact lemma14_chebyshev_reciprocal _ precision (hCondition (bin j)) hPrecision hHalf _ (hGap j)
  · intro t _ ht
    simp [coefficients, Ne.symm ht]
  · simp

end Qatlib.Papers.QFVMChen22.TimeStep
