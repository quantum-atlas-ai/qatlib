/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.Linearization
public import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
public import Qatlib.Concepts.PolynomialCalc.QubitizedPower
public import Qatlib.Concepts.WalkSearch.Spectral.Approximation
public import Qatlib.Foundations.MatrixAlgebra.HermitianLift
public import Qatlib.Papers.LinearSystems15.MainResults.Reciprocal.ChebyshevReciprocal

@[expose] public section

/-!
# Chebyshev inverse operation for a linearized stencil

[ChenXueChenEtAl2022], Section 3.2 and Appendix C, invoke a quantum linear
solver on the linearized stencil. This module uses the odd Chebyshev series
of [ChildsKothariSomma2017], Section 4.2, to build the prepare–select–unprepare
operation from a supplied Hermitian-involution encoding. The block lift
allows the stencil to be nonsymmetric. The operation has an exact
postselection block. Sparse oracle synthesis, variable-time amplification
and the cost of estimating the solution norm require additional proofs.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PolynomialCalc.QubitizedPower
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Foundations.PureStateMath (Ket)
open Qatlib.Foundations.MatrixAlgebra.HermitianLift (lift)
open Qatlib.Papers.LinearSystems15.MainResults.Reciprocal (lemma14_chebyshev_reciprocal)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open scoped BigOperators

/-- The index of an odd Chebyshev term in the truncated reciprocal series. -/
abbrev ReciprocalTerm (condition precision : ℝ) := Fin (nearOptimalReciprocalJ condition precision + 1)

/-- The signed binomial-tail coefficient of the odd Chebyshev term. -/
def reciprocalCoefficient (condition precision : ℝ) (j : ReciprocalTerm condition precision) : ℝ :=
  let b := nearOptimalReciprocalB condition precision
  4 * (-1 : ℝ) ^ (j : ℕ) *
    (∑ i ∈ Finset.Ico ((j : ℕ) + 1) (b + 1), ((2 * b).choose (b + i) : ℝ)) /
      (2 : ℝ) ^ (2 * b)

/-- The real scalar series used in the circuit approximates the reciprocal on the signed gap.
The approximation error follows from the already formalized [ChildsKothariSomma2017], Lemma 14. -/
theorem reciprocal_series_error (condition precision : ℝ) (hCondition : 1 < condition)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2) (x : ℝ)
    (hGap : |x| ∈ Set.Icc condition⁻¹ 1) :
    |(∑ j : ReciprocalTerm condition precision, reciprocalCoefficient condition precision j *
      (Polynomial.Chebyshev.T ℝ ((2 * (j : ℕ) + 1 : ℕ) : ℤ)).eval x) - x⁻¹| ≤ 2 * precision := by
  have h := lemma14_chebyshev_reciprocal condition precision hCondition hPrecision hHalf x hGap
  simp only [nearOptimalReciprocalPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, ← Fin.sum_univ_eq_sum_range] at h
  exact h

/-- The absolute coefficient mass used to normalize the selected walk powers. -/
def reciprocalMass (condition precision : ℝ) : ℝ :=
  coefficientMass (fun j => (reciprocalCoefficient condition precision j : ℂ))

/-- The lowest-degree odd term has positive coefficient for the CKS input range, so the
coefficient preparation always has nonzero mass in that range. -/
theorem reciprocal_mass_pos (condition precision : ℝ) (hCondition : 1 < condition)
    (hPrecision : 0 < precision) (hHalf : precision ≤ 1 / 2) :
    0 < reciprocalMass condition precision := by
  let b := nearOptimalReciprocalB condition precision
  let j₀ : ReciprocalTerm condition precision := ⟨0, Nat.zero_lt_succ _⟩
  have hc : 0 < condition := zero_lt_one.trans hCondition
  have hLog : 0 < Real.log (condition / precision) :=
    Real.log_pos ((lt_div_iff₀ hPrecision).2 (by nlinarith))
  have hb : 0 < b := Nat.ceil_pos.mpr (mul_pos (mul_pos hc hc) hLog)
  have hTerm : (1 : ℝ) ≤
      ∑ i ∈ Finset.Ico 1 (b + 1), ((2 * b).choose (b + i) : ℝ) := by
    have hMem : b ∈ Finset.Ico 1 (b + 1) := Finset.mem_Ico.mpr ⟨hb, Nat.lt_succ_self _⟩
    have hBound := Finset.single_le_sum
      (f := fun i : ℕ => ((2 * b).choose (b + i) : ℝ))
      (fun i _ => Nat.cast_nonneg ((2 * b).choose (b + i))) hMem
    rwa [← two_mul, Nat.choose_self, Nat.cast_one] at hBound
  have hCoeff : 0 < reciprocalCoefficient condition precision j₀ := by
    have hPos : 0 < ∑ i ∈ Finset.Ico 1 (b + 1), ((2 * b).choose (b + i) : ℝ) :=
      zero_lt_one.trans_le hTerm
    change 0 < 4 * (-1 : ℝ) ^ 0 *
      (∑ i ∈ Finset.Ico 1 (b + 1), ((2 * b).choose (b + i) : ℝ)) / (2 : ℝ) ^ (2 * b)
    simp only [pow_zero, mul_one]
    positivity
  have hLowest : 0 < ‖(reciprocalCoefficient condition precision j₀ : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCoeff]
    exact hCoeff
  exact hLowest.trans_le (Finset.single_le_sum
    (f := fun j => ‖(reciprocalCoefficient condition precision j : ℂ)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j₀))

variable {M N : Type*} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]

/-- The selected unitary on the walk register for each term of the reciprocal. -/
def reciprocalWalkPower (condition precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (j : ReciprocalTerm condition precision) : Matrix M M ℂ :=
  walk C U ^ (2 * (j : ℕ) + 1)

/-- The actual coefficient preparation, controlled walk power, and inverse preparation. -/
def reciprocalUnitary (condition precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ) :
    Matrix (ReciprocalTerm condition precision × M) (ReciprocalTerm condition precision × M) ℂ :=
  coefficientLCUUnitary (fun j => (reciprocalCoefficient condition precision j : ℂ))
    (reciprocalWalkPower condition precision C U) 0

/-- The coefficient-selected reciprocal circuit is unitary for a column isometry, a Hermitian
involution, and positive total coefficient mass. -/
theorem reciprocal_unitary_mem (condition precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU : Uᴴ = U) (hU2 : U * U = 1)
    (hMass : 0 < reciprocalMass condition precision) :
    reciprocalUnitary condition precision C U ∈
      Matrix.unitaryGroup (ReciprocalTerm condition precision × M) ℂ := by
  have hWalk : walk C U ∈ Matrix.unitaryGroup M ℂ :=
    Matrix.mem_unitaryGroup_iff'.2 (walk_unitary C U hC hU hU2)
  exact coefficientLCUUnitary_unitary _ _ _ hMass
    (fun j => (Matrix.unitaryGroup M ℂ).pow_mem hWalk (2 * (j : ℕ) + 1))

/-- The clean coefficient ancilla and the isometry range select the normalized Chebyshev
reciprocal block. This identity holds before amplification. -/
theorem reciprocal_clean_block (condition precision : ℝ) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU2 : U * U = 1)
    (hMass : 0 < reciprocalMass condition precision) :
    Cᴴ * compress (prepareLift (Ket (0 : ReciprocalTerm condition precision)))
      (reciprocalUnitary condition precision C U)
      (prepareLift (Ket (0 : ReciprocalTerm condition precision))) * C =
        ∑ j : ReciprocalTerm condition precision,
          ((reciprocalCoefficient condition precision j : ℂ) /
            (reciprocalMass condition precision : ℂ)) •
          Polynomial.aeval (signal C U) (Polynomial.Chebyshev.T ℂ ((2 * (j : ℕ) + 1 : ℕ) : ℤ)) := by
  unfold reciprocalUnitary
  rw [coefficientLCUUnitary_compress _ _ _ hMass, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul, Matrix.smul_mul, reciprocalWalkPower, compressed_chebyshev C U hC hU2]
  rfl

/-- Place the linearized stencil in the off-diagonal block of its Hermitian lift after dividing
it by the scale chosen for the solver. -/
def stencilSignal {depth : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale : ℝ) :
    Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ :=
  lift (((scale⁻¹ : ℝ) • stencilMatrix geometry coefficients).map Complex.ofReal)

open Qatlib.Concepts.WalkSearch.Spectral (aeval_eq_spectralDiagonal_of_action
  spectralDiagonal spectralDiagonal_error_le)
open scoped Matrix.Norms.L2Operator

/-- The complex extension of the unnormalized reciprocal has the same coefficients and terms as
the walk operation. -/
theorem reciprocal_map_eq_sum (condition precision : ℝ) :
    (nearOptimalReciprocalPolynomial condition precision).map Complex.ofRealHom =
      ∑ j : ReciprocalTerm condition precision,
        Polynomial.C (reciprocalCoefficient condition precision j : ℂ) *
          Polynomial.Chebyshev.T ℂ ((2 * (j : ℕ) + 1 : ℕ) : ℤ) := by
  rw [nearOptimalReciprocalPolynomial, ← Fin.sum_univ_eq_sum_range]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.Chebyshev.map_T]
  rfl

/-- Given a real diagonalization with a signed spectral gap, the clean CKS block multiplied by
its coefficient mass has operator-norm error at most twice the requested precision relative to
the diagonal inverse. This concerns the fixed-length circuit before success amplification. -/
theorem reciprocal_clean_block_error {J : Type*} [Fintype J] [DecidableEq J]
    (condition precision : ℝ) (hCondition : 1 < condition) (hPrecision : 0 < precision)
    (hHalf : precision ≤ 1 / 2) (C : Matrix M N ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU2 : U * U = 1)
    (basis : OrthonormalBasis J ℂ (EuclideanSpace ℂ N)) (eigenvalue : J → ℝ)
    (hEigen : ∀ j, (signal C U).toEuclideanLin (basis j) = (eigenvalue j : ℂ) • basis j)
    (hGap : ∀ j, |eigenvalue j| ∈ Set.Icc condition⁻¹ 1) :
    ‖(reciprocalMass condition precision : ℂ) •
        (Cᴴ * compress (prepareLift (Ket (0 : ReciprocalTerm condition precision)))
          (reciprocalUnitary condition precision C U)
          (prepareLift (Ket (0 : ReciprocalTerm condition precision))) * C) -
        spectralDiagonal basis (fun j => (eigenvalue j : ℂ)⁻¹)‖ ≤ 2 * precision := by
  let α := reciprocalMass condition precision
  let p := (nearOptimalReciprocalPolynomial condition precision).map Complex.ofRealHom
  have hMass : 0 < α := reciprocal_mass_pos condition precision hCondition hPrecision hHalf
  have hMassComplex : (α : ℂ) ≠ 0 := by exact_mod_cast hMass.ne'
  have hPoly : (α : ℂ) •
      (Cᴴ * compress (prepareLift (Ket (0 : ReciprocalTerm condition precision)))
        (reciprocalUnitary condition precision C U)
        (prepareLift (Ket (0 : ReciprocalTerm condition precision))) * C) =
      Polynomial.aeval (signal C U) p := by
    rw [reciprocal_clean_block condition precision C U hC hU2 hMass, Finset.smul_sum]
    unfold p
    rw [reciprocal_map_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, map_mul, Polynomial.aeval_C]
    have hCoefficient : (α : ℂ) * ((reciprocalCoefficient condition precision j : ℂ) / α) =
        (reciprocalCoefficient condition precision j : ℂ) := by
      rw [mul_comm, div_mul_cancel₀ _ hMassComplex]
    rw [hCoefficient, Algebra.smul_def]
  rw [hPoly, aeval_eq_spectralDiagonal_of_action basis _ _ hEigen]
  apply spectralDiagonal_error_le basis _ _ (mul_nonneg zero_le_two hPrecision.le)
  intro j
  change ‖p.eval (Complex.ofRealHom (eigenvalue j)) - (eigenvalue j : ℂ)⁻¹‖ ≤ 2 * precision
  unfold p
  rw [Polynomial.eval_map_apply, ← Complex.ofReal_inv]
  change ‖(↑((nearOptimalReciprocalPolynomial condition precision).eval (eigenvalue j)) : ℂ) -
    (↑((eigenvalue j)⁻¹) : ℂ)‖ ≤ 2 * precision
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact lemma14_chebyshev_reciprocal condition precision hCondition hPrecision hHalf _
    (hGap j)

/-- For a signal encoding the lifted stencil, postselection implements the normalized Chebyshev
reciprocal in that stencil signal. The oracle implementation is supplied by the hypothesis. -/
theorem stencil_reciprocal_clean_block {depth : ℕ} (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (scale condition precision : ℝ)
    (C : Matrix M (Address depth ⊕ Address depth) ℂ) (U : Matrix M M ℂ)
    (hC : Cᴴ * C = 1) (hU2 : U * U = 1)
    (hSignal : signal C U = stencilSignal geometry coefficients scale)
    (hMass : 0 < reciprocalMass condition precision) :
    Cᴴ * compress (prepareLift (Ket (0 : ReciprocalTerm condition precision)))
      (reciprocalUnitary condition precision C U)
      (prepareLift (Ket (0 : ReciprocalTerm condition precision))) * C =
        ∑ j : ReciprocalTerm condition precision,
          ((reciprocalCoefficient condition precision j : ℂ) /
            (reciprocalMass condition precision : ℂ)) •
          Polynomial.aeval (stencilSignal geometry coefficients scale)
            (Polynomial.Chebyshev.T ℂ ((2 * (j : ℕ) + 1 : ℕ) : ℤ)) := by
  rw [reciprocal_clean_block condition precision C U hC hU2 hMass, hSignal]

/-- The unscaled Hermitian lift sends a solution in the right block to its right-hand side in the
left block. This lets the stencil remain nonsymmetric. -/
theorem lift_solution_mulVec {I : Type*} [Fintype I] (A : Matrix I I ℂ) (x b : I → ℂ)
    (h : A *ᵥ x = b) :
    lift A *ᵥ Sum.elim 0 x = Sum.elim b 0 := by
  rw [lift, Matrix.fromBlocks_mulVec]
  change Sum.elim ((0 : Matrix I I ℂ) *ᵥ (0 : I → ℂ) + A *ᵥ x)
    (Aᴴ *ᵥ (0 : I → ℂ) + (0 : Matrix I I ℂ) *ᵥ x) = Sum.elim b 0
  simp [h]

/-- Recover the QFVM solution scale from the estimated magnitude of the pre-amplification
success branch, the residual norm, and the normalizations of the matrix and the LCU. -/
def solutionScale (residualNorm coefficientMass matrixScale successAmplitude : ℝ) : ℝ :=
  residualNorm * coefficientMass / matrixScale * successAmplitude

/-- Even when the success amplitude is estimated exactly, the approximate inverse can
perturb the recovered norm. The two amplitude errors add before conversion to physical scale. -/
theorem solution_scale_error (residualNorm mass scale amplitude estimate ideal rawError readError : ℝ)
    (hFactor : 0 ≤ residualNorm * mass / scale)
    (hRaw : |amplitude - ideal| ≤ rawError) (hRead : |estimate - amplitude| ≤ readError) :
    |solutionScale residualNorm mass scale estimate - solutionScale residualNorm mass scale ideal| ≤
      residualNorm * mass / scale * (readError + rawError) := by
  unfold solutionScale
  rw [← mul_sub, abs_mul, abs_of_nonneg hFactor]
  apply mul_le_mul_of_nonneg_left _ hFactor
  calc
    |estimate - ideal| = |(estimate - amplitude) + (amplitude - ideal)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hRead hRaw)

end Qatlib.Papers.QFVMChen22.TimeStep
