/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SchattenDiamond.DiamondNorm.DiamondStabilization
public import Mathlib.Data.Matrix.Basis

@[expose] public section


/-! # Hilbert--Schmidt adjoints and amplification

The adjoint is constructed from the actual coefficients of a linear map. The
trace identity survives tensor amplification, as required in Watrous (2012),
arXiv:1207.5726v2, Section 1, equation (1).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Qatlib.Papers.BddNormSDP12.MainResults.TraceAdjoint

open Matrix
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace

/-- The Hilbert--Schmidt pairing is the sum of the entrywise scalar pairings. -/
theorem trace_pair_entries {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) :
    Matrix.trace (Aᴴ * B) = ∑ i, ∑ j, star (A i j) * B i j := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- The Hilbert--Schmidt adjoint formed from the coefficients of a linear map. -/
def hsAdjoint {I J : Type*} [Fintype J] [DecidableEq I]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : Matrix J J ℂ →ₗ[ℂ] Matrix I I ℂ where
  toFun Y i j := ∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * Y a b
  map_add' Y Z := by
    ext i j
    change (∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * (Y a b + Z a b)) =
      (∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * Y a b) +
      ∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * Z a b
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c Y := by
    ext i j
    change (∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * (c * Y a b)) =
      c * ∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * Y a b
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring

/-- Every output coefficient is the linear combination of the matrix-unit outputs. -/
theorem map_entries {I J : Type*} [Fintype I] [DecidableEq I]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (X : Matrix I I ℂ) (a b : J) :
    T X a b = ∑ i, ∑ j, X i j * T (Matrix.single i j 1) a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j 1 by simp]
  simp only [map_smul, Matrix.smul_apply, smul_eq_mul]

/-- The coefficient construction satisfies the Hilbert--Schmidt adjoint identity. -/
theorem hsAdjoint_pair {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    Matrix.trace (Yᴴ * T X) = Matrix.trace ((hsAdjoint T Y)ᴴ * X) := by
  classical
  rw [trace_pair_entries Y (T X), trace_pair_entries (hsAdjoint T Y) X]
  change (∑ a, ∑ b, star (Y a b) * T X a b) =
    ∑ i, ∑ j, star (∑ a, ∑ b, star (T (Matrix.single i j 1) a b) * Y a b) * X i j
  simp only [star_sum, star_mul, star_star, Finset.sum_mul]
  simp_rw [map_entries T X, Finset.mul_sum]
  simpa only [Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_comm (s := (Finset.univ : Finset (J × J)))
      (t := (Finset.univ : Finset (I × I)))
      (f := fun a i => star (Y a.1 a.2) *
        (X i.1 i.2 * T (Matrix.single i.1 i.2 1) a.1 a.2)))

/-- The trace pairing on a product space is the sum of the block pairings. -/
theorem trace_pair_blocks {I R : Type*} [Fintype I] [Fintype R]
    (A B : Matrix (I × R) (I × R) ℂ) :
    Matrix.trace (Aᴴ * B) =
      ∑ s, ∑ t, Matrix.trace
        ((Matrix.of fun i j => A (i, s) (j, t))ᴴ *
          Matrix.of (fun i j => B (i, s) (j, t))) := by
  classical
  simp only [trace_pair_entries, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [show ∀ i : I, (∑ j, ∑ t, star (A (i, s) (j, t)) * B (i, s) (j, t)) =
      ∑ t, ∑ j, star (A (i, s) (j, t)) * B (i, s) (j, t) from
    fun _ => Finset.sum_comm]
  exact Finset.sum_comm

/-- Tensor amplification preserves the Hilbert--Schmidt adjoint identity. -/
theorem tensor_pair {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (Y : Matrix (Fin E × Fin r) (Fin E × Fin r) ℂ) :
    Matrix.trace (Yᴴ * tensorLeft T X) =
      Matrix.trace ((tensorLeft (hsAdjoint T) Y)ᴴ * X) := by
  rw [trace_pair_blocks Y (tensorLeft T X),
    trace_pair_blocks (tensorLeft (hsAdjoint T) Y) X]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  change Matrix.trace ((Matrix.of fun i j => Y (i, s) (j, t))ᴴ *
      T (Matrix.of fun i j => X (i, s) (j, t))) =
    Matrix.trace ((hsAdjoint T (Matrix.of fun i j => Y (i, s) (j, t)))ᴴ *
      Matrix.of (fun i j => X (i, s) (j, t)))
  exact hsAdjoint_pair T
    (Matrix.of fun i j => X (i, s) (j, t)) (Matrix.of fun i j => Y (i, s) (j, t))

/-- Trace pairing is bounded by spectral norm times trace norm. -/
theorem trace_pair_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) :
    ‖Matrix.trace (Aᴴ * B)‖ ≤ ‖A‖ * Matrix.traceNorm B := by
  exact (Matrix.abs_trace_le_traceNorm _).trans
    (by simpa only [Matrix.l2_opNorm_conjTranspose] using
      Matrix.traceNorm_mul_le_opNorm_traceNorm Aᴴ B)

/-- Interchanging the two arguments does not change the norm of the trace pairing. -/
theorem trace_pair_norm_symm {I : Type*} [Fintype I]
    (A B : Matrix I I ℂ) :
    ‖Matrix.trace (Aᴴ * B)‖ = ‖Matrix.trace (Bᴴ * A)‖ := by
  rw [← norm_star (Matrix.trace (Aᴴ * B)), ← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

end Qatlib.Papers.BddNormSDP12.MainResults.TraceAdjoint
