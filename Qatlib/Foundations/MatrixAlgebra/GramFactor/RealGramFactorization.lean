/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import QuantumInfo.ForMathlib.HermitianMat.Order

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.GramFactor
open scoped Classical BigOperators Matrix

/-- Every real positive semidefinite matrix has a square real Gram factor. -/
theorem exists_real_gram_factorization (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℝ,B*B.transpose=A := by
  let U : Matrix (Fin n) (Fin n) ℝ := hA.isHermitian.eigenvectorUnitary
  let d := fun i : Fin n => Real.sqrt (hA.isHermitian.eigenvalues i)
  have hstar : U.conjTranspose=U.transpose := by
    ext i j
    simp only [Matrix.conjTranspose_apply,Matrix.transpose_apply,star_trivial]
  have hdiag : Matrix.diagonal d*Matrix.diagonal d=
      Matrix.diagonal (fun i : Fin n => hA.isHermitian.eigenvalues i) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hA.eigenvalues_nonneg i)
  have hspec : A=U*Matrix.diagonal (fun i : Fin n => hA.isHermitian.eigenvalues i)*U.transpose := by
    have h := hA.isHermitian.spectral_theorem
    simpa only [Unitary.conjStarAlgAut_apply,RCLike.ofReal_real_eq_id,Function.comp_def,hstar] using! h
  refine ⟨U*Matrix.diagonal d,?_⟩
  rw [Matrix.transpose_mul,Matrix.diagonal_transpose,Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.diagonal d) (Matrix.diagonal d) U.transpose,hdiag]
  simpa only [Matrix.mul_assoc] using hspec.symm

/-- Every real Gram matrix can be scaled by a positive factor so that its complement to the
identity is another real Gram matrix. -/
theorem exists_scaled_real_gram_complement {r m : ℕ} (W : Matrix (Fin r) (Fin m) ℝ) :
    ∃ (a : ℝ) (R : Matrix (Fin r) (Fin r) ℝ),0<a ∧
      R*R.transpose+(a^2)⁻¹ • (W*W.transpose)=1 := by
  have hstar : W.conjTranspose=W.transpose := by
    ext i j; simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]
  have hS : (W*W.transpose).PosSemidef := by
    rw [← hstar]
    exact Matrix.posSemidef_self_mul_conjTranspose W
  let G : HermitianMat (Fin r) ℝ := ⟨W*W.transpose,hS.isHermitian⟩
  have hG : 0≤G := HermitianMat.zero_le_iff.mpr hS
  let t := G.trace+1
  have ht : 0<t := by have h := HermitianMat.trace_nonneg hG; dsimp [t]; linarith
  let a := Real.sqrt t
  have ha : 0<a := Real.sqrt_pos.mpr ht
  have ha2 : a^2=t := Real.sq_sqrt ht.le
  have hone : (0 : HermitianMat (Fin r) ℝ)≤1 := by
    rw [HermitianMat.zero_le_iff]
    exact Matrix.PosSemidef.one
  have hbound : G≤t • (1 : HermitianMat (Fin r) ℝ) := by
    apply (HermitianMat.le_trace_smul_one hG).trans
    dsimp [t]
    rw [add_smul,one_smul]
    exact le_add_of_nonneg_right hone
  let Q : HermitianMat (Fin r) ℝ := t⁻¹ • (t • 1-G)
  have hQ : 0≤Q := smul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr hbound)
  have hmat : Q.mat=1-(a^2)⁻¹ • (W*W.transpose) := by
    dsimp [Q]
    simp only [HermitianMat.mat_smul,HermitianMat.mat_sub,HermitianMat.mat_one]
    rw [ha2,smul_sub,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
    rfl
  obtain ⟨R,hR⟩ := exists_real_gram_factorization r Q.mat (HermitianMat.zero_le_iff.mp hQ)
  refine ⟨a,R,ha,?_⟩
  rw [hR,hmat]
  abel
end Qatlib.Foundations.MatrixAlgebra.GramFactor
