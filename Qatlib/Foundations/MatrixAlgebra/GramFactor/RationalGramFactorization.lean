/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.GramFactor
open scoped Classical BigOperators Matrix

/-- Every nonnegative rational number is a sum of four rational squares. -/
theorem exists_rational_four_squares (d : ℚ) (hd : 0≤d) :
    ∃ s : Fin 4 → ℚ,∑ i : Fin 4,(s i)^2=d := by
  have hnum : 0≤d.num := Rat.num_nonneg.mpr hd
  have hnumQ : (d.num.toNat : ℚ)=(d.num : ℚ) := by exact_mod_cast Int.toNat_of_nonneg hnum
  have hden : (d.den : ℚ)≠0 := by exact_mod_cast d.den_ne_zero
  obtain ⟨a,b,c,e,he⟩ := Nat.sum_four_squares (d.num.toNat*d.den)
  have heQ : (a : ℚ)^2+(b : ℚ)^2+(c : ℚ)^2+(e : ℚ)^2=(d.num.toNat : ℚ)*(d.den : ℚ) := by
    exact_mod_cast he
  let s : Fin 4 → ℚ := ![(a : ℚ)/d.den,(b : ℚ)/d.den,(c : ℚ)/d.den,(e : ℚ)/d.den]
  refine ⟨s,?_⟩
  calc
    _ = ((a : ℚ)^2+(b : ℚ)^2+(c : ℚ)^2+(e : ℚ)^2)/(d.den : ℚ)^2 := by
      simp [s,Fin.sum_univ_succ]
      ring
    _ = ((d.num : ℚ)*(d.den : ℚ))/(d.den : ℚ)^2 := by rw [heQ,hnumQ]
    _ = (d.num : ℚ)/(d.den : ℚ) := by field_simp
    _ = d := Rat.num_div_den d

/-- A rational matrix whose real image is positive semidefinite has a nonnegative quadratic form
on rational vectors. -/
theorem rational_quadratic_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ)
    (hH : (H.map (algebraMap ℚ ℝ)).PosSemidef) (x : Fin n → ℚ) :
    0≤H.toQuadraticForm' x := by
  change 0≤((Matrix.toLinearMap₂' ℚ) H x) x
  rw [Matrix.toLinearMap₂'_apply']
  have h := hH.dotProduct_mulVec_nonneg (fun i => (x i : ℝ))
  have hcast : (0 : ℝ)≤((x ⬝ᵥ (H*ᵥx) : ℚ) : ℝ) := by
    simpa [dotProduct,Matrix.mulVec,Matrix.map_apply,Rat.cast_sum,Rat.cast_mul] using h
  exact_mod_cast hcast

/-- The bilinear map associated with a symmetric rational matrix is invariant under swapping its
arguments. -/
theorem rational_bilinear_flip {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hH : H.IsSymm) :
    ((Matrix.toLinearMap₂' ℚ (S₁ := ℚ) (S₂ := ℚ)) H).flip=(Matrix.toLinearMap₂' ℚ (S₁ := ℚ) (S₂ := ℚ)) H := by
  apply LinearMap.ext₂
  intro x y
  rw [LinearMap.flip_apply,Matrix.toLinearMap₂'_apply',Matrix.toLinearMap₂'_apply']
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hH,dotProduct_comm]

/-- Symmetric rational matrices are equal if their quadratic forms agree on every rational
vector. -/
theorem rational_matrix_eq_of_quadratic_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ)
    (hA : A.IsSymm) (hB : B.IsSymm)
    (h : ∀ x : Fin n → ℚ,A.toQuadraticForm' x=B.toQuadraticForm' x) : A=B := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hq : A.toQuadraticForm'=B.toQuadraticForm' := by ext x; exact h x
  have he := congrArg (QuadraticMap.associatedHom ℚ) hq
  dsimp only [Matrix.toQuadraticForm'] at he
  rw [QuadraticMap.associated_left_inverse' ℚ (rational_bilinear_flip A hA),
    QuadraticMap.associated_left_inverse' ℚ (rational_bilinear_flip B hB)] at he
  exact (Matrix.toLinearMap₂' ℚ).injective he

/-- A nonnegatively weighted sum of rational squares after a linear map admits a rational Gram
representation. -/
theorem rational_weighted_form_gram {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → ℚ) (hw : ∀ i,0≤w i) (f : (Fin n → ℚ) →ₗ[ℚ] (I → ℚ)) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) ℚ),∀ x : Fin n → ℚ,
      (B*B.transpose).toQuadraticForm' x=(QuadraticMap.weightedSumSquares ℚ w) (f x) := by
  have hs : ∀ i : I,∃ s : Fin 4 → ℚ,∑ k : Fin 4,(s k)^2=w i :=
    fun i => exists_rational_four_squares (w i) (hw i)
  choose s hs using hs
  let m := Fintype.card (I × Fin 4)
  let E : Fin m ≃ I × Fin 4 := (Fintype.equivFin (I × Fin 4)).symm
  let B : Matrix (Fin n) (Fin m) ℚ := fun i j => s (E j).1 (E j).2*f.toMatrix' (E j).1 i
  have hfx (x : Fin n → ℚ) : f.toMatrix'*ᵥx=f x := by
    rw [← Matrix.toLin'_apply,Matrix.toLin'_toMatrix']
  have hcol (x : Fin n → ℚ) (j : Fin m) : (B.transpose*ᵥx) j=s (E j).1 (E j).2*(f x (E j).1) := by
    change (∑ i : Fin n,(s (E j).1 (E j).2*f.toMatrix' (E j).1 i)*x i)=_
    simp only [mul_assoc,← Finset.mul_sum]
    exact congrArg (fun y : I → ℚ => s (E j).1 (E j).2*y (E j).1) (hfx x)
  refine ⟨m,B,?_⟩
  intro x
  change ((Matrix.toLinearMap₂' ℚ) (B*B.transpose) x) x=_
  rw [Matrix.toLinearMap₂'_apply',← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose]
  simp only [dotProduct]
  simp_rw [hcol,← pow_two]
  calc
    _ = ∑ j : I × Fin 4,(s j.1 j.2)^2*(f x j.1)^2 := by
      rw [← Equiv.sum_comp E (fun j : I × Fin 4 => (s j.1 j.2)^2*(f x j.1)^2)]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i : I,(∑ k : Fin 4,(s i k)^2)*(f x i)^2 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ i : I,w i*(f x i)^2 := by simp_rw [hs]
    _ = _ := by simp only [QuadraticMap.weightedSumSquares_apply,smul_eq_mul,pow_two]

/-- A symmetric rational matrix that is positive semidefinite over the reals admits a rational
Gram factorization. -/
theorem exists_rational_gram_factorization (n : ℕ) (H : Matrix (Fin n) (Fin n) ℚ)
    (hSym : H.IsSymm) (hPSD : (H.map (algebraMap ℚ ℝ)).PosSemidef) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) ℚ),B*B.transpose=H := by
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  let Q := H.toQuadraticForm'
  obtain ⟨w,⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  have hw (i : Fin (Module.finrank ℚ (Fin n → ℚ))) : 0≤w i := by
    have h := rational_quadratic_nonneg H hPSD (e.symm (Pi.single i 1))
    have he := e.map_app (e.symm (Pi.single i 1))
    rw [e.apply_symm_apply] at he
    rw [← he] at h
    simpa only [QuadraticMap.weightedSumSquares_apply,smul_eq_mul,Pi.single_apply,
      mul_ite,ite_mul,zero_mul,mul_zero,one_mul,mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using h
  obtain ⟨m,B,hB⟩ := rational_weighted_form_gram w hw e.toLinearEquiv.toLinearMap
  refine ⟨m,B,?_⟩
  apply rational_matrix_eq_of_quadratic_eq (B*B.transpose) H
  · change (B*B.transpose).transpose=B*B.transpose
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  · exact hSym
  · intro x
    exact (hB x).trans (e.map_app x)
end Qatlib.Foundations.MatrixAlgebra.GramFactor
