/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram

/-!
# Schur residuals of positive Gram matrices

This module defines `gramSchurVector` from the first row of a complex matrix and proves the
corresponding Schur residual identities. For a positive semidefinite matrix with a strictly
positive first diagonal entry, subtracting its associated rank-one Gram matrix preserves
positive semidefiniteness and makes that diagonal entry zero. The matrix positivity background
is developed in [Bhatia1997].

## Main statements

* `gramSchurVector_outer`: identifies the rank-one term entrywise.
* `gram_schur_residual`: proves positivity and the vanishing first diagonal entry of the
  residual.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical BigOperators ComplexOrder
variable {n : ℕ} [NeZero n]

/-- The first row of `A` divided by the square root of the real part of its first diagonal
entry. -/
def gramSchurVector (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ :=
  fun j => A 0 j/(Real.sqrt (A 0 0).re : ℂ)

/-- Expands the entries of the congruence transform `Sᴴ * A * S`, where `S` subtracts the row
`u` from the first row of the identity matrix. -/
theorem gram_schur_transform_apply (A : Matrix (Fin n) (Fin n) ℂ)
    (u : Fin n → ℂ) (i j : Fin n) :
    let S := (1 : Matrix (Fin n) (Fin n) ℂ)-Matrix.vecMulVec (Pi.single 0 (1 : ℂ)) u
    (S.conjTranspose*A*S) i j=
      A i j-A i 0*u j-star (u i)*A 0 j+star (u i)*A 0 0*u j := by
  (try dsimp only)
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_vecMulVec,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul,Matrix.sub_apply,Matrix.vecMulVec_apply]
  simp [Matrix.mulVec,Matrix.vecMul,dotProduct,Pi.single_apply,mul_ite,ite_mul,
    Matrix.vecMulVec]
  ring

/-- For a positive semidefinite matrix with strictly positive first diagonal entry, the Gram
outer product of `gramSchurVector A` has entries `A i 0 * A 0 j / A 0 0`. -/
theorem gramSchurVector_outer (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (ha : 0<(A 0 0).re) (i j : Fin n) :
    gramOuter (gramSchurVector A) i j=A i 0*A 0 j/(A 0 0) := by
  have hα : A 0 0=((A 0 0).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp (hA.diag_nonneg (i := 0))).2.symm
  have hstar : star (A 0 i)=A i 0 := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.isHermitian i) 0
  have hs : (Real.sqrt (A 0 0).re : ℂ)*(Real.sqrt (A 0 0).re : ℂ)=A 0 0 := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt ha.le,← hα]
  dsimp [gramOuter,gramSchurVector]
  rw [map_div₀,Complex.conj_ofReal]
  change star (A 0 i)/(Real.sqrt (A 0 0).re : ℂ)*(A 0 j/(Real.sqrt (A 0 0).re : ℂ))=_
  rw [hstar,div_mul_div_comm,hs]

/-- Subtracting the Gram outer product of `gramSchurVector A` from a positive semidefinite
matrix with strictly positive first diagonal entry leaves a positive semidefinite matrix
whose first diagonal entry is zero. -/
theorem gram_schur_residual (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (ha : 0<(A 0 0).re) :
    (A-gramOuter (gramSchurVector A)).PosSemidef ∧
      (A-gramOuter (gramSchurVector A)) 0 0=0 := by
  have hα0 : A 0 0≠0 := by intro h; rw [h] at ha; norm_num at ha
  have hα : star (A 0 0)=A 0 0 := by
    simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.isHermitian 0) 0
  let u := fun j : Fin n => A 0 j/(A 0 0)
  let S := (1 : Matrix (Fin n) (Fin n) ℂ)-Matrix.vecMulVec (Pi.single 0 (1 : ℂ)) u
  have he : S.conjTranspose*A*S=A-gramOuter (gramSchurVector A) := by
    ext i j
    rw [gram_schur_transform_apply A u i j]
    simp only [Matrix.sub_apply,gramSchurVector_outer A hA ha]
    dsimp [u]
    have hs : star (A 0 i)=A i 0 := by
      simpa only [Matrix.conjTranspose_apply] using congrFun (congrFun hA.isHermitian i) 0
    rw [map_div₀,show (starRingEnd ℂ) (A 0 i)=A i 0 from hs,
      show (starRingEnd ℂ) (A 0 0)=A 0 0 from hα]
    field_simp
    ring
  refine ⟨he ▸ hA.conjTranspose_mul_mul_same S,?_⟩
  rw [Matrix.sub_apply,gramSchurVector_outer A hA ha]
  field_simp
  ring
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
