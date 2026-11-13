/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.QubitPhysics.GroundBounds
import Qatlib.Papers.RydbergMaxCut26.MomentSdp.GramFactor

/-!
# Density-matrix moment Gram representations

`moment` records the traces of operator products against a matrix, and `realMoment` takes their
real parts. For a positive semidefinite matrix, multiplication by its Hermitian square root
gives the explicit Gram factors `complexRows` and `realRows`, proving positivity; unitary
operators and trace normalization yield unit diagonal entries.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `moment_gram` and `realMoment_gram`: construct complex and real Gram representations.
* `realMoment_posSemidef`: proves positivity of the real moment matrix.
* `realMoment_relation`: transfers real-scaled operator relations to moment entries.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment

/-- The complex moment matrix with entry `trace ((P a)ᴴ * P b * ρ)`. -/
noncomputable def moment {I A : Type*} [Fintype I] (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) :
    Matrix A A ℂ := fun a b => ((P a)ᴴ*P b*ρ).trace

/-- The entrywise real part of the complex moment matrix `moment P ρ`. -/
noncomputable def realMoment {I A : Type*} [Fintype I] (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) :
    Matrix A A ℝ := fun a b => (moment P ρ a b).re

/-- The Hermitian square root of the positive semidefinite matrix `ρ`. -/
noncomputable def root {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    Matrix I I ℂ := (HermitianMat.sqrt (⟨ρ,hρ.isHermitian⟩ : HermitianMat I ℂ)).mat

/-- The matrix `root ρ hρ` equals its conjugate transpose. -/
theorem root_hermitian {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    (root ρ hρ)ᴴ=root ρ hρ :=
  (HermitianMat.sqrt (⟨ρ,hρ.isHermitian⟩ : HermitianMat I ℂ)).H

/-- The square of `root ρ hρ` equals `ρ`. -/
theorem root_square {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    root ρ hρ*root ρ hρ=ρ := HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hρ)

/-- The matrix whose column indexed by `a` consists of the entries of `P a * root ρ hρ`. -/
noncomputable def complexRows {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : Matrix (I×I) A ℂ :=
  fun ij a => (P a*root ρ hρ) ij.1 ij.2

/-- The Hilbert–Schmidt inner product of `A * root ρ hρ` and `B * root ρ hρ` equals `trace (Aᴴ *
B * ρ)`. -/
theorem root_trace {I : Type*} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef)
    (A B : Matrix I I ℂ) : ((A*root ρ hρ)ᴴ*(B*root ρ hρ)).trace = (Aᴴ*B*ρ).trace := by
  rw [Matrix.conjTranspose_mul,root_hermitian]
  have he : root ρ hρ*Aᴴ*(B*root ρ hρ) = root ρ hρ*(Aᴴ*B)*root ρ hρ := by noncomm_ring
  rw [he,Matrix.trace_mul_cycle,Matrix.trace_mul_comm,root_square]

/-- For positive semidefinite `ρ`, the complex moment matrix is the Gram matrix of `complexRows
P ρ hρ`. -/
theorem moment_gram {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    moment P ρ=(complexRows P ρ hρ)ᴴ*complexRows P ρ hρ := by
  ext a b
  rw [moment,← root_trace ρ hρ (P a) (P b)]
  simp only [Matrix.trace,Matrix.mul_apply,Matrix.conjTranspose_apply,complexRows,Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The complex moment matrix of any finite operator family against a positive semidefinite
matrix is positive semidefinite. -/
theorem moment_posSemidef {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : (moment P ρ).PosSemidef := by
  rw [moment_gram P ρ hρ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The real Gram-factor matrix obtained by separating the real and imaginary parts of
`complexRows` into two row coordinates. -/
noncomputable def realRows {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : Matrix ((I×I)×Fin 2) A ℝ :=
  fun c a => if c.2=0 then (complexRows P ρ hρ c.1 a).re else (complexRows P ρ hρ c.1 a).im

/-- For positive semidefinite `ρ`, the real moment matrix equals the transpose-product Gram
matrix of `realRows P ρ hρ`. -/
theorem realMoment_gram {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    realMoment P ρ=(realRows P ρ hρ).transpose*realRows P ρ hρ := by
  ext a b
  simp only [realMoment,moment_gram P ρ hρ,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply,
    realRows,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp [Complex.mul_re,Finset.sum_add_distrib]

/-- The real moment matrix of a finite operator family against a positive semidefinite matrix is
positive semidefinite, as required by the moment relaxation in [CrostaSaubanereHuber2026]. -/
theorem realMoment_posSemidef {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) : (realMoment P ρ).PosSemidef := by
  rw [realMoment_gram P ρ hρ]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- If each `P a` satisfies `(P a)ᴴ * P a = 1` and `ρ` has trace one, every complex moment
diagonal entry is one. -/
theorem moment_diag {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (hP : ∀ a,(P a)ᴴ*P a=1) (ρ : Matrix I I ℂ) (htr : ρ.trace=1) (a : A) :
    moment P ρ a a=1 := by simp only [moment,hP,Matrix.one_mul,htr]

/-- If each `P a` satisfies `(P a)ᴴ * P a = 1` and `ρ` has trace one, every real moment diagonal
entry is one. -/
theorem realMoment_diag {I A : Type*} [Fintype I] [DecidableEq I]
    (P : A → Matrix I I ℂ) (hP : ∀ a,(P a)ᴴ*P a=1) (ρ : Matrix I I ℂ) (htr : ρ.trace=1) (a : A) :
    realMoment P ρ a a=1 := by simp only [realMoment,moment_diag P hP ρ htr,Complex.one_re]

/-- A real scalar relation between the operator products `(P a)ᴴ * P b` and `(P c)ᴴ * P d`
induces the same relation between their real moment entries. This implements moment
constraints used in [CrostaSaubanereHuber2026]. -/
theorem realMoment_relation {I A : Type*} [Fintype I]
    (P : A → Matrix I I ℂ) (ρ : Matrix I I ℂ) (a b c d : A) (s : ℝ)
    (hrel : (P a)ᴴ*P b=s • ((P c)ᴴ*P d)) :
    realMoment P ρ a b=s*realMoment P ρ c d := by
  simp [realMoment,moment,hrel,Matrix.trace_smul]
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment
