/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Uniform label swap and single-cell compression

This module constructs the self-adjoint unitary `uniformSwap` on the basis `Option L`,
exchanging the empty state and the uniform label state. Its labelled columns form the isometric
compression matrix `compression`.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `uniformSwap_squared`: The uniform swap is an involution.
* `uniformSwap_unitary`: The uniform swap is unitary.
* `compression_isometry`: The labelled columns define an isometric embedding.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L] [Nonempty L]

/-- The reciprocal square root of the finite label cardinality, used as the uniform label
amplitude. -/
def coefficient (L : Type*) [Fintype L] : ℝ := 1/Real.sqrt (Fintype.card L)

/-- For a nonempty label type, its cardinality times the squared uniform coefficient equals one. -/
theorem coefficient_normalized : (Fintype.card L : ℝ)*coefficient L^2=1 := by
  have hp : (0 : ℝ)<Fintype.card L := by exact_mod_cast Fintype.card_pos
  simp only [coefficient,div_pow,one_pow,Real.sq_sqrt hp.le]
  exact mul_div_cancel₀ _ hp.ne'

/-- The complex version of the identity that label cardinality times the squared uniform
coefficient equals one. -/
theorem coefficient_complex : (Fintype.card L : ℂ)*(coefficient L : ℂ)^2=1 := by
  exact_mod_cast coefficient_normalized (L := L)

/-- The vector equal to one on the empty state and to the negative uniform coefficient on every
labelled state. -/
def swapVector : Option L → ℂ
  | none => 1
  | some _ => -(coefficient L : ℂ)
omit [Nonempty L] in

/-- The swap vector is fixed by pointwise complex conjugation. -/
theorem swapVector_star : star (swapVector (L := L))=swapVector (L := L) := by
  funext i
  cases i with
  | none => exact star_one _
  | some y =>
    change star (-(coefficient L : ℂ))=-(coefficient L : ℂ)
    rw [star_neg]
    exact congrArg Neg.neg (Complex.conj_ofReal (coefficient L))

/-- The Hermitian squared norm of the swap vector is two for a nonempty label type. -/
theorem swapVector_dot : star (swapVector (L := L)) ⬝ᵥ swapVector (L := L)=2 := by
  rw [swapVector_star]
  have h := coefficient_complex (L := L)
  simp only [dotProduct,Fintype.sum_option,swapVector,mul_one,neg_mul_neg,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← pow_two,h]
  norm_num

/-- The identity minus the outer product of the swap vector with its conjugate, exchanging the
empty state with the uniform label state for nonempty `L`. -/
def uniformSwap : Matrix (Option L) (Option L) ℂ :=
  1-vecMulVec swapVector (star swapVector)

/-- The rank-one outer product of the swap vector with its pointwise conjugate. -/
def swapOuter : Matrix (Option L) (Option L) ℂ :=
    vecMulVec (swapVector (L := L)) (star (swapVector (L := L)))

/-- The square of the swap vector outer product equals twice that outer product. -/
theorem swap_rank_one_squared :
    swapOuter (L := L)*swapOuter (L := L)=swapOuter (L := L)+swapOuter (L := L) := by
  unfold swapOuter
  rw [Matrix.vecMulVec_mul_vecMulVec,swapVector_dot]
  ext i j
  simp only [Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,Matrix.add_apply]
  ring
omit [Nonempty L] in

/-- The uniform swap matrix is self-adjoint. -/
theorem uniformSwap_adjoint : (uniformSwap (L := L))ᴴ=uniformSwap (L := L) := by
  rw [uniformSwap,Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,mul_comm]

/-- For a nonempty label type, the uniform swap matrix squares to the identity. -/
theorem uniformSwap_squared : uniformSwap (L := L)*uniformSwap (L := L)=1 := by
  have hR := swap_rank_one_squared (L := L)
  change (1-swapOuter)*(1-swapOuter)=1
  calc
    _ = 1-swapOuter-swapOuter+swapOuter*swapOuter := by noncomm_ring
    _ = 1 := by rw [hR];abel

/-- For a nonempty label type, the conjugate transpose of the uniform swap multiplied by the
swap is the identity. -/
theorem uniformSwap_unitary : (uniformSwap (L := L))ᴴ*uniformSwap (L := L)=1 := by
  rw [uniformSwap_adjoint,uniformSwap_squared]

/-- The rectangular matrix consisting of the labelled columns of the uniform swap. -/
def compression : Matrix (Option L) L ℂ := fun i y => uniformSwap i (some y)

/-- The compression matrix has orthonormal columns for a nonempty label type. -/
theorem compression_isometry : (compression (L := L))ᴴ*compression (L := L)=1 := by
  ext x y
  have h :=
      congrArg (fun M : Matrix (Option L) (Option L) ℂ => M (some x) (some y))
      (uniformSwap_unitary (L := L))
  change (∑ z : Option L, star (uniformSwap z (some x))*uniformSwap z (some y))=_ at h
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,compression,Matrix.one_apply,Option.some.injEq] using h
end Qatlib.Concepts.CompressedQuery.CyclicRecord
