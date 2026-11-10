/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {L : Type*} [Fintype L] [Nonempty L]

def coefficient (L : Type*) [Fintype L] : ℝ := 1/Real.sqrt (Fintype.card L)

theorem coefficient_normalized : (Fintype.card L : ℝ)*coefficient L^2=1 := by
  have hp : (0 : ℝ)<Fintype.card L := by exact_mod_cast Fintype.card_pos
  simp only [coefficient,div_pow,one_pow,Real.sq_sqrt hp.le]
  exact mul_div_cancel₀ _ hp.ne'

theorem coefficient_complex : (Fintype.card L : ℂ)*(coefficient L : ℂ)^2=1 := by
  exact_mod_cast coefficient_normalized (L := L)

def swapVector : Option L → ℂ
  | none => 1
  | some _ => -(coefficient L : ℂ)
omit [Nonempty L] in

theorem swapVector_star : star (swapVector (L := L))=swapVector (L := L) := by
  funext i
  cases i with
  | none => exact star_one _
  | some y =>
    change star (-(coefficient L : ℂ))=-(coefficient L : ℂ)
    rw [star_neg]
    exact congrArg Neg.neg (Complex.conj_ofReal (coefficient L))

theorem swapVector_dot : star (swapVector (L := L)) ⬝ᵥ swapVector (L := L)=2 := by
  rw [swapVector_star]
  have h := coefficient_complex (L := L)
  simp only [dotProduct,Fintype.sum_option,swapVector,mul_one,neg_mul_neg,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← pow_two,h]
  norm_num

def uniformSwap : Matrix (Option L) (Option L) ℂ :=
  1-vecMulVec swapVector (star swapVector)

def swapOuter : Matrix (Option L) (Option L) ℂ :=
    vecMulVec (swapVector (L := L)) (star (swapVector (L := L)))

theorem swap_rank_one_squared :
    swapOuter (L := L)*swapOuter (L := L)=swapOuter (L := L)+swapOuter (L := L) := by
  unfold swapOuter
  rw [Matrix.vecMulVec_mul_vecMulVec,swapVector_dot]
  ext i j
  simp only [Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,Matrix.add_apply]
  ring
omit [Nonempty L] in

theorem uniformSwap_adjoint : (uniformSwap (L := L))ᴴ=uniformSwap (L := L) := by
  rw [uniformSwap,Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply,Matrix.vecMulVec_apply,mul_comm]

theorem uniformSwap_squared : uniformSwap (L := L)*uniformSwap (L := L)=1 := by
  have hR := swap_rank_one_squared (L := L)
  change (1-swapOuter)*(1-swapOuter)=1
  calc
    _ = 1-swapOuter-swapOuter+swapOuter*swapOuter := by noncomm_ring
    _ = 1 := by rw [hR];abel

theorem uniformSwap_unitary : (uniformSwap (L := L))ᴴ*uniformSwap (L := L)=1 := by
  rw [uniformSwap_adjoint,uniformSwap_squared]

def compression : Matrix (Option L) L ℂ := fun i y => uniformSwap i (some y)

theorem compression_isometry : (compression (L := L))ᴴ*compression (L := L)=1 := by
  ext x y
  have h :=
      congrArg (fun M : Matrix (Option L) (Option L) ℂ => M (some x) (some y))
      (uniformSwap_unitary (L := L))
  change (∑ z : Option L, star (uniformSwap z (some x))*uniformSwap z (some y))=_ at h
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,compression,Matrix.one_apply,Option.some.injEq] using h
end Qatlib.Concepts.CompressedQuery.CyclicRecord
