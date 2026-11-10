/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.AffineTransform

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

abbrev atrans {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (w : BVec n) : BVec n :=
  (Aᵀ)⁻¹.mulVec w

lemma dot_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (x y : BVec n) :
    dot (A.mulVec x) y = dot x (Aᵀ.mulVec y) := by
  calc dot (A.mulVec x) y = dot y (A.mulVec x) := dotProduct_comm _ _
    _ = dot x (Aᵀ.mulVec y) := (Matrix.dotProduct_transpose_mulVec A x y).symm

lemma nonsing_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (hA : IsUnit A.det) (x : BVec n) :
    (A⁻¹).mulVec (A.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

lemma affine_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : BVec n) (hA : IsUnit A.det) :
    Function.Injective (fun x : BVec n => A.mulVec x + b) := by
  intro x1 x2 h
  have h' : A.mulVec x1 = A.mulVec x2 := add_right_cancel h
  calc x1 = (A⁻¹).mulVec (A.mulVec x1) := (nonsing_inv_mulVec A hA x1).symm
    _ = (A⁻¹).mulVec (A.mulVec x2) := by rw [h']
    _ = x2 := nonsing_inv_mulVec A hA x2

lemma affine_bijective {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : BVec n) (hA : IsUnit A.det) :
    Function.Bijective (fun x : BVec n => A.mulVec x + b) :=
  (affine_injective A b hA).bijective_of_finite

theorem lemma2_affine {n : ℕ} (f : BVec n → ZMod 2)
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : IsUnit A.det) (b : BVec n)
    (hf : Bent f) :
    Bent (fun x => f (A.mulVec x + b)) ∧
    (∀ w, walsh (fun x => f (A.mulVec x + b)) w
        = eps (dot (atrans A w) b) * walsh f (atrans A w)) := by

  have hd : ∀ (w y : BVec n),
      dot w ((A⁻¹).mulVec (y - b))
        = dot (atrans A w) y - dot (atrans A w) b := by
    intro w y
    calc dot w ((A⁻¹).mulVec (y - b))
        = dot ((A⁻¹).mulVec (y - b)) w := dotProduct_comm _ _
      _ = dot (y - b) ((A⁻¹)ᵀ.mulVec w) := dot_mulVec (A⁻¹) (y - b) w
      _ = dot (y - b) (atrans A w) := by rw [Matrix.transpose_nonsing_inv]
      _ = dot (atrans A w) (y - b) := dotProduct_comm _ _
      _ = dot (atrans A w) y - dot (atrans A w) b := dotProduct_sub _ _ _
  have hformula : ∀ w, walsh (fun x => f (A.mulVec x + b)) w
        = eps (dot (atrans A w) b) * walsh f (atrans A w) := by
    intro w
    rw [walsh]

    have hreindex : (∑ x, eps (dot w x) * eps (f (A.mulVec x + b)))
        = ∑ y, eps (dot w ((A⁻¹).mulVec (y - b))) * eps (f y) := by
      refine Fintype.sum_bijective (fun x : BVec n => A.mulVec x + b)
        (affine_bijective A b hA) _ _ ?_
      intro x
      have hsub : (A.mulVec x + b) - b = A.mulVec x := by abel
      simp only [hsub, nonsing_inv_mulVec A hA]
    rw [hreindex]
    trans ∑ y, eps (dot (atrans A w) b) * (eps (dot (atrans A w) y) * eps (f y))
    · apply Finset.sum_congr rfl
      intro y _
      rw [hd w y, sub_eq_add_neg, eps_add, eps_neg]
      ring
    · rw [← Finset.mul_sum]
      rfl
  refine ⟨?_, hformula⟩
  intro w
  rw [hformula w, mul_pow, eps_sq, one_mul]
  exact hf (atrans A w)

end Qatlib.Papers.NonlinBool08.MainResults.AffineTransform
