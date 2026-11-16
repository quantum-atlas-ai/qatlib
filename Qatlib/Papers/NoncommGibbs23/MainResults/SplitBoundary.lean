/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommGibbs23.MainResults.Model
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Qatlib.Papers.NoncommGibbs23.MainResults
open Matrix

/-- If an anti-Hermitian matrix and a Hermitian matrix sum to zero, both vanish. -/
theorem split_zero {D : ℕ} (A H : Operator D)
    (hA : Aᴴ = -A) (hH : Hᴴ = H) (hzero : A + H = 0) :
    A = 0 ∧ H = 0 := by
  have hstar := congrArg (fun M : Operator D => Mᴴ) hzero
  rw [Matrix.conjTranspose_add, hA, hH, Matrix.conjTranspose_zero] at hstar
  constructor
  · ext i j
    have h1 := congrFun (congrFun hzero i) j
    have h2 := congrFun (congrFun hstar i) j
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply] at h1 h2 ⊢
    linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2
  · ext i j
    have h1 := congrFun (congrFun hzero i) j
    have h2 := congrFun (congrFun hstar i) j
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply] at h1 h2 ⊢
    linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

/-- The legacy superoperator symmetry laws reduce a zero split on a Hermitian input to zero parts. -/
theorem super_split {D : ℕ} (r : Operator D) (A H : Operator D → Operator D)
    (hr : rᴴ = r) (hA : ∀ X, (A X)ᴴ = -A (Xᴴ))
    (hH : ∀ X, (H X)ᴴ = H (Xᴴ)) (hzero : A r + H r = 0) :
    A r = 0 ∧ H r = 0 := by
  apply split_zero (A r) (H r) _ _ hzero
  · simpa only [hr] using hA r
  · simpa only [hr] using hH r

end Qatlib.Papers.NoncommGibbs23.MainResults
