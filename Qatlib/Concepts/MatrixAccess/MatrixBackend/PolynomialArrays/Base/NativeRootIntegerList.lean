/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerConvolution
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Reuse List.toFinsupp to interpret dynamic ascending coefficient arrays.
Deleting zero tails preserves this polynomial, including the empty zero case.
No trace of Python execution is postulated or certified by these lemmas. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial

/-- The existing ascending-list finitely supported representation, cast once. -/
def rootIntegerListPolynomial (a : List ℤ) : ℂ[X] :=
  (⟨⟨a.toFinsupp⟩⟩ : ℤ[X]).map (Int.castRingHom ℂ)

/-- The coefficient at index `k` is the `k`th list entry cast to ℂ, with zero for an out-of-range index. -/
theorem rootIntegerListPolynomial_coeff (a : List ℤ) (k : ℕ) :
    (rootIntegerListPolynomial a).coeff k=(a.getD k 0 : ℂ) := by
  rw [rootIntegerListPolynomial,Polynomial.coeff_map]
  change (a.toFinsupp k : ℂ)=(a.getD k 0 : ℂ)
  rw [List.toFinsupp_apply]

/-- Listing the entries of the finite integer array in index order gives the same complex polynomial as interpreting the array directly. -/
theorem rootIntegerListPolynomial_ofFn {d : ℕ} (a : Fin (d+1) → ℤ) :
    rootIntegerListPolynomial (List.ofFn a)=rootIntegerPolynomial a := by
  apply Polynomial.ext
  intro k
  rw [rootIntegerListPolynomial_coeff,rootIntegerPolynomial_coeff]
  by_cases hk : k<d+1
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left hk,Option.getD_some]
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right hk,Option.getD_none,Int.cast_zero]

/-- The empty integer coefficient list represents the zero complex polynomial. -/
theorem rootIntegerListPolynomial_nil : rootIntegerListPolynomial []=0 := by
  apply Polynomial.ext
  intro k
  simp [rootIntegerListPolynomial_coeff]

/-- Appending one zero to the high-degree end of an integer coefficient list preserves its complex polynomial. -/
theorem rootIntegerListPolynomial_pop_zero (a : List ℤ) :
    rootIntegerListPolynomial (a++[0])=rootIntegerListPolynomial a := by
  apply Polynomial.ext
  intro k
  simp only [rootIntegerListPolynomial_coeff]
  rw [←List.toFinsupp_apply, ←List.toFinsupp_apply,
    List.toFinsupp_concat_eq_toFinsupp_add_single]
  simp

/-- A finite trace of exactly the zero-tail deletion used by canonical.
There is no requirement that deletion is maximal, nor a source-run claim. -/
inductive RootZeroTailDeletion : List ℤ → List ℤ → Prop where
  | refl (a : List ℤ) : RootZeroTailDeletion a a
  | pop (a b : List ℤ) (h : RootZeroTailDeletion a b) :
      RootZeroTailDeletion (a++[0]) b

/-- If `b` is obtained from `a` by any finite sequence of trailing-zero deletions, the two lists represent the same complex polynomial. -/
theorem rootIntegerListPolynomial_zero_tail_trace {a b : List ℤ}
    (h : RootZeroTailDeletion a b) :
    rootIntegerListPolynomial a=rootIntegerListPolynomial b := by
  induction h with
  | refl _ => rfl
  | pop a _ _ ih => exact (rootIntegerListPolynomial_pop_zero a).trans ih

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
