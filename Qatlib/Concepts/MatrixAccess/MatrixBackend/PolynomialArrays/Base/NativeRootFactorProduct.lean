/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootCanonicalMultiply

set_option backward.isDefEq.respectTransparency false

/-! Actual ordered repeated-factor multiplication and its integer-list equality
guard, transported to the same original target polynomial. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial

/-- The exponent loop repeats the same normalized integer-list multiplication. -/
def rootIntegerListRepeatMultiply (factor : List ℤ) : ℕ → List ℤ → List ℤ
  | 0,acc => acc
  | n+1,acc => rootIntegerListRepeatMultiply factor n (rootIntegerListMultiply acc factor)

/-- The finite construction in `NativeRootFactorProduct` satisfies `rootIntegerListRepeatMultiply_polynomial` under the displayed hypotheses. -/
theorem rootIntegerListRepeatMultiply_polynomial (factor : List ℤ) (n : ℕ) (acc : List ℤ) :
    rootIntegerListPolynomial (rootIntegerListRepeatMultiply factor n acc)=
      rootIntegerListPolynomial acc*(rootIntegerListPolynomial factor)^n := by
  induction n generalizing acc with
  | zero => simp [rootIntegerListRepeatMultiply]
  | succ n ih =>
    rw [rootIntegerListRepeatMultiply,ih,rootIntegerListMultiply_polynomial]
    rw [pow_succ]
    ring

/-- The outer factor loop starts at the literal one-cell content array. -/
def rootIntegerFactorProduct (content : ℤ) (factors : List (List ℤ×ℕ)) : List ℤ :=
  factors.foldl (fun acc f => rootIntegerListRepeatMultiply f.1 f.2 acc) [content]

/-- The finite construction in `NativeRootFactorProduct` satisfies `rootIntegerListPolynomial_singleton` under the displayed hypotheses. -/
theorem rootIntegerListPolynomial_singleton (c : ℤ) :
    rootIntegerListPolynomial [c]=C (c : ℂ) := by
  apply Polynomial.ext
  intro k
  rw [rootIntegerListPolynomial_coeff,Polynomial.coeff_C]
  cases k <;> simp

/-- The finite construction in `NativeRootFactorProduct` satisfies `rootFactorFold_polynomial` under the displayed hypotheses. -/
private theorem rootFactorFold_polynomial (factors : List (List ℤ×ℕ)) (acc : List ℤ) :
    rootIntegerListPolynomial
      (factors.foldl (fun acc f => rootIntegerListRepeatMultiply f.1 f.2 acc) acc)=
      rootIntegerListPolynomial acc*
        (factors.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod := by
  induction factors generalizing acc with
  | nil => simp
  | cons f rest ih =>
    rw [List.foldl_cons,ih,rootIntegerListRepeatMultiply_polynomial]
    simp only [List.map_cons,List.prod_cons,mul_assoc]

/-- The finite construction in `NativeRootFactorProduct` satisfies `rootIntegerFactorProduct_polynomial` under the displayed hypotheses. -/
theorem rootIntegerFactorProduct_polynomial (content : ℤ) (factors : List (List ℤ×ℕ)) :
    rootIntegerListPolynomial (rootIntegerFactorProduct content factors)=
      C (content : ℂ)*(factors.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod := by
  rw [rootIntegerFactorProduct,rootFactorFold_polynomial,rootIntegerListPolynomial_singleton]

/-- The source coefficient guard on normalized factors and the original target. -/
theorem rootIntegerFactorProduct_guard (target : List ℤ) (content : ℤ)
    (factors : List (List ℤ×ℕ))
    (hguard : rootIntegerFactorProduct content factors=rootCanonicalCoefficients target) :
    rootIntegerListPolynomial target=
      C (content : ℂ)*(factors.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod := by
  rw [← rootCanonicalCoefficients_polynomial target,← hguard]
  exact rootIntegerFactorProduct_polynomial content factors

/-- Actual coefficient-list equality replaces an external polynomial-product
premise. Factor/target canonicalization transports the ORIGINAL inputs. -/
theorem rootIntegerFactorProduct_original_guard (target : List ℤ) (content : ℤ)
    (factors : List (List ℤ×ℕ))
    (hguard : rootIntegerFactorProduct content
      (factors.map (fun f => (rootCanonicalCoefficients f.1,f.2)))=
        rootCanonicalCoefficients target) :
    rootIntegerListPolynomial target=
      C (content : ℂ)*(factors.map (fun f => (rootIntegerListPolynomial f.1)^f.2)).prod := by
  calc
    _=rootIntegerListPolynomial (rootCanonicalCoefficients target) :=
      (rootCanonicalCoefficients_polynomial target).symm
    _=rootIntegerListPolynomial (rootIntegerFactorProduct content
        (factors.map (fun f => (rootCanonicalCoefficients f.1,f.2)))) :=
      congrArg rootIntegerListPolynomial hguard.symm
    _=_ := by
      rw [rootIntegerFactorProduct_polynomial]
      simp only [List.map_map,Function.comp_def,rootCanonicalCoefficients_polynomial]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
