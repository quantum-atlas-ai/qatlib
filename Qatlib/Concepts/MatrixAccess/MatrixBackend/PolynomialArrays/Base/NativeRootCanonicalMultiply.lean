/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootConvolutionLoop
import Mathlib.Data.List.Induction

set_option backward.isDefEq.respectTransparency false

/-! A terminating pure integer-list model of canonical and multiply: actual
ordered updates, empty branch and normalization, all on the same inputs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Remove exactly the maximal zero suffix of an already decoded integer list. -/
def rootCanonicalCoefficients (a : List ℤ) : List ℤ :=
  (a.reverse.dropWhile (fun x => x==0)).reverse

/-- The normalization trace is derived for every input, not supplied. -/
theorem rootCanonicalCoefficients_trace (a : List ℤ) :
    RootZeroTailDeletion a (rootCanonicalCoefficients a) := by
  induction a using List.reverseRecOn with
  | nil => simpa [rootCanonicalCoefficients] using RootZeroTailDeletion.refl ([] : List ℤ)
  | append_singleton a x ih =>
    by_cases hx : x=0
    · subst x
      simpa [rootCanonicalCoefficients] using
        RootZeroTailDeletion.pop a (rootCanonicalCoefficients a) ih
    · have hc : rootCanonicalCoefficients (a++[x])=a++[x] := by
        simp [rootCanonicalCoefficients,hx]
      rw [hc]
      exact RootZeroTailDeletion.refl _

/-- A normalized nonempty list has an actual nonzero final coefficient. -/
theorem rootCanonicalCoefficients_shape (a : List ℤ) :
    rootCanonicalCoefficients a=[] ∨
      ∃ b x,rootCanonicalCoefficients a=b++[x] ∧ x≠0 := by
  induction a using List.reverseRecOn with
  | nil => left; simp [rootCanonicalCoefficients]
  | append_singleton a x ih =>
    by_cases hx : x=0
    · subst x
      have hc : rootCanonicalCoefficients (a++[0])=rootCanonicalCoefficients a := by
        simp [rootCanonicalCoefficients]
      simpa only [hc] using ih
    · right
      refine ⟨a,x,?_,hx⟩
      simp [rootCanonicalCoefficients,hx]

/-- The finite construction in `NativeRootCanonicalMultiply` satisfies `rootCanonicalCoefficients_polynomial` under the displayed hypotheses. -/
theorem rootCanonicalCoefficients_polynomial (a : List ℤ) :
    rootIntegerListPolynomial (rootCanonicalCoefficients a)=rootIntegerListPolynomial a :=
  (rootIntegerListPolynomial_zero_tail_trace (rootCanonicalCoefficients_trace a)).symm

/-- Exact nested convolution, followed by the source zero-suffix normalization.
The empty-input branch agrees literally with the public multiply function. -/
def rootIntegerListMultiply : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | _,[] => []
  | x::xs,y::ys => rootCanonicalCoefficients (List.ofFn
      (rootIntegerConvolutionLoop (fun i : Fin (xs.length+1) => (x::xs).get i)
        (fun j : Fin (ys.length+1) => (y::ys).get j)))

/-- The finite construction in `NativeRootCanonicalMultiply` satisfies `rootIntegerListMultiply_polynomial` under the displayed hypotheses. -/
theorem rootIntegerListMultiply_polynomial (a b : List ℤ) :
    rootIntegerListPolynomial (rootIntegerListMultiply a b)=
      rootIntegerListPolynomial a*rootIntegerListPolynomial b := by
  cases a with
  | nil => simp [rootIntegerListMultiply,rootIntegerListPolynomial_nil]
  | cons x xs =>
    cases b with
    | nil => simp [rootIntegerListMultiply,rootIntegerListPolynomial_nil]
    | cons y ys =>
      have ha : List.ofFn (fun i : Fin (xs.length+1) => (x::xs).get i)=x::xs :=
        List.ofFn_get (x::xs)
      have hb : List.ofFn (fun j : Fin (ys.length+1) => (y::ys).get j)=y::ys :=
        List.ofFn_get (y::ys)
      simpa only [rootIntegerListMultiply,ha,hb] using
        rootIntegerConvolutionLoop_trimmed_product
          (fun i : Fin (xs.length+1) => (x::xs).get i)
          (fun j : Fin (ys.length+1) => (y::ys).get j)
          _ (rootCanonicalCoefficients_trace _)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
