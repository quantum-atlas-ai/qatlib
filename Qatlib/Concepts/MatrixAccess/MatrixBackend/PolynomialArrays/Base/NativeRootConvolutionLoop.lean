/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerList
import Mathlib.Data.List.FinRange

set_option backward.isDefEq.respectTransparency false

/-! The nested ascending-index convolution loop, with an arbitrary initial
state invariant. Only bounded integer updates are modeled, not Python objects. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open scoped BigOperators

/-- The finite construction in `NativeRootConvolutionLoop` satisfies `rootArrayFold_coordinate` under the displayed hypotheses. -/
private theorem rootArrayFold_coordinate {α : Type} {N : ℕ}
    (l : List α) (step : (Fin N → ℤ) → α → (Fin N → ℤ))
    (v : α → ℤ) (k : Fin N)
    (hstep : ∀ s i,step s i k=s k+v i) (s : Fin N → ℤ) :
    l.foldl step s k=s k+(l.map v).sum := by
  induction l generalizing s with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons,ih,hstep]
    simp only [List.map_cons,List.sum_cons]
    omega

/-- The source inner j loop in order, updating exactly output cell i+j. -/
def rootIntegerConvolutionInner {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) (i : Fin (d+1))
    (s : Fin (d+e+1) → ℤ) : Fin (d+e+1) → ℤ :=
  (List.finRange (e+1)).foldl
    (fun state j k => if i.val+j.val=k.val then state k+a i*b j else state k) s

/-- The finite construction in `NativeRootConvolutionLoop` satisfies `rootIntegerConvolutionInner_coordinate` under the displayed hypotheses. -/
theorem rootIntegerConvolutionInner_coordinate {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) (i : Fin (d+1))
    (s : Fin (d+e+1) → ℤ) (k : Fin (d+e+1)) :
    rootIntegerConvolutionInner a b i s k=
      s k+∑ j,if i.val+j.val=k.val then a i*b j else 0 := by
  unfold rootIntegerConvolutionInner
  rw [rootArrayFold_coordinate (List.finRange (e+1)) _
    (fun j => if i.val+j.val=k.val then a i*b j else 0) k]
  · rw [← List.ofFn_eq_map,Fin.sum_ofFn]
  · intro state j
    split_ifs <;> simp

/-- The source outer i loop in order, starting with the actual zero array. -/
def rootIntegerConvolutionLoop {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) : Fin (d+e+1) → ℤ :=
  (List.finRange (d+1)).foldl (fun state i => rootIntegerConvolutionInner a b i state)
    (fun _ => 0)

/-- The finite construction in `NativeRootConvolutionLoop` satisfies `rootIntegerConvolutionLoop_eq` under the displayed hypotheses. -/
theorem rootIntegerConvolutionLoop_eq {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) :
    rootIntegerConvolutionLoop a b=rootIntegerConvolution a b := by
  funext k
  unfold rootIntegerConvolutionLoop
  rw [rootArrayFold_coordinate (List.finRange (d+1)) _
    (fun i => ∑ j,if i.val+j.val=k.val then a i*b j else 0) k]
  · rw [← List.ofFn_eq_map,Fin.sum_ofFn]
    simp only [zero_add,rootIntegerConvolution]
  · intro state i
    exact rootIntegerConvolutionInner_coordinate a b i state k

/-- Each typed update stays inside the allocated output array. -/
theorem rootIntegerConvolutionLoop_update_bound {d e : ℕ}
    (i : Fin (d+1)) (j : Fin (e+1)) : i.val+j.val<d+e+1 := by
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The SAME loop output, after any finite zero-tail normalization trace,
interprets the product of the SAME dynamic input arrays. -/
theorem rootIntegerConvolutionLoop_trimmed_product {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) (out : List ℤ)
    (htrace : RootZeroTailDeletion (List.ofFn (rootIntegerConvolutionLoop a b)) out) :
    rootIntegerListPolynomial out=
      rootIntegerListPolynomial (List.ofFn a)*rootIntegerListPolynomial (List.ofFn b) := by
  rw [← rootIntegerListPolynomial_zero_tail_trace htrace]
  rw [rootIntegerConvolutionLoop_eq,rootIntegerListPolynomial_ofFn,
    rootIntegerPolynomial_convolution,rootIntegerListPolynomial_ofFn,
    rootIntegerListPolynomial_ofFn]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
