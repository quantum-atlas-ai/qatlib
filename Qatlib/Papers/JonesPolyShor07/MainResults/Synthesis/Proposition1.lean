/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciRepresentation

/-!
# Multiplicative evaluation of Fibonacci words

The evaluations `evalSS`, `evalSP`, and `evalPS` send the empty word to the identity and
concatenation to matrix multiplication. The module also evaluates singleton SS words as a
generator matrix or its inverse, according to the sign. See [ShorJordan2008].

## Main statements

* `evalSS_append`: The SS evaluation of a concatenation is the product of the two SS
  evaluations.
* `evalSS_singleton`: A singleton SS word with true sign evaluates to its generator matrix.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis

open Definitions Matrix

/-- If each fold step multiplies the accumulator by its value at one, folding from M equals M
times the fold from one. -/
private theorem foldl_mul {M β : Type} [Monoid M] (f : M → β → M)
    (hf : ∀ M b, f M b = M * f 1 b) (M : M) (l : List β) :
    l.foldl f M = M * l.foldl f 1 := by
  induction l generalizing M with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih (f M b), List.foldl_cons, ih (f 1 b), hf M b, hf 1 b,
      one_mul, mul_assoc]

/-- The empty word evaluates to the identity in the SS sector; see [ShorJordan2008]. -/
@[simp] theorem evalSS_nil (k : ℕ) : evalSS k [] = 1 := rfl

/-- The empty word evaluates to the identity in the SP sector. -/
@[simp] theorem evalSP_nil (k : ℕ) : evalSP k [] = 1 := rfl

/-- The empty word evaluates to the identity in the PS sector. -/
@[simp] theorem evalPS_nil (k : ℕ) : evalPS k [] = 1 := rfl

/-- The SS evaluation of a concatenation is the product of the two SS evaluations; see
[ShorJordan2008]. -/
theorem evalSS_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalSS k (w₁ ++ w₂) = evalSS k w₁ * evalSS k w₂ := by
  unfold evalSS
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

/-- The SP evaluation of a concatenation is the product of the two SP evaluations; see
[ShorJordan2008]. -/
theorem evalSP_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalSP k (w₁ ++ w₂) = evalSP k w₁ * evalSP k w₂ := by
  unfold evalSP
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

/-- The PS evaluation of a concatenation is the product of the two PS evaluations; see
[ShorJordan2008]. -/
theorem evalPS_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalPS k (w₁ ++ w₂) = evalPS k w₁ * evalPS k w₂ := by
  unfold evalPS
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

/-- A singleton SS word with true sign evaluates to its generator matrix; see [ShorJordan2008]. -/
theorem evalSS_singleton (k : ℕ) (i : Fin (k - 1)) :
    evalSS k [(i, true)] = rhoSS k i := by
  simp [evalSS]

/-- A singleton SS word with false sign evaluates to the inverse generator matrix. -/
theorem evalSS_singleton_inv (k : ℕ) (i : Fin (k - 1)) :
    evalSS k [(i, false)] = (rhoSS k i)⁻¹ := by
  simp [evalSS]

end Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis
