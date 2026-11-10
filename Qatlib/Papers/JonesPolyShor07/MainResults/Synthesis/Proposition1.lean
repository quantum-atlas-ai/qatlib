/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPolyShor07.MainResults.Definitions.FibonacciRepresentation
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis

open Definitions Matrix

private theorem foldl_mul {M β : Type} [Monoid M] (f : M → β → M)
    (hf : ∀ M b, f M b = M * f 1 b) (M : M) (l : List β) :
    l.foldl f M = M * l.foldl f 1 := by
  induction l generalizing M with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih (f M b), List.foldl_cons, ih (f 1 b), hf M b, hf 1 b,
      one_mul, mul_assoc]

@[simp] theorem evalSS_nil (k : ℕ) : evalSS k [] = 1 := rfl

@[simp] theorem evalSP_nil (k : ℕ) : evalSP k [] = 1 := rfl

@[simp] theorem evalPS_nil (k : ℕ) : evalPS k [] = 1 := rfl

theorem evalSS_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalSS k (w₁ ++ w₂) = evalSS k w₁ * evalSS k w₂ := by
  unfold evalSS
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

theorem evalSP_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalSP k (w₁ ++ w₂) = evalSP k w₁ * evalSP k w₂ := by
  unfold evalSP
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

theorem evalPS_append (k : ℕ) (w₁ w₂ : BraidWord k) :
    evalPS k (w₁ ++ w₂) = evalPS k w₁ * evalPS k w₂ := by
  unfold evalPS
  rw [List.foldl_append]
  exact foldl_mul _ (fun M g => by rw [one_mul]) _ _

theorem evalSS_singleton (k : ℕ) (i : Fin (k - 1)) :
    evalSS k [(i, true)] = rhoSS k i := by
  simp [evalSS]

theorem evalSS_singleton_inv (k : ℕ) (i : Fin (k - 1)) :
    evalSS k [(i, false)] = (rhoSS k i)⁻¹ := by
  simp [evalSS]

end Qatlib.Papers.JonesPolyShor07.MainResults.Synthesis
