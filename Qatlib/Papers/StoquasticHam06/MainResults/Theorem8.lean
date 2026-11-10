/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem8

def flipBit {n : ℕ} (i : Fin n) (y : Sigma n) : Sigma n :=
  Function.update y i (!(y i))

def flipSet {n : ℕ} (S : Finset (Fin n)) (y : Sigma n) : Sigma n :=
  fun i => if i ∈ S then !(y i) else y i

@[simp] theorem flipSet_empty {n : ℕ} (y : Sigma n) :
    flipSet ∅ y = y := by
  funext i; simp [flipSet]

theorem flipSet_ne_self {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (y : Sigma n) : flipSet S y ≠ y := by
  obtain ⟨i, hi⟩ := hS
  intro h
  have := congrFun h i
  simp [flipSet, hi] at this

def xString {n : ℕ} (S : Finset (Fin n)) : QMatrix n :=
  fun x y => if x = flipSet S y then 1 else 0

def negXString {n : ℕ} (S : Finset (Fin n)) : QMatrix n :=
  fun x y => if x = flipSet S y then (-1) else 0

def qsmul {n : ℕ} (h : ℚ) (A : QMatrix n) : QMatrix n := fun x y => h * A x y

theorem negXString_offdiag_nonpos {n : ℕ} (S : Finset (Fin n)) (h : ℚ) (hh : 0 ≤ h)
    (x y : Sigma n) (_hxy : x ≠ y) :
    QMatrix.toReal (qsmul h (negXString S)) x y ≤ 0 := by
  unfold QMatrix.toReal qsmul negXString
  split_ifs with hx
  · have : (h * (-1) : ℚ) ≤ 0 := by
      nlinarith
    exact_mod_cast this
  · simp

theorem diag_offdiag_zero {n : ℕ} (E : QMatrix n)
    (hE : ∀ x y : Sigma n, x ≠ y → E x y = 0) (x y : Sigma n) (hxy : x ≠ y) :
    QMatrix.toReal E x y = 0 := by
  unfold QMatrix.toReal
  rw [hE x y hxy]; simp

theorem tripleX_form_stoquastic {n m : ℕ} (E : QMatrix n)
    (hE : ∀ x y : Sigma n, x ≠ y → E x y = 0)
    (S : Fin m → Finset (Fin n)) (h : Fin m → ℚ) (hh : ∀ a, 0 ≤ h a) :
    ∀ x y : Sigma n, x ≠ y →
      QMatrix.toReal
        (fun p q => E p q + ∑ a : Fin m, qsmul (h a) (negXString (S a)) p q) x y ≤ 0 := by
  intro x y hxy
  unfold QMatrix.toReal
  have hdiag : E x y = 0 := hE x y hxy
  simp only [hdiag, zero_add]

  have hterm : ∀ a : Fin m, ((qsmul (h a) (negXString (S a))) x y : ℝ) ≤ 0 := by
    intro a
    have := negXString_offdiag_nonpos (S a) (h a) (hh a) x y hxy
    simpa [QMatrix.toReal] using this
  have hsum : ((∑ a : Fin m, (qsmul (h a) (negXString (S a))) x y : ℚ) : ℝ) ≤ 0 := by
    push_cast
    exact Finset.sum_nonpos (fun a _ => hterm a)
  simpa using hsum

theorem flipSet_flipSet {n : ℕ} (S : Finset (Fin n)) (y : Sigma n) :
    flipSet S (flipSet S y) = y := by
  funext i
  by_cases hi : i ∈ S <;> simp [flipSet, hi]

theorem xString_entry {n : ℕ} (S : Finset (Fin n)) (x y : Sigma n) :
    xString S x y = 0 ∨ xString S x y = 1 := by
  unfold xString
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem8
