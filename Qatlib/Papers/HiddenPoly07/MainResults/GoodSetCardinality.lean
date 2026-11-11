/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Cardinality of nonzero coordinate tuples

This module defines `Xgood` as the finite set of tuples with nonzero coordinates. An equivalence
between the field and optional units yields `card_units_eq`, from which `card_Xgood` and a
uniform real lower bound follow.

The development follows [DeckerDraismaWocjan2009].

## Main statements

* `mem_Xgood`: A tuple belongs to `Xgood F n` exactly when every coordinate is nonzero.
* `card_Xgood`: For a finite field of cardinality d, the good tuple set has cardinality (d −
  1)^n.
* `card_Xgood_ge`: For d ≥ 2, the real number (d − 1)^n is at least d^n/2^n.

## References

* [Decker et al., 2009][DeckerDraismaWocjan2009]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HiddenPoly07.MainResults

open scoped BigOperators

/-- The equivalence from optional field units to the field, sending `none` to zero and `some u`
to the underlying nonzero element. -/
def optionUnitsEquiv (F : Type*) [Field F] [DecidableEq F] : Option Fˣ ≃ F where
  toFun o := o.elim 0 fun u => (u : F)
  invFun x := if h : x = 0 then none else some (Units.mk0 x h)
  left_inv := by
    intro o
    cases o with
    | none => simp
    | some u => simp
  right_inv := by
    intro x
    by_cases h : x = 0 <;> simp [h]

/-- The unit group of a finite field has cardinality one less than the field. -/
theorem card_units_eq (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card Fˣ = Fintype.card F - 1 := by
  have h : Fintype.card (Option Fˣ) = Fintype.card F :=
    Fintype.card_congr (optionUnitsEquiv F)
  rw [Fintype.card_option] at h
  omega

/-- The finite set of n-tuples obtained from units of `F`, equivalently the tuples whose
coordinates are all nonzero. -/
def Xgood (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) : Finset (Fin n → F) :=
  Finset.univ.image fun x : Fin n → Fˣ => fun i => (x i : F)

/-- A tuple belongs to `Xgood F n` exactly when every coordinate is nonzero. -/
theorem mem_Xgood {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    {x : Fin n → F} : x ∈ Xgood F n ↔ ∀ i, x i ≠ 0 := by
  simp only [Xgood, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩ i
    exact Units.ne_zero (u i)
  · intro hx
    exact ⟨fun i => Units.mk0 (x i) (hx i), by simp⟩

/-- For a finite field of cardinality d, the good tuple set has cardinality (d − 1)^n
([Proposition 4.1][DeckerDraismaWocjan2009]). -/
theorem card_Xgood (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Xgood F n).card = (Fintype.card F - 1) ^ n := by
  classical
  rw [Xgood, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, card_units_eq F]
  · intro u v huv
    funext i
    exact Units.ext (congrFun huv i)

/-- For d ≥ 2, the real number (d − 1)^n is at least d^n/2^n ([Proposition
4.1][DeckerDraismaWocjan2009]). -/
theorem card_Xgood_ge (F : Type*) [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (hF : 2 ≤ Fintype.card F) :
    (Fintype.card F : ℝ) ^ n / 2 ^ n ≤ ((Fintype.card F - 1 : ℕ) : ℝ) ^ n := by
  have hd : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hcast : ((Fintype.card F - 1 : ℕ) : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
    norm_num
  rw [hcast, ← div_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

end Qatlib.Papers.HiddenPoly07.MainResults
