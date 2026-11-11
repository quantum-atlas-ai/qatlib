/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Binary spaces and finite abelian Fourier operators

This module introduces the binary vector spaces, bilinear pairing, orthogonal submodules, and
hiding promise used throughout the exact Simon development. It also defines character pairings,
Fourier transforms, translations, and phase multiplications on finite products of cyclic groups.
These constructions support the results of [BrassardHoyer1997].

## Main statements

* `ortho`: defines orthogonality with respect to the binary dot product.
* `FulfillsPromise`: states that oracle fibers are exactly cosets of the hidden submodule.
* `FG`: defines the normalized finite abelian Fourier transform.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

/-- The binary vector space of functions from `Fin n` to `ZMod 2`. -/
abbrev BoolVec (n : ℕ) : Type := Fin n → ZMod 2

/-- The coordinate dot product of two binary vectors, valued in `ZMod 2`. -/
def dot {n : ℕ} (g h : BoolVec n) : ZMod 2 := ∑ i, g i * h i

/-- The binary dot product of zero with any vector is zero. -/
@[simp] lemma dot_zero_left {n : ℕ} (h : BoolVec n) : dot 0 h = 0 := by
  simp [dot]

/-- The binary dot product of any vector with zero is zero. -/
@[simp] lemma dot_zero_right {n : ℕ} (g : BoolVec n) : dot g 0 = 0 := by
  simp [dot]

/-- The binary dot product is additive in its first argument. -/
lemma dot_add_left {n : ℕ} (g g' h : BoolVec n) :
    dot (g + g') h = dot g h + dot g' h := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The binary dot product is additive in its second argument. -/
lemma dot_add_right {n : ℕ} (g h h' : BoolVec n) :
    dot g (h + h') = dot g h + dot g h' := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Scalar multiplication in the first argument scales the binary dot product. -/
lemma dot_smul_left {n : ℕ} (c : ZMod 2) (g h : BoolVec n) :
    dot (c • g) h = c * dot g h := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Scalar multiplication in the second argument scales the binary dot product. -/
lemma dot_smul_right {n : ℕ} (c : ZMod 2) (g h : BoolVec n) :
    dot g (c • h) = c * dot g h := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Negating the first argument negates the binary dot product. -/
lemma dot_neg_left {n : ℕ} (g h : BoolVec n) : dot (-g) h = -dot g h := by
  have h1 := dot_smul_left (n := n) (-1) g h
  rwa [neg_one_smul, neg_one_mul] at h1

/-- Negating the second argument negates the binary dot product. -/
lemma dot_neg_right {n : ℕ} (g h : BoolVec n) : dot g (-h) = -dot g h := by
  have h1 := dot_smul_right (n := n) (-1) g h
  rwa [neg_one_smul, neg_one_mul] at h1

/-- The submodule of vectors whose binary dot product with every vector of `H` is zero. -/
def ortho {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) : Submodule (ZMod 2) (BoolVec n) where
  carrier := {g | ∀ h ∈ H, dot g h = 0}
  zero_mem' := by intro h _; simp
  add_mem' := by
    intro g g' hg hg' h hh
    rw [dot_add_left, hg h hh, hg' h hh, add_zero]
  smul_mem' := by
    intro c g hg h hh
    rw [dot_smul_left, hg h hh, mul_zero]

/-- A vector belongs to `ortho H` exactly when its dot product with every vector of `H`
vanishes. -/
@[simp] lemma mem_ortho {n : ℕ} {H : Submodule (ZMod 2) (BoolVec n)} {g : BoolVec n} :
    g ∈ ortho H ↔ ∀ h ∈ H, dot g h = 0 := Iff.rfl

/-- The binary submodule spanned by a finite set of vectors. -/
def spanFinset {n : ℕ} (X : Finset (BoolVec n)) : Submodule (ZMod 2) (BoolVec n) :=
  Submodule.span (ZMod 2) ((X : Finset (BoolVec n)) : Set (BoolVec n))

/-- Linear independence of a finite binary vector family over `ZMod 2`. -/
def LinIndep {n k : ℕ} (v : Fin k → BoolVec n) : Prop :=
  LinearIndependent (ZMod 2) v

/-- The assertion that a finite binary vector family spans `V`. -/
def Generates {n k : ℕ} (v : Fin k → BoolVec n) (V : Submodule (ZMod 2) (BoolVec n)) : Prop :=
  Submodule.span (ZMod 2) (Set.range v) = V

/-- The hiding promise that `ρ x = ρ y` holds exactly when `x - y` belongs to `H0`. -/
def FulfillsPromise {n : ℕ} {R : Type} (ρ : BoolVec n → R)
    (H0 : Submodule (ZMod 2) (BoolVec n)) : Prop :=
  ∀ x y, ρ x = ρ y ↔ x - y ∈ H0

/-- The product of cyclic groups `ZMod (m i)` indexed by `Fin n`. -/
abbrev AbGroup (n : ℕ) (m : Fin n → ℕ) : Type := (i : Fin n) → ZMod (m i)

/-- The product of standard additive character values on the coordinate products of two group
elements. -/
noncomputable def charPair {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : ℂ :=
  ∏ i, @ZMod.stdAddChar (m i) (hnz i) (g i * h i)

/-- The character pairing turns addition in its first argument into multiplication. -/
lemma charPair_add_left {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g g' h : AbGroup n m) :
    charPair (m := m) (g + g') h = charPair (m := m) g h * charPair (m := m) g' h := by
  simp only [charPair, Pi.add_apply, add_mul, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

/-- The character pairing turns addition in its second argument into multiplication. -/
lemma charPair_add_right {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h h' : AbGroup n m) :
    charPair (m := m) g (h + h') = charPair (m := m) g h * charPair (m := m) g h' := by
  simp only [charPair, Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

/-- Negating the second argument inverts the character pairing. -/
lemma charPair_neg_right {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) :
    charPair (m := m) g (-h) = (charPair (m := m) g h)⁻¹ := by
  simp only [charPair, Pi.neg_apply, mul_neg, AddChar.map_neg_eq_inv, Finset.prod_inv_distrib]

/-- The character pairing is symmetric in its two arguments. -/
lemma charPair_comm {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : charPair (m := m) g h = charPair (m := m) h g := by
  simp only [charPair, mul_comm]

/-- The normalized Fourier transform defined by summing against the character pairing. -/
noncomputable def FG {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (f : AbGroup n m → ℂ) : AbGroup n m → ℂ :=
  fun g => ((Real.sqrt (Fintype.card (AbGroup n m) : ℝ) : ℂ))⁻¹ *
    ∑ h, charPair (m := m) g h * f h

/-- The translation operator sending `f` to the function `g ↦ f (g - t)`. -/
def tau {n : ℕ} {m : Fin n → ℕ} (t : AbGroup n m) (f : AbGroup n m → ℂ) :
    AbGroup n m → ℂ :=
  fun g => f (g - t)

/-- The phase multiplication operator sending `f g` to `charPair h g * f g`. -/
noncomputable def phi {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (h : AbGroup n m) (f : AbGroup n m → ℂ) : AbGroup n m → ℂ :=
  fun g => charPair (m := m) h g * f g

end Qatlib.Papers.ExactSimon97.MainResults
