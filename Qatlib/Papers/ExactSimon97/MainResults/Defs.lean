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

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ExactSimon97.MainResults

abbrev BoolVec (n : ℕ) : Type := Fin n → ZMod 2

def dot {n : ℕ} (g h : BoolVec n) : ZMod 2 := ∑ i, g i * h i

@[simp] lemma dot_zero_left {n : ℕ} (h : BoolVec n) : dot 0 h = 0 := by
  simp [dot]

@[simp] lemma dot_zero_right {n : ℕ} (g : BoolVec n) : dot g 0 = 0 := by
  simp [dot]

lemma dot_add_left {n : ℕ} (g g' h : BoolVec n) :
    dot (g + g') h = dot g h + dot g' h := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {n : ℕ} (g h h' : BoolVec n) :
    dot g (h + h') = dot g h + dot g h' := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_smul_left {n : ℕ} (c : ZMod 2) (g h : BoolVec n) :
    dot (c • g) h = c * dot g h := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma dot_smul_right {n : ℕ} (c : ZMod 2) (g h : BoolVec n) :
    dot g (c • h) = c * dot g h := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma dot_neg_left {n : ℕ} (g h : BoolVec n) : dot (-g) h = -dot g h := by
  have h1 := dot_smul_left (n := n) (-1) g h
  rwa [neg_one_smul, neg_one_mul] at h1

lemma dot_neg_right {n : ℕ} (g h : BoolVec n) : dot g (-h) = -dot g h := by
  have h1 := dot_smul_right (n := n) (-1) g h
  rwa [neg_one_smul, neg_one_mul] at h1

def ortho {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) : Submodule (ZMod 2) (BoolVec n) where
  carrier := {g | ∀ h ∈ H, dot g h = 0}
  zero_mem' := by intro h _; simp
  add_mem' := by
    intro g g' hg hg' h hh
    rw [dot_add_left, hg h hh, hg' h hh, add_zero]
  smul_mem' := by
    intro c g hg h hh
    rw [dot_smul_left, hg h hh, mul_zero]

@[simp] lemma mem_ortho {n : ℕ} {H : Submodule (ZMod 2) (BoolVec n)} {g : BoolVec n} :
    g ∈ ortho H ↔ ∀ h ∈ H, dot g h = 0 := Iff.rfl

def spanFinset {n : ℕ} (X : Finset (BoolVec n)) : Submodule (ZMod 2) (BoolVec n) :=
  Submodule.span (ZMod 2) ((X : Finset (BoolVec n)) : Set (BoolVec n))

def LinIndep {n k : ℕ} (v : Fin k → BoolVec n) : Prop :=
  LinearIndependent (ZMod 2) v

def Generates {n k : ℕ} (v : Fin k → BoolVec n) (V : Submodule (ZMod 2) (BoolVec n)) : Prop :=
  Submodule.span (ZMod 2) (Set.range v) = V

def FulfillsPromise {n : ℕ} {R : Type} (ρ : BoolVec n → R)
    (H0 : Submodule (ZMod 2) (BoolVec n)) : Prop :=
  ∀ x y, ρ x = ρ y ↔ x - y ∈ H0

abbrev AbGroup (n : ℕ) (m : Fin n → ℕ) : Type := (i : Fin n) → ZMod (m i)

noncomputable def charPair {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : ℂ :=
  ∏ i, @ZMod.stdAddChar (m i) (hnz i) (g i * h i)

lemma charPair_add_left {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g g' h : AbGroup n m) :
    charPair (m := m) (g + g') h = charPair (m := m) g h * charPair (m := m) g' h := by
  simp only [charPair, Pi.add_apply, add_mul, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

lemma charPair_add_right {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h h' : AbGroup n m) :
    charPair (m := m) g (h + h') = charPair (m := m) g h * charPair (m := m) g h' := by
  simp only [charPair, Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

lemma charPair_neg_right {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) :
    charPair (m := m) g (-h) = (charPair (m := m) g h)⁻¹ := by
  simp only [charPair, Pi.neg_apply, mul_neg, AddChar.map_neg_eq_inv, Finset.prod_inv_distrib]

lemma charPair_comm {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (g h : AbGroup n m) : charPair (m := m) g h = charPair (m := m) h g := by
  simp only [charPair, mul_comm]

noncomputable def FG {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (f : AbGroup n m → ℂ) : AbGroup n m → ℂ :=
  fun g => ((Real.sqrt (Fintype.card (AbGroup n m) : ℝ) : ℂ))⁻¹ *
    ∑ h, charPair (m := m) g h * f h

def tau {n : ℕ} {m : Fin n → ℕ} (t : AbGroup n m) (f : AbGroup n m → ℂ) :
    AbGroup n m → ℂ :=
  fun g => f (g - t)

noncomputable def phi {n : ℕ} {m : Fin n → ℕ} [hnz : ∀ i, NeZero (m i)]
    (h : AbGroup n m) (f : AbGroup n m → ℂ) : AbGroup n m → ℂ :=
  fun g => charPair (m := m) h g * f g

end Qatlib.Papers.ExactSimon97.MainResults
