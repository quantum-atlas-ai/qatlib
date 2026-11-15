/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Data.Bool.Basic

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.CosetReduction

abbrev Position (V : Type*) := (V × V) × Bool
abbrev BoolMatrix (V : Type*) := V → V → Bool

variable {V : Type*}

def liftPerm (p : Equiv.Perm V) : Equiv.Perm (Position V) :=
  (p.prodCongr p).prodCongr (Equiv.refl Bool)

def liftHom (V : Type*) : Equiv.Perm V →* Equiv.Perm (Position V) where
  toFun := liftPerm
  map_one' := by ext x <;> rfl
  map_mul' := by intro p q; ext x <;> rfl

def flipMatrix (A : BoolMatrix V) : Equiv.Perm (Position V) where
  toFun := fun x => (x.1, xor x.2 (A x.1.1 x.1.2))
  invFun := fun x => (x.1, xor x.2 (A x.1.1 x.1.2))
  left_inv := by
    rintro ⟨⟨i,j⟩,b⟩
    simp
  right_inv := by
    rintro ⟨⟨i,j⟩,b⟩
    simp

def colorSubgroup (V : Type*) : Subgroup (Equiv.Perm (Position V)) where
  carrier := {p | ∀ x, (p x).2 = x.2}
  one_mem' := by intro x; rfl
  mul_mem' := by
    intro p q hp hq x
    exact (hp (q x)).trans (hq x)
  inv_mem' := by
    intro p hp x
    have h := hp (p.symm x)
    simpa using h.symm

def encodedSubgroup (A : BoolMatrix V) : Subgroup (Equiv.Perm (Position V)) :=
  (liftHom V).range.map (MulAut.conj (flipMatrix A)).toMonoidHom

def cosetRepresentative (A B : BoolMatrix V) : Equiv.Perm (Position V) :=
  flipMatrix B * (flipMatrix A)⁻¹

open scoped Pointwise

def CosetIntersects (A B : BoolMatrix V) : Prop :=
  ((colorSubgroup V : Set (Equiv.Perm (Position V))) ∩
    cosetRepresentative A B • (encodedSubgroup A : Set (Equiv.Perm (Position V)))).Nonempty

def MatrixIso (A B : BoolMatrix V) : Prop :=
  ∃ p : Equiv.Perm V, ∀ i j, B (p i) (p j) = A i j

def recoverVertex (A B : BoolMatrix V) (k : Equiv.Perm (Position V)) (i : V) : V :=
  (((flipMatrix B)⁻¹ * k * flipMatrix A) ((i,i),false)).1.1

end Qatlib.Concepts.GraphQuery.CosetReduction
