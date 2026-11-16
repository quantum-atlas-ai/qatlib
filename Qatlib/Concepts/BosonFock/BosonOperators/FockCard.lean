/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BosonFock.BosonOperators.RowFibers
public import Mathlib.Data.Sym.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section


/-! # The actual bounded occupations and stars-and-bars cardinality

The concrete occupation type is transported to fixed-size multisets
using the actual repeated-mode list, rather than replacing its cardinality
by an assumed binomial formula. This is needed by the fixed-source
LinearOptics10 Proposition 71.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Concepts.BosonFock.BosonOperators.FockCard
open Qatlib.Concepts.BosonFock.BosonOperators

/-- The actual repeated-mode list gives a multiset of exactly the prescribed photon number. -/
def toSym {m n : ℕ} (S : FockOccupation m n) : Sym (Fin m) n :=
  ⟨(bosonRows (fun i => (S.1 i : ℕ)) : Multiset (Fin m)), by
    simpa only [Multiset.coe_card] using (bosonRows_length (fun i => (S.1 i : ℕ))).trans S.2⟩

/-- A fixed-size multiset gives bounded mode counts whose actual sum is its cardinality. -/
def ofSym {m n : ℕ} (s : Sym (Fin m) n) : FockOccupation m n :=
  ⟨fun i => ⟨(s : Multiset (Fin m)).count i, by
    have h := Multiset.count_le_card i (s : Multiset (Fin m))
    rw [Sym.card_coe] at h
    omega⟩, by
      rw [Multiset.sum_count_eq_card (fun i _ => Finset.mem_univ i), Sym.card_coe]⟩

/-- The multiset constructed from an actual occupation has exactly its original mode counts. -/
theorem toSymCount {m n : ℕ} (S : FockOccupation m n) (i : Fin m) :
    (toSym S : Multiset (Fin m)).count i = (S.1 i : ℕ) := by
  simpa [toSym] using RowFibers.rowCount (fun i => (S.1 i : ℕ)) i

/-- Recovering counts from the actual repeated-mode multiset recovers the entire occupation. -/
theorem ofTo {m n : ℕ} (S : FockOccupation m n) : ofSym (toSym S) = S := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact toSymCount S i

/-- Reconstructing the actual repeated-mode multiset from its counts recovers every multiset. -/
theorem toOf {m n : ℕ} (s : Sym (Fin m) n) : toSym (ofSym s) = s := by
  apply Sym.coe_injective
  apply Multiset.ext.mpr
  intro i
  exact toSymCount (ofSym s) i

/-- The actual bounded occupation type is equivalent to the fixed-size multiset type. -/
def occEquiv (m n : ℕ) : FockOccupation m n ≃ Sym (Fin m) n where
  toFun := toSym
  invFun := ofSym
  left_inv := ofTo
  right_inv := toOf

/-- Stars and bars computes the cardinality of the actual occupation type in every dimension. -/
theorem occCard (m n : ℕ) : Fintype.card (FockOccupation m n) = (m+n-1).choose n := by
  rw [Fintype.card_congr (occEquiv m n), Sym.card_sym_eq_choose]
  simp

end Qatlib.Concepts.BosonFock.BosonOperators.FockCard
