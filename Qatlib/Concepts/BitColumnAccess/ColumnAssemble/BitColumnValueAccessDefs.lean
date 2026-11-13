/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SharedAncilla.AncillaProduct.UnitaryFamilyWord
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Value-query and bit-column word definitions

This module defines value-XOR and individual bit-column updates on an address and a Boolean
register, together with their matrices. The word types `ValueStep` and `ColumnStep` combine
query operations with known matrices, and `expand` replaces each value query by all b column
queries. These definitions provide explicit finite oracle semantics for the quantum input-access
setting discussed in [GilyenSuLowWiebe2019].

## Main statements

* `columnWord`: the matrix obtained by applying all bit-column updates in index order.
* `evalValue`, `evalColumns`: matrix semantics of the two word types.
* `valueQueries`, `columnQueries`: query-operation counts.
* `valueGates`, `columnGates`: counts of known-matrix steps.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.BitColumnAccess.ColumnAssemble
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib

/-- Preserves the address and XORs the entire function value at that address into the target
register. -/
def valueUpdate {N b : ℕ} (f : Fin N→Reg b) (x : Fin N×Reg b) : Fin N×Reg b :=
  (x.1,fun j => x.2 j ^^ f x.1 j)
/-- Preserves the address and XORs the jth bit of its function value into target bit j, leaving
all other target bits unchanged. -/
def columnUpdate {N b : ℕ} (f : Fin N→Reg b) (j : Fin b) (x : Fin N×Reg b) : Fin N×Reg b :=
  (x.1,fun k => if k=j then x.2 k ^^ f x.1 j else x.2 k)
/-- The matrix associated with the full value-XOR update on address-register pairs. -/
def valueMatrix {N b : ℕ} (f : Fin N→Reg b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
    permMatrix (valueUpdate f)
/-- The matrix associated with a single bit-column XOR update on address-register pairs. -/
def columnMatrix {N b : ℕ} (f : Fin N→Reg b) (j : Fin b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
    permMatrix (columnUpdate f j)
/-- The list of all b bit-column indices in increasing order. -/
def columns (b : ℕ) : List (Fin b) := List.ofFn id
/-- The matrix product implementing all bit-column operations in increasing index order, with
later operations multiplied on the left. -/
noncomputable def columnWord {N b : ℕ} (f : Fin N→Reg b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  ((columns b).map (columnMatrix f)).reverse.prod
/-- A step in a value-access word, consisting of either a specified known matrix or a full value
query. -/
inductive ValueStep (N b : ℕ) where
  | known : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ → ValueStep N b
  | query : ValueStep N b
/-- A step in a bit-column-access word, consisting of either a specified known matrix or a query
to a specified column. -/
inductive ColumnStep (N b : ℕ) where
  | known : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ → ColumnStep N b
  | query : Fin b → ColumnStep N b

/-- Replaces each full value query by a query to every bit column in order and retains each
known-matrix step. -/
def expand {N b : ℕ} (W : List (ValueStep N b)) : List (ColumnStep N b) := W.flatMap fun s =>
  match s with | .known A => [.known A] | .query => (columns b).map ColumnStep.query
/-- The matrix obtained by applying a value-access word from left to right, interpreting queries
as `valueMatrix`. -/
noncomputable def evalValue {N b : ℕ} (f : Fin N→Reg b) (W : List (ValueStep N b)) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  (W.map (fun s => match s with | .known A => A | .query => valueMatrix f)).reverse.prod
/-- The matrix obtained by applying a column-access word from left to right, interpreting each
query as its `columnMatrix`. -/
noncomputable def evalColumns {N b : ℕ} (f : Fin N→Reg b) (W : List (ColumnStep N b)) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  (W.map (fun s => match s with | .known A => A | .query j => columnMatrix f j)).reverse.prod

/-- The number of full value-query steps in a value-access word. -/
def valueQueries {N b : ℕ} (W : List (ValueStep N b)) : ℕ :=
    W.countP (fun s => match s with | .query => true | _ => false)
/-- The number of bit-column query steps in a column-access word. -/
def columnQueries {N b : ℕ} (W : List (ColumnStep N b)) : ℕ :=
    W.countP (fun s => match s with | .query _ => true | _ => false)
/-- The number of known-matrix steps in a value-access word, computed as its length minus its
query count. -/
def valueGates {N b : ℕ} (W : List (ValueStep N b)) : ℕ := W.length-valueQueries W
/-- The number of known-matrix steps in a column-access word, computed as its length minus its
query count. -/
def columnGates {N b : ℕ} (W : List (ColumnStep N b)) : ℕ := W.length-columnQueries W

end Qatlib.Concepts.BitColumnAccess.ColumnAssemble
