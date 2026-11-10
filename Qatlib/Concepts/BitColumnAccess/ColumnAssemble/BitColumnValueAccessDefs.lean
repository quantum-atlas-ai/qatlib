/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SharedAncilla.AncillaProduct.UnitaryFamilyWord
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.BitColumnAccess.ColumnAssemble
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib

def valueUpdate {N b : ℕ} (f : Fin N→Reg b) (x : Fin N×Reg b) : Fin N×Reg b :=
  (x.1,fun j => x.2 j ^^ f x.1 j)
def columnUpdate {N b : ℕ} (f : Fin N→Reg b) (j : Fin b) (x : Fin N×Reg b) : Fin N×Reg b :=
  (x.1,fun k => if k=j then x.2 k ^^ f x.1 j else x.2 k)
def valueMatrix {N b : ℕ} (f : Fin N→Reg b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
    permMatrix (valueUpdate f)
def columnMatrix {N b : ℕ} (f : Fin N→Reg b) (j : Fin b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
    permMatrix (columnUpdate f j)
def columns (b : ℕ) : List (Fin b) := List.ofFn id
noncomputable def columnWord {N b : ℕ} (f : Fin N→Reg b) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  ((columns b).map (columnMatrix f)).reverse.prod
inductive ValueStep (N b : ℕ) where
  | known : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ → ValueStep N b
  | query : ValueStep N b
inductive ColumnStep (N b : ℕ) where
  | known : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ → ColumnStep N b
  | query : Fin b → ColumnStep N b

def expand {N b : ℕ} (W : List (ValueStep N b)) : List (ColumnStep N b) := W.flatMap fun s =>
  match s with | .known A => [.known A] | .query => (columns b).map ColumnStep.query
noncomputable def evalValue {N b : ℕ} (f : Fin N→Reg b) (W : List (ValueStep N b)) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  (W.map (fun s => match s with | .known A => A | .query => valueMatrix f)).reverse.prod
noncomputable def evalColumns {N b : ℕ} (f : Fin N→Reg b) (W : List (ColumnStep N b)) : Matrix (Fin N×Reg b) (Fin N×Reg b) ℂ :=
  (W.map (fun s => match s with | .known A => A | .query j => columnMatrix f j)).reverse.prod

def valueQueries {N b : ℕ} (W : List (ValueStep N b)) : ℕ :=
    W.countP (fun s => match s with | .query => true | _ => false)
def columnQueries {N b : ℕ} (W : List (ColumnStep N b)) : ℕ :=
    W.countP (fun s => match s with | .query _ => true | _ => false)
def valueGates {N b : ℕ} (W : List (ValueStep N b)) : ℕ := W.length-valueQueries W
def columnGates {N b : ℕ} (W : List (ColumnStep N b)) : ℕ := W.length-columnQueries W

end Qatlib.Concepts.BitColumnAccess.ColumnAssemble
