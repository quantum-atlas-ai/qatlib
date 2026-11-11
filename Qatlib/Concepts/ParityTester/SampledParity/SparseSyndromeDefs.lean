/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Mathlib.Data.List.FinRange

/-!
# Sparse parity scans and read accounting

This module represents parity checks by lists of coordinate indices and defines their execution
through `scanRow` and `scanRows`. `parityMatrix` reduces each coordinate's multiplicity modulo
two, whereas `columnReads` retains its full occurrence count for read accounting. The relation
between parity matrices and syndromes provides coding-theoretic context in [NielsenChuang2010].

## Main statements

* `scanRow` returns a row parity together with its coordinate read list.
* `scanRows` executes all rows and concatenates their read logs.
* `parityMatrix` encodes row multiplicities over `ZMod 2`.
* `columnReads` counts every occurrence of a coordinate in the flattened row list.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.ParityTester.SampledParity

/-- Sums the selected coordinates of `x` in `ZMod 2` and returns the row list as the coordinate
read log. Repeated indices contribute repeated additions and reads. -/
def scanRow {n : ℕ} (x : Fin n → ZMod 2) :
    List (Fin n) → ZMod 2 × List (Fin n)
  | [] => (0, [])
  | i :: rest =>
      let r := scanRow x rest
      (x i + r.1, i :: r.2)

/-- Scans each row in order, returning the list of parity sums and the concatenation of all row
read logs. -/
def scanRows {n : ℕ} (x : Fin n → ZMod 2) :
    List (List (Fin n)) → List (ZMod 2) × List (Fin n)
  | [] => ([], [])
  | row :: rows =>
      let a := scanRow x row
      let r := scanRows x rows
      (a.1 :: r.1, a.2 ++ r.2)

/-- Forms the matrix over `ZMod 2` whose entry counts a coordinate's occurrences in the
indicated row modulo two. -/
def parityMatrix {n : ℕ} (rows : List (List (Fin n))) :
    Matrix (Fin rows.length) (Fin n) (ZMod 2) :=
  fun r i => ((rows.get r).count i : ZMod 2)

/-- Counts the total occurrences of coordinate `i` in the flattened row list, retaining
multiplicity as a natural number. -/
def columnReads {n : ℕ} (rows : List (List (Fin n))) (i : Fin n) : ℕ :=
  rows.flatten.count i

end Qatlib.Concepts.ParityTester.SampledParity
