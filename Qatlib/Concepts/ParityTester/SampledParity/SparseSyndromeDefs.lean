/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Mathlib.Data.List.FinRange

set_option autoImplicit false
namespace Qatlib.Concepts.ParityTester.SampledParity

def scanRow {n : ℕ} (x : Fin n → ZMod 2) :
    List (Fin n) → ZMod 2 × List (Fin n)
  | [] => (0, [])
  | i :: rest =>
      let r := scanRow x rest
      (x i + r.1, i :: r.2)

def scanRows {n : ℕ} (x : Fin n → ZMod 2) :
    List (List (Fin n)) → List (ZMod 2) × List (Fin n)
  | [] => ([], [])
  | row :: rows =>
      let a := scanRow x row
      let r := scanRows x rows
      (a.1 :: r.1, a.2 ++ r.2)

def parityMatrix {n : ℕ} (rows : List (List (Fin n))) :
    Matrix (Fin rows.length) (Fin n) (ZMod 2) :=
  fun r i => ((rows.get r).count i : ZMod 2)

def columnReads {n : ℕ} (rows : List (List (Fin n))) (i : Fin n) : ℕ :=
  rows.flatten.count i

end Qatlib.Concepts.ParityTester.SampledParity
