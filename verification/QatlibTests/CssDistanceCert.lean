/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.DistCert.Branch
public import QatlibTests.BinaryRank

@[expose] public section

/-! # Exact distance via branch certificates -/

namespace QatlibTests.CssDistanceCert

set_option autoImplicit false
set_option warningAsError true

open QatlibTests.BinaryRank
open Qatlib.Concepts.CodeCert.DistCert
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

/-- A single Z on the repetition code is undetectable and outside the stabilizer row spaces. -/
def logicalZ : PauliLabel (Fin 3) := (0, fun i => if i = 0 then 1 else 0)

/-- The zero-labelled branch continues, while every nonzero child exceeds the budget. -/
def excludeBelowOne : List (Fin 3) → Branch (Fin 3) (Fin 0) (Fin 3)
  | [] => .point
  | i :: is => .split i fun p => if p = 0 then excludeBelowOne is else .heavy

/-- The checker certifies the exact distance using the actual repetition check matrices. -/
theorem repetitionDist : cssDistance repetitionCss = 1 :=
  distance_sound repetitionCss 1 logicalZ (excludeBelowOne [0, 1, 2]) (by decide +kernel)

/-- The weight-one X label already violates a completely assigned Z check row. -/
theorem detectedBranch :
    checkBranch repetitionCss 2 (fun i => some (if i = 0 then 1 else 0, 0))
      (.closeZ 0) = true := by
  decide +kernel

/-- A partially assigned point cannot be passed off as a certificate for all extensions. -/
theorem rejectPoint :
    checkBranch repetitionCss 1 (fun _ => none) .point = false := by
  decide +kernel

end QatlibTests.CssDistanceCert
