/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ParityTester.SampledParity.SparseSyndromeDefs

/-!
# Sample schedules for parity testing

This module defines `runSchedule`, which executes a list of parity-row indices while recording
both check values and coordinate reads. `passes` accepts when every returned value is zero, and
`missMass` counts accepting length-`t` index sequences divided by the total sequence count. The
syndrome interpretation of parity checks is standard background in [NielsenChuang2010].

## Main statements

* `runSchedule` preserves the chosen row order and records repeated reads.
* `passes` tests whether all scheduled parity values vanish.
* `missMass` defines the rational acceptance mass used for uniform sampling with replacement
  when the row list is nonempty.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.ParityTester.SampledParity
open Qatlib.Concepts.ParityTester.SampledParity
/-- Executes the rows selected by a list of indices and returns their parity values together
with the concatenated coordinate read log. Both outputs retain the schedule order and
repeated occurrences. -/
def runSchedule {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2) :
    List (Fin rows.length) → List (ZMod 2) × List (Fin n)
  | [] => ([], [])
  | i :: schedule =>
      let a := scanRow x (rows.get i)
      let r := runSchedule rows x schedule
      (a.1 :: r.1, a.2 ++ r.2)

/-- Returns true exactly when every parity value produced by the scheduled scans is zero. -/
def passes {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2)
    (schedule : List (Fin rows.length)) : Bool :=
  ((runSchedule rows x schedule).1).all (fun b => decide (b = 0))

/-- Defines the rational count of accepting length-`t` row-index sequences divided by
`rows.length ^ t`. For a nonempty row list this is the acceptance probability under
independent uniform row sampling with replacement. -/
def missMass {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2) (t : ℕ) : ℚ :=
  ((Finset.univ.filter fun samples : Fin t → Fin rows.length =>
      passes rows x (List.ofFn samples) = true).card : ℚ) / (rows.length : ℚ) ^ t

end Qatlib.Concepts.ParityTester.SampledParity
