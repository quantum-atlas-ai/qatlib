/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ParityTester.SampledParity.SparseSyndromeDefs

set_option autoImplicit false
namespace Qatlib.Concepts.ParityTester.SampledParity
open Qatlib.Concepts.ParityTester.SampledParity
def runSchedule {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2) :
    List (Fin rows.length) → List (ZMod 2) × List (Fin n)
  | [] => ([], [])
  | i :: schedule =>
      let a := scanRow x (rows.get i)
      let r := runSchedule rows x schedule
      (a.1 :: r.1, a.2 ++ r.2)

def passes {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2)
    (schedule : List (Fin rows.length)) : Bool :=
  ((runSchedule rows x schedule).1).all (fun b => decide (b = 0))

def missMass {n : ℕ} (rows : List (List (Fin n))) (x : Fin n → ZMod 2) (t : ℕ) : ℚ :=
  ((Finset.univ.filter fun samples : Fin t → Fin rows.length =>
      passes rows x (List.ofFn samples) = true).card : ℚ) / (rows.length : ℚ) ^ t

end Qatlib.Concepts.ParityTester.SampledParity
