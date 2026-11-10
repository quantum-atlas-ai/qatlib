/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvWitness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable def kushilevitzInputW : Fin 20 → Fin 6 → Bool :=
  ![(![true, true, true, false, false, false] : Fin 6 → Bool),
    ![false, true, true, true, false, false],
    ![false, false, true, true, true, false],
    ![true, false, false, true, true, false],
    ![true, true, false, false, true, false],
    ![true, false, true, false, false, true],
    ![false, true, false, true, false, true],
    ![false, false, true, false, true, true],
    ![true, false, false, true, false, true],
    ![false, true, false, false, true, true],
    ![false, false, false, true, true, true],
    ![true, false, false, false, true, true],
    ![true, true, false, false, false, true],
    ![false, true, true, false, false, true],
    ![false, false, true, true, false, true],
    ![false, true, false, true, true, false],
    ![true, false, true, false, true, false],
    ![true, true, false, true, false, false],
    ![false, true, true, false, true, false],
    ![true, false, true, true, false, false]]

def kushilevitzFunW (x : Fin 20) : Bool := decide (10 ≤ x.val)

noncomputable def kushilevitzWeightA : ℝ := (1 + Real.sqrt 5) / 5

noncomputable def kushilevitzWeightB : ℝ := (1 - Real.sqrt 5) / 5

noncomputable def kushilevitzWeightC : ℝ := 1 / 5

noncomputable def kushilevitzWeight (d : ℕ) : ℝ :=
  if d = 2 then kushilevitzWeightA else if d = 4 then kushilevitzWeightB else kushilevitzWeightC

noncomputable def kushilevitzDist (x y : Fin 20) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 => kushilevitzInputW x i ≠ kushilevitzInputW y i).card

noncomputable def kushilevitzGammaW : Matrix (Fin 20) (Fin 20) ℂ :=
  fun x y =>
    if kushilevitzFunW x = kushilevitzFunW y then 0
    else (kushilevitzWeight (kushilevitzDist x y) : ℂ)
end Qatlib.Concepts.AdversaryBounds.AdvDuality

open Finset
namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006

noncomputable def kushilevitzIsOneWord (w : Fin 6 → Bool) : Bool :=
  decide (∃ x : Fin 20, 10 ≤ x.val ∧ kushilevitzInputW x = w)

def kushilevitzWeightOf (w : Fin 6 → Bool) : ℕ :=
  (univ.filter (fun i => w i)).card

noncomputable def kushilevitzMonotone (w : Fin 6 → Bool) : Bool :=
  if 4 ≤ kushilevitzWeightOf w then true
  else if kushilevitzWeightOf w = 3 then kushilevitzIsOneWord w
  else false
end Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
