/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvWitness

/-!
# The Kushilevitz adversary witness

This module specifies twenty six-bit inputs, their two output classes, and the
distance-dependent weights of `kushilevitzGammaW`. The witness assigns zero to equal-output
pairs and one of three real weights to different-output pairs according to their Hamming
distance.

`kushilevitzMonotone` extends the selected weight-three values to a total six-bit Boolean
function by assigning false below weight three and true above it. These are the data for the
negative-weight separation associated with Theorem 21 of [HoyerLeeSpalek2007].

## Main statements

* `kushilevitzGammaW`: defines the explicit twenty-by-twenty adversary matrix.
* `kushilevitzDist`: counts differing coordinates of the selected inputs.
* `kushilevitzMonotone`: defines the total six-bit extension used in the separation.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

/-- The explicit family of twenty six-bit inputs used by the Kushilevitz adversary witness. -/
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

/-- The output labeling of the witness inputs, false on indices below ten and true on indices at
least ten. -/
def kushilevitzFunW (x : Fin 20) : Bool := decide (10 ≤ x.val)

/-- The real witness weight `(1 + sqrt 5) / 5`. -/
noncomputable def kushilevitzWeightA : ℝ := (1 + Real.sqrt 5) / 5

/-- The real witness weight `(1 - sqrt 5) / 5`. -/
noncomputable def kushilevitzWeightB : ℝ := (1 - Real.sqrt 5) / 5

/-- The real witness weight `1 / 5`. -/
noncomputable def kushilevitzWeightC : ℝ := 1 / 5

/-- The distance-dependent weight, equal to `kushilevitzWeightA` at distance two,
`kushilevitzWeightB` at distance four, and `kushilevitzWeightC` otherwise. -/
noncomputable def kushilevitzWeight (d : ℕ) : ℝ :=
  if d = 2 then kushilevitzWeightA else if d = 4 then kushilevitzWeightB else kushilevitzWeightC

/-- The Hamming distance between two selected six-bit witness inputs. -/
noncomputable def kushilevitzDist (x y : Fin 20) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 => kushilevitzInputW x i ≠ kushilevitzInputW y i).card

/-- The complex adversary matrix with zero entries on equal-output pairs and distance-dependent
real weights on different-output pairs, as used for [Hoyer, Lee, and Spalek, Theorem
21][HoyerLeeSpalek2007]. -/
noncomputable def kushilevitzGammaW : Matrix (Fin 20) (Fin 20) ℂ :=
  fun x y =>
    if kushilevitzFunW x = kushilevitzFunW y then 0
    else (kushilevitzWeight (kushilevitzDist x y) : ℂ)
end Qatlib.Concepts.AdversaryBounds.AdvDuality

open Finset
namespace Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006

/-- Test whether a six-bit word is one of the ten selected witness inputs labeled true. -/
noncomputable def kushilevitzIsOneWord (w : Fin 6 → Bool) : Bool :=
  decide (∃ x : Fin 20, 10 ≤ x.val ∧ kushilevitzInputW x = w)

/-- The Hamming weight of a six-bit Boolean word. -/
def kushilevitzWeightOf (w : Fin 6 → Bool) : ℕ :=
  (univ.filter (fun i => w i)).card

/-- The total six-bit Boolean function that is true above Hamming weight three and, at weight
three, exactly on the selected true-labeled witness words. -/
noncomputable def kushilevitzMonotone (w : Fin 6 → Bool) : Bool :=
  if 4 ≤ kushilevitzWeightOf w then true
  else if kushilevitzWeightOf w = 3 then kushilevitzIsOneWord w
  else false
end Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
