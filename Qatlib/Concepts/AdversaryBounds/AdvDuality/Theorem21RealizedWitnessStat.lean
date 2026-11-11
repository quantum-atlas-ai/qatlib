/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvWitness
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21Defs

/-!
# Statement of the Kushilevitz witness bounds

`Theorem21RealizedWitness` states the four properties needed of the explicit adversary matrix:
Hermiticity, zero entries on equal-output pairs, filter bound at most one, and operator norm at
least `2 + 3 * sqrt 5 / 5`.

These properties encode the negative-weight witness associated with Theorem 21 of
[HoyerLeeSpalek2007].

## Main statements

* `Theorem21RealizedWitness`: states the structural and norm conditions on the explicit witness.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The conjunction asserting that `kushilevitzGammaW` is Hermitian, vanishes on equal-output
pairs, has filter bound at most one, and has norm at least `2 + 3 * sqrt 5 / 5`. See [Hoyer,
Lee, and Spalek, Theorem 21][HoyerLeeSpalek2007]. -/
def Theorem21RealizedWitness : Prop :=
  kushilevitzGammaW.IsHermitian ∧
    (∀ x y : Fin 20, kushilevitzFunW x = kushilevitzFunW y → kushilevitzGammaW x y = 0) ∧
    advFilterBound kushilevitzInputW kushilevitzGammaW ≤ 1 ∧
    (2 + 3 * Real.sqrt 5 / 5) ≤ ‖kushilevitzGammaW‖

end Qatlib.Concepts.AdversaryBounds.AdvDuality
