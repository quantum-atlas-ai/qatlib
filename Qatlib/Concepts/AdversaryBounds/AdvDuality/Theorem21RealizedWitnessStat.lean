/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvWitness
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def Theorem21RealizedWitness : Prop :=
  kushilevitzGammaW.IsHermitian ∧
    (∀ x y : Fin 20, kushilevitzFunW x = kushilevitzFunW y → kushilevitzGammaW x y = 0) ∧
    advFilterBound kushilevitzInputW kushilevitzGammaW ≤ 1 ∧
    (2 + 3 * Real.sqrt 5 / 5) ≤ ‖kushilevitzGammaW‖

end Qatlib.Concepts.AdversaryBounds.AdvDuality
