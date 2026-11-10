/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversary
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

theorem theorem21_kushilevitz_bound :
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPmValue kushilevitzInputW kushilevitzFunW :=
  advPmValue_kushilevitz_ge

end

end Qatlib.Concepts.SignedWeights.Representations.Examples
