/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryFourBitWitness
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Concepts.SignedWeights.Representations.Examples

open Qatlib
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

theorem theorem20_four_bit_bound :
    ENNReal.ofReal (2.5135 : ℝ) ≤
      advPmValue (fun w : FourBitWord => w) ambainisSorted4 := by
  have hdec : (2.5135 : ℝ) = 25135 / 10000 := by norm_num
  rw [hdec]
  exact ambainis_four_bit_printed_bound

end

end Qatlib.Concepts.SignedWeights.Representations.Examples
