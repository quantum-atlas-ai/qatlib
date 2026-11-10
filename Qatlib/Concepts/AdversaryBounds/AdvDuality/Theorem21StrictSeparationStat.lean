/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.OptimizedAdv
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21RealizedWitnessStat
import Qatlib.Concepts.AdversaryBounds.AdvDuality.Theorem21Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdversaryBounds.AdvDuality.NegativeWeightsMakeAdversariesStronger2006
open Qatlib.Concepts.AdversaryBounds.OptimizedAdv

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Finset

def Theorem21StrictSeparation : Prop :=
  advNonneg (fun w => w) kushilevitzMonotone (fun _ => 1) ≤ ENNReal.ofReal 3 ∧
    ENNReal.ofReal (2 + 3 * Real.sqrt 5 / 5) ≤
      advPlus (fun w => w) kushilevitzMonotone (fun _ => 1)

end Qatlib.Concepts.AdversaryBounds.AdvDuality
