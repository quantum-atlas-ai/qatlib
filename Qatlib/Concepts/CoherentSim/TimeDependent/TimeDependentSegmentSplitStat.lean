/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.CoherentSim.TimeDependent

def TimeDependentSegmentSplit : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ) (t : ℝ) (r : ℕ),
    Continuous H → 0 ≤ t → 0 < r →
    orderedEvolution (fun u => Complex.I • H u) 0 t =
      ((List.ofFn (fun k : Fin r =>
        orderedEvolution (fun u => Complex.I • H u)
          ((k.val : ℝ) * t / (r : ℝ))
          (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ)))).reverse).prod

end Qatlib.Concepts.CoherentSim.TimeDependent
