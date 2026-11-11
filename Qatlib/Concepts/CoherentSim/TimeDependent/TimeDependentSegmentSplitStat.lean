/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Time segment decomposition specification

`TimeDependentSegmentSplit` states the decomposition of ordered evolution for the generator
`Complex.I • H` into equally spaced time segments. Reversing the segment list places the later
evolutions on the left in the matrix product.

The mathematical context is discussed in [BerryEtAl2015Taylor].

## Main statements

* `TimeDependentSegmentSplit`: The equal segment product identity for continuous Hamiltonians.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.CoherentSim.TimeDependent

/-- The statement that, for continuous `H`, nonnegative `t` and positive `r`, ordered evolution
on [0, t] is the reverse list product of the evolutions on the `r` equal subintervals. -/
def TimeDependentSegmentSplit : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (H : ℝ → Matrix I I ℂ) (t : ℝ) (r : ℕ),
    Continuous H → 0 ≤ t → 0 < r →
    orderedEvolution (fun u => Complex.I • H u) 0 t =
      ((List.ofFn (fun k : Fin r =>
        orderedEvolution (fun u => Complex.I • H u)
          ((k.val : ℝ) * t / (r : ℝ))
          (((k.val + 1 : ℕ) : ℝ) * t / (r : ℝ)))).reverse).prod

end Qatlib.Concepts.CoherentSim.TimeDependent
