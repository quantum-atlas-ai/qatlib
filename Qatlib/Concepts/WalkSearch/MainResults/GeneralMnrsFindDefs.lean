/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DetectionExecutionDefs

/-!
# Decoding and success for marked vertices

`generalFindDecoder` filters an observed vertex through a finite marked set.
`generalFindSuccess` sums the squared amplitude norms on that set, providing the success
functional used by the general walk search account. For background on search via quantum walks,
see [MagniezNayakRolandSantha2011].

## Main statements

* `generalFindDecoder`: Return `some u` if `u` belongs to the marked set `S`, and return `none`
  otherwise.
* `generalFindSuccess`: The sum of squared amplitude norms of `ψ` over the marked vertices in
  `S`.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Concepts.WalkSearch.MainResults
namespace GeneralMnrsFindDefs

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Return `some u` if `u` belongs to the marked set `S`, and return `none` otherwise. -/
noncomputable def generalFindDecoder {V : ℕ} (S : Finset (GeneralVertex V))
    (u : GeneralVertex V) : Option (GeneralVertex V) :=
  if u ∈ S then some u else none

/-- The sum of squared amplitude norms of `ψ` over the marked vertices in `S`. -/
noncomputable def generalFindSuccess {V : ℕ} (S : Finset (GeneralVertex V))
    (ψ : QState (GeneralVertex V)) : ℝ :=
  ∑ u ∈ S, ‖ψ u‖ ^ 2

end GeneralMnrsFindDefs
end Qatlib.Concepts.WalkSearch.MainResults
