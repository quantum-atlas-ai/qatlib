/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows

set_option backward.isDefEq.respectTransparency false

/-!
# SourceMainResults — lower bound on initial state preparation

Low--Su, fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

Theorem 3 (p.42, Eqs. (172)–(173)): for every `0 < p < 1` there is a linear
system with `‖A⁻¹ b‖² / ‖A⁻¹‖² = Θ(p)` such that any algorithm preparing the
normalized solution to small constant accuracy needs `Ω(1/√p)` queries to the
state-preparation oracle `O_b`.

The frozen library contains the *corrected explicit-instance* form: an
explicit Grover instance with `d ≥ 150` dimensions, oracle accuracy
`ε ≤ 1/100`, and any unitary circuit with quantum state-preparation oracle
satisfies `d ≤ 64 (QueryCount C)²`, whose ratio `p_d = (5d² - 8d + 4)/d³` is
`Θ(1/d)` for `d ≥ 8`. The frozen contract
`InitialStatePreparationLowerBoundSubgoalCorrected` is proved in Frozen v2.0.2
by `initialStatePreparationLowerBoundSubgoalCorrected`.

Boundary: the frozen form is the explicit Grover family, not the paper's
`∀ 0 < p < 1` abstract parameterized family; see its `covered_by` note. The
implication "lower bound ⇒ QLS upper bound" is not part of this file.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.QLSStatePrep24.PrepLowerBound

/-- Fixed arXiv:2410.18178v2, Theorem 3 (p.42, Eqs. (172)–(173)): the initial
state preparation query lower bound on the explicit Grover instance. The frozen
contract states that for any finite instance of dimension `≥ 150`, oracle
accuracy `≤ 1/100`, normalized product initial state and unitary circuit whose
output is within `ε` of the solution target, the dimension is bounded by
`64 (QueryCount C)²`, giving the `Ω(1/√p)` lower bound with
`p = (5d² - 8d + 4)/d³ = Θ(1/d)`. Proved in Frozen v2.0.2 by
`initialStatePreparationLowerBoundSubgoalCorrected`. -/
theorem theorem3_initial_state_preparation_lower_bound :
    InitialStatePreparationLowerBoundSubgoalCorrected :=
  initialStatePreparationLowerBoundSubgoalCorrected

end Qatlib.Papers.QLSStatePrep24.PrepLowerBound
