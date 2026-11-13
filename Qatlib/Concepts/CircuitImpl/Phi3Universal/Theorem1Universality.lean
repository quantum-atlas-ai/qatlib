/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.Phi3UniversalityTheorem1Quan

/-!
# Universality of the Φ₃ gate family

This module exposes `theorem1_phi3_universality`, the packaged Φ₃ universality statement
associated with Theorem 1 of [Yao1993]. The result concerns exact circuit realization of unitary
transformations with an exponential gate bound and a linear ancillary-wire bound.

## Main statements

* `theorem1_phi3_universality`: the proposition `Phi3UniversalityTheorem1`.

## References

* [Yao, 1993, Theorem 1][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal.Theorem1Universality

open Qatlib.Concepts.CircuitImpl.Phi3Universal

/-- The Φ₃ universality statement of [Yao, Theorem 1][Yao1993], packaged as
`Phi3UniversalityTheorem1`. -/
theorem theorem1_phi3_universality : Phi3UniversalityTheorem1 :=
  phi3UniversalityTheorem1

end Qatlib.Concepts.CircuitImpl.Phi3Universal.Theorem1Universality
