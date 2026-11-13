/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.Section6AncillaLowerBoundStat
import Qatlib.Concepts.SearchStopping.KnownCount.Section6LabelSpaceLowerBoundAfas

/-!
# Search lower bound with an ancilla

`section6AncillaLowerBound` proves the fixed-space phase-query lower bound for an address
register tensored with a nonempty finite workspace. The target event contains every workspace
value paired with the marked address.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `section6AncillaLowerBound`: Singleton phase-oracle search on an address register with any
  nonempty finite workspace has fixed-space query lower bound ⌊sin(π/8)√N⌋ at success threshold
  1/2, where N is the address cardinality.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.SearchStopping.KnownCount

/-- Singleton phase-oracle search on an address register with any nonempty finite workspace has
fixed-space query lower bound ⌊sin(π/8)√N⌋ at success threshold 1/2, where N is the address
cardinality. -/
theorem section6AncillaLowerBound : Section6AncillaLowerBound := by
  intro I W _ _ _ _ _
  apply section6LabelSpaceLowerBound I (I × W) Prod.fst
  intro i
  exact ⟨(i, Classical.choice (inferInstance : Nonempty W)), rfl⟩

end Qatlib.Concepts.SearchStopping.KnownCount
