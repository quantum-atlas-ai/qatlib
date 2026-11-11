/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MeasureStats.PauliShadows.PauliShadowUnbiasedRestrictedStat

/-!
# Unbiased single-qubit Pauli shadows

`pauliShadowUnbiasedRestrictedSubgoal` proves the single-qubit reconstruction specification
`PauliShadowUnbiasedRestrictedSubgoal`. Averaging inverse-measurement snapshots over uniformly
selected Pauli axes and their Born outcomes recovers the density operator. See
[HuangKuengPreskill2020].

## Main statements

* `pauliShadowUnbiasedRestrictedSubgoal`: unbiasedness of the restricted Pauli shadow.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Concepts.ChannelTheory.Stinespring

namespace Qatlib.Concepts.MeasureStats.PauliShadows

open Qatlib

/-- The single-qubit Pauli shadow, averaged over uniformly selected axes and Born outcomes,
reconstructs every density operator. -/
theorem pauliShadowUnbiasedRestrictedSubgoal : PauliShadowUnbiasedRestrictedSubgoal :=
  fun ρ hρ => Qatlib.Concepts.ChannelTheory.Stinespring.pauliShadow_unbiased ρ hρ

end Qatlib.Concepts.MeasureStats.PauliShadows
