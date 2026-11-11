/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.LCUContractionSubgoalStat

/-!
# Prepared LCU workspace corner identity

This module proves `LCUContractionSubgoal` by applying the general LCU corner theorem to a
prepared workspace. For nonnegative weights summing to one, the selected ancilla corner acts as
the corresponding weighted sum of system matrices, providing the workspace identity used for the
constructions of [ChildsWiebe2012].

## Main statements

* `lcuContractionSubgoal`: proves the prepared workspace corner identity.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

set_option warningAsError false

open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

open Qatlib

/-- A prepared LCU workspace with nonnegative weights summing to one has selected ancilla corner
`(∑ j, w j • U j) *ᵥ ψ`, establishing `LCUContractionSubgoal`. -/
theorem lcuContractionSubgoal : LCUContractionSubgoal :=
  fun J I _ _ _ _ U w hw _ P j0 hP ψ => Qatlib.Concepts.BlockEncoding.LinearCombination.lcu_corner_apply U hw hP ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
