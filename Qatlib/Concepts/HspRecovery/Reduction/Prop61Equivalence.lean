/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsDihe

/-!
# Oracle reduction equivalence

This module provides `prop61_equivalence`, exposing the established `SourceOracleReductions`
specification under the name corresponding to Proposition 6.1 of [Kuperberg2005]. The result
connects the source-level oracle reductions used in hidden-reflection recovery.

## Main statements

* `prop61_equivalence`: the combined source oracle reduction specification holds.

## References

* [Kuperberg, Proposition 6.1][Kuperberg2005]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore.Prop61Equivalence

open Qatlib.Concepts.HspRecovery.ReductionCore

/-- The `SourceOracleReductions` specification holds, exposing the oracle reductions
corresponding to [Kuperberg, Proposition 6.1][Kuperberg2005]. -/
theorem prop61_equivalence : SourceOracleReductions :=
  sourceOracleReductions

end Qatlib.Concepts.HspRecovery.ReductionCore.Prop61Equivalence
