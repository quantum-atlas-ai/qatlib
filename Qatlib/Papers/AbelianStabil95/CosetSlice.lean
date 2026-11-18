/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle

@[expose] public section

/-!
# Abelian-stabilizer first slice: the public additive-oracle query resource bound

The first auditable slice of the AbelianStabil95 line: the
public cyclic-recovery additive-oracle layer, restated as the slice's single
dependency point for the sampling-oracle side of the stabilizer pipeline. The
public layer's query resource statement — one oracle query counts one query and
zero gates — is reused as proved; this slice does not construct the full
hidden-subgroup sampler, the Fourier readout, or the `2L + m` space budget.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery

namespace Qatlib.Papers.AbelianStabil95.CosetSlice

variable {I R : Type*}

/-- The public additive-oracle query resource statement, restated as this line's
dependency point. -/
theorem addOracleQueryReused :
    QueryCount ([Step.query] : Circuit (I × R)) = 1 ∧
      GateCount ([Step.query] : Circuit (I × R)) = 0 :=
  addOracle_query_resources

end Qatlib.Papers.AbelianStabil95.CosetSlice
