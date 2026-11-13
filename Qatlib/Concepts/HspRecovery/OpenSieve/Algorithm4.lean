/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt
import Qatlib.Concepts.HspRecovery.RecordExtract.SummandExtractionDihe

/-!
# Summand extraction and dihedral transport endpoints

This module provides the summand-extraction, representation-transport, and dihedral-instance
statements used for Algorithm 4 in the sieve framework of [Kuperberg2005]. Each theorem exposes
the corresponding imported endpoint for downstream use.

## Main statements

* `algorithm4_summand_extraction`: the source summand-extraction specification.
* `algorithm4_representation_transport`: the representation-transport target for nonzero
  modulus.
* `algorithm4_dihedral_instance_endpoint`: the dihedral endpoint obligation when `p ≤ 1`.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm4

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.OpenSieve

/-- Establishes the `SourceSummandExtraction` specification used by the representation sieve
associated with Algorithm 4 of [Kuperberg2005]. -/
theorem algorithm4_summand_extraction : SourceSummandExtraction :=
  sourceSummandExtraction

/-- Establishes the representation-transport target `RepTransportTarget N` for every nonzero
modulus `N`. -/
theorem algorithm4_representation_transport (N : ℕ) [NeZero N] :
    RepTransportTarget N :=
  (clause13_endpoint N).1

/-- Establishes `clause14_general_endpoint_obligation N p` for a nonzero modulus `N` and any
real parameter `p ≤ 1`. -/
theorem algorithm4_dihedral_instance_endpoint (N : ℕ) [NeZero N] (p : ℝ)
    (hp : p ≤ 1) :
    clause14_general_endpoint_obligation N p :=
  clause14_general_endpoint_discharged N p hp

end Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm4
