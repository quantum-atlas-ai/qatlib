/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# General record and recovery interfaces

This module exposes the general record law and collision-based shift recovery endpoints used by
the Algorithm 2 interface in the dihedral hidden-subgroup development [Kuperberg2005]. It
supplies a success-one shift endpoint for positive collision widths whose square covers the
modulus, together with the chosen-width query bound.

## Main statements

* `algorithm2_record_law`: the general record extraction specification.
* `algorithm2_general_recovery`: collision recovery and its chosen-width query bound.
* `algorithm2_general_endpoint_obligation`: discharge of the general endpoint obligation for `p
  ≤ 1`.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

/-- The general dihedral record extraction law holds, including its circuit counts and qubit
factorization [Kuperberg2005]. -/
theorem algorithm2_record_law : SourceGeneralRecordLaw :=
  sourceGeneralRecordLaw

/-- Every positive collision width whose square covers `N` gives a success-one shift endpoint;
the chosen collision width also satisfies the stated query bound [Kuperberg2005]. -/
theorem algorithm2_general_recovery (N : ℕ) [NeZero N] :
    (∀ m : ℕ, 0 < m → N ≤ m * m →
      ShiftRecoveryEndpoint N 1 (generalCollisionLedger N m)) ∧
      (ShiftRecoveryEndpoint N 1 (generalCollisionLedger N (generalCollisionWidth N))) ∧
      (generalCollisionQueryCount N (generalCollisionWidth N)
        ≤ 2 * generalCollisionWidth N + 2) :=
  clause14_endpoint N

/-- The general recovery endpoint obligation holds for every real success parameter `p ≤ 1`
[Kuperberg2005]. -/
theorem algorithm2_general_endpoint_obligation (N : ℕ) [NeZero N] (p : ℝ)
    (hp : p ≤ 1) :
    clause14_general_endpoint_obligation N p :=
  clause14_general_endpoint_discharged N p hp

end Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2
