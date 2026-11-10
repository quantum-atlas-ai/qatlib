/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.RecordExtract.GeneralRecordLawDihe
import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.RecordExtract.Nonabelian
open Qatlib.Concepts.HspRecovery.OpenSieve

theorem algorithm2_record_law : SourceGeneralRecordLaw :=
  sourceGeneralRecordLaw

theorem algorithm2_general_recovery (N : ℕ) [NeZero N] :
    (∀ m : ℕ, 0 < m → N ≤ m * m →
      ShiftRecoveryEndpoint N 1 (generalCollisionLedger N m)) ∧
      (ShiftRecoveryEndpoint N 1 (generalCollisionLedger N (generalCollisionWidth N))) ∧
      (generalCollisionQueryCount N (generalCollisionWidth N)
        ≤ 2 * generalCollisionWidth N + 2) :=
  clause14_endpoint N

theorem algorithm2_general_endpoint_obligation (N : ℕ) [NeZero N] (p : ℝ)
    (hp : p ≤ 1) :
    clause14_general_endpoint_obligation N p :=
  clause14_general_endpoint_discharged N p hp

end Qatlib.Concepts.HspRecovery.RecordExtract.Algorithm2
