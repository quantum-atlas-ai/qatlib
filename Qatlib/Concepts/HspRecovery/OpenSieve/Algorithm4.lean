/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt
import Qatlib.Concepts.HspRecovery.RecordExtract.SummandExtractionDihe
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm4

open Qatlib.Concepts.HspRecovery.RecordExtract
open Qatlib.Concepts.HspRecovery.OpenSieve

theorem algorithm4_summand_extraction : SourceSummandExtraction :=
  sourceSummandExtraction

theorem algorithm4_representation_transport (N : ℕ) [NeZero N] :
    RepTransportTarget N :=
  (clause13_endpoint N).1

theorem algorithm4_dihedral_instance_endpoint (N : ℕ) [NeZero N] (p : ℝ)
    (hp : p ≤ 1) :
    clause14_general_endpoint_obligation N p :=
  clause14_general_endpoint_discharged N p hp

end Qatlib.Concepts.HspRecovery.OpenSieve.Algorithm4
