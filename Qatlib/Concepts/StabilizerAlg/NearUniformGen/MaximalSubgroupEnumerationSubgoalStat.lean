/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

def MaximalSubgroupEnumerationSubgoal : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H],
    ∃ maxs : Finset (AddSubgroup H),
      (∀ L ∈ maxs, L < ⊤) ∧
      (∀ K : AddSubgroup H, K < ⊤ → ∃ L ∈ maxs, K ≤ L) ∧
      maxs.card < Fintype.card H

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
