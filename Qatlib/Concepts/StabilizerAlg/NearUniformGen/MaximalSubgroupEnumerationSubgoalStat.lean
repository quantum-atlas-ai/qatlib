/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.BackendAudit.FiniteAbelianDuality

/-!
# Finite subgroup-cover specification

`MaximalSubgroupEnumerationSubgoal` states the existence of a finite collection of proper
subgroups that contains a supergroup of every proper subgroup. Its cardinality bound is the
ingredient used in the near-uniform generation failure estimate. For background, see
[Kitaev1995].

## Main statements

* `MaximalSubgroupEnumerationSubgoal`: specifies a proper-subgroup cover of size less than the
  group order.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.QuditTeleport.TeleportCore

namespace Qatlib.Concepts.StabilizerAlg.NearUniformGen

/-- The proposition that every finite abelian group possesses a finite family of proper
subgroups covering all proper subgroups by containment and having cardinality less than the
group order. -/
def MaximalSubgroupEnumerationSubgoal : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H],
    ∃ maxs : Finset (AddSubgroup H),
      (∀ L ∈ maxs, L < ⊤) ∧
      (∀ K : AddSubgroup H, K < ⊤ → ∃ L ∈ maxs, K ≤ L) ∧
      maxs.card < Fintype.card H

end Qatlib.Concepts.StabilizerAlg.NearUniformGen
