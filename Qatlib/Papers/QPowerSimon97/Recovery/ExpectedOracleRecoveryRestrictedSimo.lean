/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedOracleRecoveryRestrictedStat
import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry

/-!
# Verified Simon recovery with expected oracle cost

Proves `expectedOracleRecoveryRestricted`, the restricted verified-retry formulation of exact
Simon secret recovery. Under the Boolean Simon promise, retries terminate with total mass one at
the specified secret and satisfy the explicit expected oracle-query bound, capturing this part
of Theorem 3.2 of [Simon1997].

## Main statements

* `expectedOracleRecoveryRestricted`: The restricted verified Simon retry procedure has zero
  nontermination mass, total halting mass one at the promised secret, and expected oracle-query
  bound `2 * (n + 3)` [Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher

/-- The restricted verified Simon retry procedure has zero nontermination mass, total halting
mass one at the promised secret, and expected oracle-query bound `2 * (n + 3)` [Simon1997]. -/
theorem expectedOracleRecoveryRestricted : ExpectedOracleRecoveryRestricted := by
  intro n R _ _ _ f s hf
  have h := simon_verified_unbounded_expected_queries_and_cutoff n R f s hf
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end Qatlib.Papers.QPowerSimon97.Recovery
