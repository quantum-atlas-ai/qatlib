/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedOracleRecoveryRestrictedStat
import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry
set_option warningAsError false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher

theorem expectedOracleRecoveryRestricted : ExpectedOracleRecoveryRestricted := by
  intro n R _ _ _ f s hf
  have h := simon_verified_unbounded_expected_queries_and_cutoff n R f s hf
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end Qatlib.Papers.QPowerSimon97.Recovery
