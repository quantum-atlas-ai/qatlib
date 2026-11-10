/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry
set_option warningAsError false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open scoped ENNReal

theorem simon_verified_zero_nonzero_actual_consumers :
    generalNeverMass (simonVerifiedRetryKernel simonProjectionOracle) (Sum.inr ()) = 0 ∧
    generalUnboundedTime (simonVerifiedRetryKernel simonProjectionOracle) (Sum.inr ()) ≤ 2 ∧
    generalNeverMass (simonVerifiedRetryKernel (fun x : BooleanVec 2 => x)) (Sum.inr ()) = 0 ∧
    generalPendingMass (simonVerifiedRetryKernel (fun x : BooleanVec 2 => x)) (Sum.inr ()) 4 ≤
      (1/16 : ℝ≥0∞) := by
  have hp := simon_verified_unbounded_expected_queries_and_cutoff 2 (ZMod 2)
    simonProjectionOracle simonSecretE0 booleanSimonPromise_simonProjectionOracle
  have hz := simon_verified_unbounded_expected_queries_and_cutoff 2 (BooleanVec 2)
    (fun x => x) (ZeroStr 2) booleanSimonPromise_id_zero
  refine ⟨hp.1, hp.2.1, hz.1, ?_⟩
  convert hz.2.2.2.2 4 using 1 <;> norm_num [← ENNReal.inv_pow]

end Qatlib.Papers.QPowerSimon97.Recovery
