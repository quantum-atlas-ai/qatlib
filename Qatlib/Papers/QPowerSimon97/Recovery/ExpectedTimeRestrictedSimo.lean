/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedTimeRestrictedStat
import Qatlib.Papers.QPowerSimon97.Recovery.WeightedConstantCost
set_option warningAsError false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.AbelianDecoders.SimonDecoding

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open scoped Classical ENNReal

theorem expectedTimeRestricted : ExpectedTimeRestricted := by
  intro n R _ _ _ f s Tf hf
  have h := simon_verified_unbounded_expected_queries_and_cutoff n R f s hf
  refine ⟨h.1, h.2.2.1, ?_,
    (simon_verified_receipt_trace_coupling_and_classical_expected_work n R f s hf).2⟩
  intro fuel
  rw [weightedRunFor_const_charge_expected_cost,
    (general_unbounded_actual_expected_time Unit (Reg n)
      (simonVerifiedRetryKernel f) (Sum.inr ())).2.2 fuel]
  calc
    _ ≤ (((n + 3) * Tf n : ℕ) : ℝ≥0∞) *
        generalUnboundedTime (simonVerifiedRetryKernel f) (Sum.inr ()) :=
      mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range fuel)) _
    _ ≤ (((n + 3) * Tf n : ℕ) : ℝ≥0∞) * 2 := mul_le_mul_right h.2.1 _
    _ = _ := by push_cast; ring

end Qatlib.Papers.QPowerSimon97.Recovery
