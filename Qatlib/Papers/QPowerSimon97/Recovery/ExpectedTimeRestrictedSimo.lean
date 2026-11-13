/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.ExpectedTimeRestrictedStat
import Qatlib.Papers.QPowerSimon97.Recovery.WeightedConstantCost

/-!
# Expected cost of verified Simon retries

Proves `expectedTimeRestricted` for the verified Simon retry kernel. In addition to almost-sure
exact recovery, it bounds oracle work uniformly over finite execution fuel and bounds the
limiting classical work, giving a restricted expected-cost formulation associated with Theorem
3.2 of [Simon1997].

## Main statements

* `expectedTimeRestricted`: The restricted verified Simon retry procedure recovers the promised
  secret almost surely, has expected oracle work at most `2 * ((n + 3) * Tf n)` for every finite
  fuel, and has limiting expected classical work at most `2 * simonBlockOpsBound n` [Simon1997].

## References

* [Simon, 1997][Simon1997]
-/

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

/-- The restricted verified Simon retry procedure recovers the promised secret almost surely,
has expected oracle work at most `2 * ((n + 3) * Tf n)` for every finite fuel, and has
limiting expected classical work at most `2 * simonBlockOpsBound n` [Simon1997]. -/
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
