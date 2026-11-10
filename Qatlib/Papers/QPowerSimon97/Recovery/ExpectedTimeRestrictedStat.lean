/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AbelianDecoders.SimonDecoding.VerifiedSimonRetry
import Qatlib.Concepts.StoppingCore.BranchCostCore.WeightedUnboundedExecution
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
set_option autoImplicit false
open scoped ENNReal Classical
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.AbelianDecoders.SimonDecoding
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib

def ExpectedTimeRestricted : Prop :=
  ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n) (Tf : ℕ → ℕ),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    generalNeverMass (simonVerifiedRetryKernel f) (Sum.inr ()) = 0 ∧
    (∑' K : ℕ, haltJoint (simonVerifiedRetryKernel f) (Sum.inr ()) s K) = 1 ∧
    (∀ fuel : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost
        (weightedRunFor (simonVerifiedRetryKernel f) (fun _ => (n+3)*Tf n) fuel
          (Sum.inr ())) ≤
        ((2*((n+3)*Tf n) : ℕ) : ℝ≥0∞)) ∧
    simonClassicalExpectedLimit f ≤ ((2*simonBlockOpsBound n : ℕ) : ℝ≥0∞)

end Qatlib.Papers.QPowerSimon97.Recovery
