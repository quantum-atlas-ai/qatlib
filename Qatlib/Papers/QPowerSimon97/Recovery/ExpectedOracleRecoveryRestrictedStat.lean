/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
import Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralUnboundedExecution
set_option warningAsError false

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
open scoped ENNReal Classical
namespace Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib

def ExpectedOracleRecoveryRestricted : Prop :=
  ∀ (n : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    let verify := fun candidate : Option (Reg n) => match candidate with
      | none => none
      | some t => if f (regBooleanEquiv n t)=f 0 then some t else none
    let trial := PMF.map verify (simonDecodedRun f (n+1)).1
    let kernel : Unit → PMF (Reg n ⊕ Unit) := fun _ =>
      PMF.map (fun x => match x with | none => Sum.inr () | some t => Sum.inl t) trial
    generalNeverMass kernel (Sum.inr ()) = 0 ∧
    (∑' K : ℕ, haltJoint kernel (Sum.inr ()) s K) = 1 ∧
    ((n+3 : ℕ) : ℝ≥0∞)*generalUnboundedTime kernel (Sum.inr ()) ≤ (2*(n+3) : ℕ)
end Qatlib.Papers.QPowerSimon97.Recovery
