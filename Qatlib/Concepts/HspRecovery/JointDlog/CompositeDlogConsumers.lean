/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CfOrder.CompositeOrderDlogDecoder
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CfOrder

namespace Qatlib.Concepts.HspRecovery.JointDlog
open Qatlib.Concepts.HspRecovery.BackendAudit Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
open scoped Classical
set_option warningAsError false

theorem composite_dlog_mod_six_real_consumer :
    (cyclicDlogRecordDist 6 (1 : ZMod 6) 2).probEvent
      (fun ω : Fin 2 → ZMod 6 × ZMod 6 =>
        (cyclicDlogVerified (1 : ZMod 6) 2 (List.ofFn ω)).1 = some 2) = 5/9 ∧
    (cyclicDlogVerified (1 : ZMod 6) 2 ([(2,4),(5,4)] : List (ZMod 6 × ZMod 6))).1 = some 2 ∧
    (cyclicDlogVerified (1 : ZMod 6) 2 ([(2,4),(5,4)] : List (ZMod 6 × ZMod 6))).2.1 = 2 ∧
    (cyclicDlogVerified (1 : ZMod 6) 2 ([(2,4),(5,4)] : List (ZMod 6 × ZMod 6))).2.2.2 = 2 := by
  have hs := composite_dlog_fresh_verified_success 6 (ZMod 6) (1 : ZMod 6) 2 2 2
    (by norm_num) (by change (6 : ZMod 6) = 0; decide)
    (by
      intro a b hab
      simpa only [show a.val • (1 : ZMod 6) = a from by norm_num,
        show b.val • (1 : ZMod 6) = b from by norm_num] using! hab)
    (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · rw [hs]; have ht : Nat.totient 6 = 2 := by decide
    rw [ht]; norm_num
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem composite_dlog_mod_six_sampling_resources :
    let cs := tableSamplingCircuit (R := ZMod 6) (cyclicDlogCharacters 6)
      (cyclicDlogSamplingPrepare 6)
    QueryCount cs = 1 ∧ GateCount cs = 2 ∧
    QueryCount (List.replicate 2 cs).flatten = 2 ∧
    GateCount (List.replicate 2 cs).flatten = 4 :=
  composite_dlog_same_sampling_resource_ledger 6 (ZMod 6) 2
end Qatlib.Concepts.HspRecovery.JointDlog
