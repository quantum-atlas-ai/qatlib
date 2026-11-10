/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic.NormNum.Parity
import Qatlib.Concepts.HspRecovery.JointDlog.JointBezoutDlogDecoder
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false
open scoped Classical BigOperators
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.JointDlog

namespace Qatlib.Concepts.HspRecovery.JointDlog
open Qatlib.Concepts.HspRecovery.BackendAudit Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
set_option warningAsError false

private theorem joint_six_injective : Function.Injective (fun x : ZMod 6 => x.val • (1 : ZMod 6)) := by
  intro x y h
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_one] using! h

private theorem joint_six_exact_probability :
    (cyclicDlogRecordDist 6 (1 : ZMod 6) 2).probEvent
      (fun ω : Fin 2 → ZMod 6 × ZMod 6 =>
        (jointDlogVerified (1 : ZMod 6) 2 (List.ofFn ω)).1 = some 2) = 2/3 := by
  rw [joint_dlog_uniform_success_mass 6 (ZMod 6) 1 2 2 2
    (by omega) (by decide) joint_six_injective (by decide), Finset.sum_filter]
  have heq :
      (∑ a : Fin 2 → Fin 6, if (List.ofFn (fun i => (a i).val)).foldl Nat.gcd 6 = 1
        then (1/(6 : ℝ))^2 else 0) =
      ∑ p : Fin 6 × Fin 6, if Nat.gcd (Nat.gcd 6 p.1.val) p.2.val = 1
        then (1/(6 : ℝ))^2 else 0 := by
    apply Fintype.sum_equiv (finTwoArrowEquiv (Fin 6))
    intro a
    simp [List.ofFn_succ, finTwoArrowEquiv]
  norm_num only [Nat.cast_ofNat] at heq ⊢
  rw [heq, Fintype.sum_prod_type]
  norm_num [Fin.sum_univ_succ]

private theorem joint_six_euclid_first : cyclicDlogEuclid 2 1 0 6 0 1 = ((2,1,0),1) := by
  rw [cyclicDlogEuclid]
  norm_num
  rw [cyclicDlogEuclid]
  norm_num

private theorem joint_six_euclid_second : cyclicDlogEuclid 3 1 0 2 0 1 = ((1,1,-1),3) := by
  rw [cyclicDlogEuclid]
  norm_num
  rw [cyclicDlogEuclid]
  norm_num
  rw [cyclicDlogEuclid]
  norm_num
  rw [cyclicDlogEuclid]
  norm_num

private theorem joint_six_val_two : (2 : ZMod 6).val = 2 := by decide

private theorem joint_six_val_three : (3 : ZMod 6).val = 3 := by decide

private theorem joint_six_fold :
    jointDlogFold ([(2,4),(3,0)] : List (ZMod 6 × ZMod 6)) = ((1,2),(2,4)) := by
  norm_num [jointDlogFold, joint_six_val_two, joint_six_val_three, joint_six_euclid_first, joint_six_euclid_second]
  decide

private theorem joint_six_binary : binaryAddCounted (1 : ZMod 6) 2 = (2,3) := by
  have hl : Nat.log 2 2 = 1 := by simpa using! Nat.log_pow (by omega : 1 < 2) 1
  rw [binaryAddCounted, hl]
  norm_num [binaryAddFuel]

theorem joint_mod_six_full_consumer :
    ((jointDlogVerified (1 : ZMod 6) 2 ([(2,4),(3,0)] : List (ZMod 6 × ZMod 6))).1 = some 2 ∧
      (jointDlogVerified (1 : ZMod 6) 2 ([(2,4),(3,0)] : List (ZMod 6 × ZMod 6))).2 = (2,4,3) ∧
      (cyclicDlogRecordDist 6 (1 : ZMod 6) 2).probEvent
        (fun ω : Fin 2 → ZMod 6 × ZMod 6 =>
          (jointDlogVerified (1 : ZMod 6) 2 (List.ofFn ω)).1 = some 2) = 2/3) ∧
    (∀ m : ℕ, 1-(6 : ℝ)/(2^m : ℝ) ≤ (cyclicDlogRecordDist 6 (1 : ZMod 6) 2).probEvent
      (fun ω : Fin m → ZMod 6 × ZMod 6 =>
        (jointDlogVerified (1 : ZMod 6) 2 (List.ofFn ω)).1 = some 2)) ∧
    (let cs := tableSamplingCircuit (R := ZMod 6) (cyclicDlogCharacters 6) (cyclicDlogSamplingPrepare 6);
      QueryCount (List.replicate 2 cs).flatten = 2 ∧
      GateCount (List.replicate 2 cs).flatten = 4) := by
  refine ⟨⟨?_, ?_, joint_six_exact_probability⟩, ?_, ?_⟩
  · norm_num [jointDlogVerified, joint_six_fold, joint_six_val_two, joint_six_binary]
  · norm_num [jointDlogVerified, joint_six_fold, joint_six_val_two, joint_six_binary]
  · intro m
    exact joint_dlog_fresh_actual_verified_success 6 (ZMod 6) 1 2 2 m
      (by omega) (by decide) joint_six_injective (by decide)
  · have h := composite_dlog_same_sampling_resource_ledger 6 (ZMod 6) 2
    exact ⟨h.2.2.1, h.2.2.2⟩

theorem joint_dlog_nonunit_mod_six_consumer :
    (jointDlogVerified (1 : ZMod 6) 2 ([(2,4),(3,0)] : List (ZMod 6 × ZMod 6))).1 = some 2 ∧
    (jointDlogVerified (1 : ZMod 6) 2 ([(2,4),(3,0)] : List (ZMod 6 × ZMod 6))).2 = (2,4,3) ∧
    (cyclicDlogRecordDist 6 (1 : ZMod 6) 2).probEvent
      (fun ω : Fin 2 → ZMod 6 × ZMod 6 =>
        (jointDlogVerified (1 : ZMod 6) 2 (List.ofFn ω)).1 = some 2) = 2/3 :=
  joint_mod_six_full_consumer.1

end Qatlib.Concepts.HspRecovery.JointDlog
