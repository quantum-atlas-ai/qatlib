/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Distinguisher.BooleanRecoveryProbability
import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryConsumers
import Qatlib.Concepts.HspRecovery.CyclicRecovery.CyclicGcdDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.HspRecovery.BackendAudit

open scoped Classical
open Qatlib.Concepts.HspRecovery.BackendAudit Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.HspRecovery.Distinguisher
universe u

def BooleanRecoveryBackendLaw : Prop :=
  ∀ {n : ℕ} {R : Type u} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (H : AddSubgroup (BooleanVec n)),
    HidesSubgroup f H →
    ∀ (e : BooleanVec n ≃ AddChar (BooleanVec n) ℂ) (m : ℕ),
    ENNReal.ofReal (1 - (Fintype.card {x // x ∉ H} : ℝ) * (1 / 2) ^ m) ≤
      ∑ xs with booleanSampleCandidate (booleanDecodedSamples xs) = H,
        (hiddenSubgroupFreshSamples f e m) xs

def SimonRecoveryBackendLaw : Prop :=
  ∀ {n : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R) (s : Reg n) (k : ℕ),
    BooleanSimonPromise f (regBooleanEquiv n s) →
    ENNReal.ofReal (1 - (1 / 2) ^ k) ≤ (simonDecodedRun f (n + k)).1 (some s) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (simonDecodedRun f (n + k)).1 (fun out => out ≠ some s) ≤
        ENNReal.ofReal ((1 / 2) ^ k)

def TableRecoveryBackendLaw : Prop :=
  ∀ {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : G → R) (e : G ≃ AddChar G ℂ) (tab : G → G → Bool)
    (H : AddSubgroup G) (m : ℕ),
    HidesSubgroup f H → (∀ a y, tab a y = true ↔ e a y = 1) →
    1 - (Fintype.card G : ℝ) * ((2 : ℝ)⁻¹) ^ m ≤
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → G =>
        ((tableKernelDecode tab (List.ofFn xs)).1 : Set G) = (H : Set G))

def CyclicRecoveryBackendLaw : Prop :=
  ∀ {R : Type} [Fintype R] [DecidableEq R] [AddCommGroup R]
    (N r k : ℕ) (hN : 0 < N) (f : Fin N → R),
    0 < r → r ∣ N → (∀ x y : Fin N, f x = f y ↔ x.val % r = y.val % r) →
    let m := Nat.log2 N + 1 + k
    (ENNReal.ofReal (1 - (2 : ℝ) ^ (-(k : ℤ))) ≤
        (cyclicCountedRecovery N hN f m).within (m + 2) (fun out => out = some r)) ∧
      (List.replicate m (cyclicSamplingCircuit (R := R) N) |>.map QueryCount).sum + 2 = m + 2 ∧
      (List.replicate m (cyclicSamplingCircuit (R := R) N) |>.map GateCount).sum = 2 * m ∧
      (∀ ω : Fin m → Fin N,
        (cyclicGcdCounted N (List.ofFn (fun i => (ω i).val))).2 ≤ m * (N + 1)) ∧
      cyclicCountedRecovery N hN f m =
        (cyclicFreshSamples N hN f m).map (fun ω => (cyclicVerifiedDecode N hN f ω, m + 2))

def RecoveryBackendAudit : Prop :=
  BooleanRecoveryBackendLaw.{u} ∧ SimonRecoveryBackendLaw ∧
    TableRecoveryBackendLaw ∧ CyclicRecoveryBackendLaw

theorem recoveryBackendAudit : RecoveryBackendAudit.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hiddenSubgroupFreshSamples_boolean_recovery_success_ge
  · exact simon_gaussian_accessible_budget
  · exact character_table_actual_subgroup_recovery_probability
  · intro R _ _ _ N r k hN f hr hrdvd hcol
    simpa only [] using (cyclic_accessible_budget_and_measurements N r k hN f hr hrdvd hcol)

end Qatlib.Concepts.HspRecovery.BackendAudit
