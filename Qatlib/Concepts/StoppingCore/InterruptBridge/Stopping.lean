/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.InterruptBridge.StoppingCoreDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

namespace Qatlib.Concepts.StoppingCore.InterruptBridge

open Qatlib
open scoped BigOperators ComplexOrder

theorem quantumRunFor_prefix {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (k : ℕ) (C : Circuit I) (ψ : QState I) :
    quantumRunFor O k ⟨C,ψ⟩ = ⟨C.drop k, Run O (C.take k) ψ⟩ := by
  induction k generalizing C ψ with
  | zero => rfl
  | succ k ih =>
    cases C with
    | nil => simpa [quantumRunFor, quantumTick, Run] using ih [] ψ
    | cons s C =>
      cases s <;> simp [quantumRunFor, quantumTick, ih]

theorem quantumRunFor_resume {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (m n : ℕ) (cfg : QuantumContinuation I) :
    quantumRunFor O (m+n) cfg = quantumRunFor O n (quantumRunFor O m cfg) := by
  induction m generalizing cfg with
  | zero => simp [quantumRunFor]
  | succ m ih => simpa only [Nat.succ_add, quantumRunFor] using ih (quantumTick O cfg)

theorem quantum_prefix_receipts {I : Type*} [Fintype I] [DecidableEq I]
    (C : Circuit I) (k : ℕ) :
    QueryCount (C.take k) + QueryCount (C.drop k) = QueryCount C ∧
      GateCount (C.take k) + GateCount (C.drop k) = GateCount C ∧
      QueryCount (C.take k) + GateCount (C.take k) = min k C.length := by
  have hlength (cs : Circuit I) : QueryCount cs + GateCount cs = cs.length := by
    induction cs with
    | nil => rfl
    | cons s cs ih => cases s <;> simp [QueryCount, GateCount] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.take_append_drop] using (queryCount_append (C.take k) (C.drop k)).symm
  · simpa only [List.take_append_drop] using (gateCount_append (C.take k) (C.drop k)).symm
  · simpa only [List.length_take] using hlength (C.take k)

theorem quantumRunFor_normalized {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ) (k : ℕ)
    (C : Circuit I) (hC : IsUnitaryCircuit C) (ψ : QState I) (hψ : Normalized ψ) :
    Normalized (quantumRunFor O k ⟨C,ψ⟩).state := by
  rw [quantumRunFor_prefix]
  exact normalized_run O hO (C.take k)
    (fun U hU => hC U (List.mem_of_mem_take hU)) hψ

theorem zero_charge_stability_failure :
    weightedHaltJoint zeroCountdownNext (fun _ => 0) (.inr true) () 0 = 0 ∧
      weightedRunFor zeroCountdownNext (fun _ => 0) 2 (.inr true) (.inl (),0) = 1 := by
  constructor
  · simp [weightedHaltJoint, weightedRunFor, CostedLaw.ret, PMF.pure_apply]
  · rw [weightedRunFor_succ_running]
    simp only [zeroCountdownNext, if_true, PMF.pure_bind, CostedLaw.charge_zero]
    rw [weightedRunFor_succ_running]
    simp [zeroCountdownNext, weightedRunFor, CostedLaw.ret, PMF.pure_apply]

theorem coarse_conditional_mixture {O P : Type*} [Fintype O] [Fintype P] [DecidableEq P]
    {D E : ℕ} (I : Instrument O D E) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (f : O → P) (p : P) (hp : 0 < instrumentProb (I.coarsen f) ρ p) :
    (I.coarsen f).conditionalState ρ p hp =
      ∑ o ∈ Finset.univ.filter (fun o => f o = p),
        if h : 0 < instrumentProb I ρ o then
          (((instrumentProb I ρ o / instrumentProb (I.coarsen f) ρ p : ℝ) : ℂ)) •
            I.conditionalState ρ o h else 0 := by
  classical
  let μ : ℝ := instrumentProb (I.coarsen f) ρ p
  change (μ : ℂ)⁻¹ • ((∑ o ∈ Finset.univ.filter (fun o => f o = p), I.branch o) ρ) = _
  rw [LinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : 0 < instrumentProb I ρ o
  · rw [dif_pos ho, ← (Qatlib.Concepts.QuditTeleport.TeleportCore.Instrument.conditionalState_reconstruction I ρ o ho).1, smul_smul]
    congr 1
    simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    dsimp [μ]
    ring
  · have hz : instrumentProb I ρ o = 0 :=
      le_antisymm (not_lt.mp ho) (instrumentProb_nonneg I hρ.1 o)
    rw [dif_neg ho, (instrumentProb_eq_zero_iff I hρ.1 o).mp hz, smul_zero]

end Qatlib.Concepts.StoppingCore.InterruptBridge
