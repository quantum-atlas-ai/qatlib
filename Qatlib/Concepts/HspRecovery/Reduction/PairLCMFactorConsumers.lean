/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.PairLCMOrderRecovery
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.OrderRecovery

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.HspRecovery.ReductionCore
open scoped BigOperators Classical
set_option autoImplicit false

theorem pairLCM_twenty_one_order :
    let a : (ZMod 21)ˣ := Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)
    orderOf a=6 := by
  (try dsimp only)
  apply (orderOf_eq_iff (by decide : 0<6)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

theorem pairLCM_twenty_one_reduced_decodes :
    (reducedOrderDecode 21 2048 (⟨683,by decide⟩:Fin 2048)).1=some (1,3) ∧
    (reducedOrderDecode 21 2048 (⟨1024,by decide⟩:Fin 2048)).1=some (1,2) := by
  decide

theorem pair_lcm_twenty_one_non_coprime_factor_consumer :
    let a : (ZMod 21)ˣ := Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)
    orderOf a=6 ∧
    (pairLCMOrderDecode 21 2048 a ((⟨683,by decide⟩:Fin 2048),(⟨1024,by decide⟩:Fin 2048))).1=some 6 ∧
    ∃ d, pairLCMFactor 21 2048 a ((⟨683,by decide⟩:Fin 2048),(⟨1024,by decide⟩:Fin 2048))=some d ∧
      1<d ∧ d<21 ∧ d∣21 := by
  (try dsimp only)
  refine ⟨pairLCM_twenty_one_order, by decide, 7, by decide, by decide, by decide, by decide⟩

theorem pair_lcm_twenty_one_same_record_classical_work :
    let a : (ZMod 21)ˣ := Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)
    let yz : Fin 2048×Fin 2048 := (⟨683,by decide⟩,⟨1024,by decide⟩)
    (pairLCMOrderDecode 21 2048 a yz).2=(8,6) ∧
    (pairLCMOrderDecode 21 2048 a yz).2.1≤21*(21+1) ∧
    (pairLCMOrderDecode 21 2048 a yz).2.2≤21^2 ∧
    1<7 ∧ 7<21 ∧ 7∣21 := by
  (try dsimp only)
  have h := pair_lcm_order_soundness_and_actual_work 21 2048
    (Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide))
    (⟨683,by decide⟩:Fin 2048) (⟨1024,by decide⟩:Fin 2048)
  exact ⟨by decide, h.1, h.2.1, h.2.2.2 7 (by decide)⟩

noncomputable def pairModularOrderFreshMass (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hM : 0<M) (yz : Fin M×Fin M) : ℝ :=
  (modularOrderLaw N M a hM).probOf (fun j : Fin 2 => if j=0 then yz.1 else yz.2)

theorem pairModularOrderFreshMass_prob (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hM : 0<M) (yz : Fin M×Fin M) :
    pairModularOrderFreshMass N M a hM yz =
      (modularOrderLaw N M a hM).prob yz.1 * (modularOrderLaw N M a hM).prob yz.2 := by
  simp [pairModularOrderFreshMass, FinDist.probOf, Fin.prod_univ_two]

theorem pairModularOrderFreshMass_sum (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0<M) :
    ∑ yz, pairModularOrderFreshMass N M a hM yz = 1 := by
  simp_rw [pairModularOrderFreshMass_prob]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, (modularOrderLaw N M a hM).sum_one]
  simp [(modularOrderLaw N M a hM).sum_one]

theorem pair_lcm_actual_fresh_quantum_ledger (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hM : 0<M) :
    (∀ _j : Fin 2, IsUnitaryCircuit (modularOrderCircuit N M a)) ∧
    (∑ _j : Fin 2, QueryCount (modularOrderCircuit N M a))=2*(M*(M-1)/2) ∧
    (∑ _j : Fin 2, GateCount (modularOrderCircuit N M a))=2*(M*(M-1)+2) := by
  have h := modular_order_exact_query_macro_ledger N M a hM
  exact ⟨fun _ => h.1, by simp [h.2.1], by simp [h.2.2]⟩

theorem pair_lcm_twenty_one_probability_and_work :
    let a : (ZMod 21)ˣ := Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)
    (∑ yz ∈ Finset.univ.filter (fun yz : Fin 2048×Fin 2048 =>
      (pairLCMOrderDecode 21 2048 a yz).1=some 6),
      (modularOrderLaw 21 2048 a (by decide)).prob yz.1 *
      (modularOrderLaw 21 2048 a (by decide)).prob yz.2) ≥ (8/Real.pi^2)^2/4 ∧
    (∑ _j : Fin 2, QueryCount (modularOrderCircuit 21 2048 a))=4192256 ∧
    (∑ _j : Fin 2, GateCount (modularOrderCircuit 21 2048 a))=8384516 := by
  (try dsimp only)
  constructor
  · have h := pair_lcm_order_actual_fresh_success_bound 21 2048
      (Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)) (by decide) (by decide)
      (by rw [pairLCM_twenty_one_order]; decide) (by decide)
    simpa only [pairLCM_twenty_one_order] using! h
  · have h := (pair_lcm_actual_fresh_quantum_ledger 21 2048
      (Units.mkOfMulEqOne (2:ZMod 21) 11 (by decide)) (by decide)).2
    have hq : 2*(2048*(2048-1)/2)=4192256 := by decide
    have hg : 2*(2048*(2048-1)+2)=8384516 := by decide
    rw [hq,hg] at h
    exact h
end Qatlib.Concepts.HspRecovery.ReductionCore
