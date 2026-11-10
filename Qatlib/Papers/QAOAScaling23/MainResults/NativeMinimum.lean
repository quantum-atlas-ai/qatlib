/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.MainResults.CausalTheorem
import Qatlib.Papers.QAOAScaling23.BiasedProcess.FamilyBudget
import Qatlib.Papers.QAOAScaling23.LABSDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.MainResults
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open BiasedProcess WeightedCost BudgetPrefix CausalSearch FreshRepeat
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
variable {I : Type} [Fintype I] [DecidableEq I]

def publicAlgorithm (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (B N : ℕ) (δ : ℝ) :
    Qatlib.Foundations.ProbabilityCore.FiniteBranch.Tree (NativeBatch I) :=
  freshNative cost (initializedRun cost (Born.preparedLaw U hU seed)
    (publicOracle U hU seed cost B N) (2^N) B 3 seed) (outerIterations δ)

theorem actual_public_minimum (U : Matrix I I ℂ) (hU : U∈Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (B N : ℕ) (hN : 1≤N) (hcard : Fintype.card I≤2^N)
    (h0 : 0<Born.weights cost (Born.preparedLaw U hU seed) 0)
    (hbudget : 37500*(N:ℝ)/Real.sqrt (Born.weights cost (Born.preparedLaw U hU seed) 0)≤(B:ℝ))
    (δ : ℝ) (hδ : 0<δ) :
    (publicAlgorithm U hU seed cost B N δ).probability
        (fun b => b.best.map (fun i => (costRank cost i).val)≠some 0)≤δ ∧
      (publicAlgorithm U hU seed cost B N δ).All
        (fun b => b.totalPaid≤outerIterations δ*B) := by
  have hNreal : (1:ℝ)≤N := by exact_mod_cast hN
  have hBr : (0:ℝ)<B := (by positivity : (0:ℝ)<37500*(N:ℝ)/
    Real.sqrt (Born.weights cost (Born.preparedLaw U hU seed) 0)).trans_le hbudget
  have hB : 0<B := by exact_mod_cast hBr
  let ms:=NativeFamily.tail B N hB
  let rs:=NativeFamily.rows U hU seed cost h0 ms
  let candidate:=NativeFamily.candidate U hU seed cost h0 ms
  have hq : ∀ j : Fin (costLevels cost).card,
      (((Born.preparedLaw U hU seed).map (costRank cost)) j).toReal=
        Born.weights cost (Born.preparedLaw U hU seed) j.val := by
    intro j
    simp only [Born.weights,dif_pos j.isLt,costClassLaw]
  have horder : ∀ i j,(costRank cost i).val<(costRank cost j).val ↔ cost i<cost j :=
    fun i j => costRank_lt_iff cost i j
  have hjoint : ∀ current r,(costRank cost current).val=r+1 →
      (paidTree cost current (publicOracle U hU seed cost B N current)).law=
        (rs r).law.map (rowPayload rs candidate r) := by
    intro current r hr
    have h:=NativeFamily.joint_paid U hU seed cost h0 ms current r hr
    rw [show 1::ms=publicSchedule B N from NativeFamily.tail_spec B N hB] at h
    exact h
  have hcapFuel : ∀ i,(costRank cost i).val≤2^N := fun i =>
    (costRank cost i).isLt.le.trans (Born.classes_le_bit_bound cost N hcard)
  have hb : 15*2500*(N:ℝ)/Real.sqrt (popt (Born.weights cost (Born.preparedLaw U hU seed)))≤(B:ℝ) := by
    simpa only [popt,show (15:ℝ)*2500=37500 by norm_num] using hbudget
  exact causal_public_budget_theorem (Born.classes_pos cost seed) cost (costRank cost)
    (costRank_zero_iff cost) horder (Born.preparedLaw U hU seed) _ hq h0
    (Born.weights_nonneg cost _) (publicOracle U hU seed cost B N)
    (fun current => oracleCode_noSave U hU seed cost (publicSchedule B N) current)
    rs (NativeFamily.row_law U hU seed cost h0 ms) candidate
    (NativeFamily.candidate_rank U hU seed cost h0 ms) hjoint
    2500 (N:ℝ) ((25/32:ℝ)^(8*(N+1))) δ (by norm_num) (by positivity) hδ
    (NativeFamily.family_charge_bound U hU seed cost h0 B N hN hB hbudget)
    (by positivity) (NativeFamily.family_bad_bound U hU seed cost h0 B N hN hB hbudget)
    (NativeFamily.family_bad_union cost N hcard) (2^N) B 3 hcapFuel seed (by norm_num; nlinarith) hb

omit [DecidableEq I] in

theorem actual_output_optimal (cost : I → ℝ) (b : NativeBatch I)
    (h : b.best.map (fun i => (costRank cost i).val)=some 0) :
    ∃ i,b.best=some i ∧ ∀ j,cost i≤cost j := by
  cases hb : b.best with
  | none => simp [hb] at h
  | some i =>
    have hr : (costRank cost i).val=0 := by
      simpa only [hb,Option.map_some,Option.some.injEq] using h
    exact ⟨i,rfl,(costRank_zero_iff cost i).mp hr⟩

theorem labs_public_minimum (N B : ℕ) (hN : 3≤N)
    (U : Matrix (Fin N → Bool) (Fin N → Bool) ℂ)
    (hU : U∈Matrix.unitaryGroup (Fin N → Bool) ℂ) (seed : Fin N → Bool)
    (h0 : 0<Born.weights LABSDefs.energy (Born.preparedLaw U hU seed) 0)
    (hbudget : 37500*(N:ℝ)/Real.sqrt (Born.weights LABSDefs.energy (Born.preparedLaw U hU seed) 0)≤(B:ℝ))
    (δ : ℝ) (hδ : 0<δ) :
    (publicAlgorithm U hU seed LABSDefs.energy B N δ).probability
        (fun b => b.best.map (fun i => (costRank LABSDefs.energy i).val)≠some 0)≤δ ∧
      (publicAlgorithm U hU seed LABSDefs.energy B N δ).All
        (fun b => b.totalPaid≤outerIterations δ*B) := by
  exact actual_public_minimum U hU seed LABSDefs.energy B N (by omega)
    (by simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]; exact le_refl _) h0 hbudget δ hδ

theorem labs_output_merit (N : ℕ) (hN : 3≤N) (b : NativeBatch (Fin N → Bool))
    (h : b.best.map (fun i => (costRank LABSDefs.energy i).val)=some 0) :
    ∃ i,b.best=some i ∧ (∀ j : Fin N → Bool,LABSDefs.energy i≤LABSDefs.energy j) ∧
      ∀ j : Fin N → Bool,LABSDefs.meritFactor j≤LABSDefs.meritFactor i := by
  obtain ⟨i,hi,hmin⟩:=actual_output_optimal LABSDefs.energy b h
  exact ⟨i,hi,hmin,fun j => LABSDefs.meritFactor_antitone (by omega) i j (hmin j)⟩

end Qatlib.Papers.QAOAScaling23.MainResults
