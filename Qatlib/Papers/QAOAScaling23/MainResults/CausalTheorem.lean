/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.FreshRepeat.NativeOutput
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.MainResults
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Foundations.ProbabilityCore.FiniteBranch.ClockedCode
open BiasedProcess WeightedCost BudgetPrefix CausalSearch FreshRepeat
variable {I : Type} [Fintype I]

theorem source_initial_fee_funded {L : ℕ} (hL : 0<L) (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0)
    (C N M : ℝ) (hC : 0<C) (hN : 0<N)
    (hM : 1/Real.sqrt (popt q)≤M) (B initialFee : ℕ)
    (hinitFee : (initialFee:ℝ)≤C*N) (hbudget : 15*C*M*N≤(B:ℝ)) : initialFee≤B := by
  have hq01 : q 0≤1 := by
    have h:=ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠⊤) (PMF.coe_le_one p ⟨0,hL⟩)
    simpa only [hq,Fin.val_zero,ENNReal.toReal_one] using h
  have hs : 0<Real.sqrt (popt q) := Real.sqrt_pos.2 h0
  have hs1 : Real.sqrt (popt q)≤1 := by
    simpa only [popt,Real.sqrt_one] using Real.sqrt_le_sqrt hq01
  have hM1 : 1≤M := ((one_le_div hs).2 hs1).trans hM
  have hCN : 0<C*N := mul_pos hC hN
  have hCNM : C*N≤C*M*N := by nlinarith [mul_le_mul_of_nonneg_left hM1 hCN.le]
  have hi : (initialFee:ℝ)≤(B:ℝ) := by nlinarith
  exact_mod_cast hi

theorem causal_minimum_theorem {L : ℕ} (hL : 0<L) (cost : I → ℝ) (rank : I → Fin L)
    (hzero : ∀ i,(rank i).val=0 ↔ ∀ j,cost i≤cost j)
    (horder : ∀ i j,(rank i).val<(rank j).val ↔ cost i<cost j)
    (p : PMF I) (q : ℕ → ℝ) (hq : ∀ i : Fin L,((p.map rank) i).toReal=q i.val)
    (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (oracle : I → Code I (Option I)) (hno : ∀ i,NoSave (oracle i))
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I)
    (hnext : ∀ r a,(rank (candidate r a)).val=((rows r).next a).val)
    (hjoint : ∀ current r,(rank current).val=r+1 →
      (paidTree cost current (oracle current)).law=
        ((rows r).law.map (rowPayload rows candidate r)))
    (C N M ε δ : ℝ) (hC : 0<C) (hN : 0<N) (hδ : 0<δ)
    (hM : 1/Real.sqrt (popt q)≤M)
    (hrow : ∀ j,0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j))
    (hε : 0≤ε) (hrowBad : ∀ r,rowBadMean rows r≤ε) (hunion : (L:ℝ)*ε≤1/6)
    (fuel B initialFee : ℕ) (hfuel : ∀ i,(rank i).val≤fuel) (fallback : I) (hinitFee : (initialFee:ℝ)≤C*N)
    (hbudget : 15*C*M*N≤(B:ℝ)) :
    let actual :=
        freshNative cost (initializedRun cost p oracle fuel B initialFee fallback)
        (outerIterations δ)
    actual.probability (fun b => b.best.map (fun i => (rank i).val)≠some 0)≤δ ∧
      actual.All (fun b => b.totalPaid≤outerIterations δ*B) := by
  have hi:=source_initial_fee_funded hL (p.map rank) q hq h0 C N M hC hN hM
    B initialFee hinitFee hbudget
  have hphys:=initializedRun_failure_le_risk cost rank hzero horder p oracle hno rows
    candidate hnext hjoint fuel B initialFee fallback hfuel hi
  have hrisk:=initialized_risk_half hL (p.map rank) q hq h0 hnn rows hlaw C N M ε hC hN hM
    hrow hε hrowBad hunion B initialFee hinitFee hbudget
  exact native_amplified_run cost (fun i => (rank i).val) horder _ (hphys.trans hrisk) B
    (initializedRun_cap cost p oracle fuel B initialFee fallback) δ hδ

theorem causal_public_budget_theorem {L : ℕ} (hL : 0<L) (cost : I → ℝ) (rank : I → Fin L)
    (hzero : ∀ i,(rank i).val=0 ↔ ∀ j,cost i≤cost j)
    (horder : ∀ i j,(rank i).val<(rank j).val ↔ cost i<cost j)
    (p : PMF I) (q : ℕ → ℝ) (hq : ∀ i : Fin L,((p.map rank) i).toReal=q i.val)
    (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (oracle : I → Code I (Option I)) (hno : ∀ i,NoSave (oracle i))
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (candidate : (r : ℕ) → Fin (rows r).outcomes → I)
    (hnext : ∀ r a,(rank (candidate r a)).val=((rows r).next a).val)
    (hjoint : ∀ current r,(rank current).val=r+1 →
      (paidTree cost current (oracle current)).law=
        ((rows r).law.map (rowPayload rows candidate r)))
    (C N ε δ : ℝ) (hC : 0<C) (hN : 0<N) (hδ : 0<δ)
    (hrow : ∀ j,0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j))
    (hε : 0≤ε) (hrowBad : ∀ r,rowBadMean rows r≤ε) (hunion : (L:ℝ)*ε≤1/6)
    (fuel B initialFee : ℕ) (hfuel : ∀ i,(rank i).val≤fuel) (fallback : I) (hinitFee : (initialFee:ℝ)≤C*N)
    (hbudget : 15*C*N/Real.sqrt (popt q)≤(B:ℝ)) :
    let actual :=
        freshNative cost (initializedRun cost p oracle fuel B initialFee fallback)
        (outerIterations δ)
    actual.probability (fun b => b.best.map (fun i => (rank i).val)≠some 0)≤δ ∧
      actual.All (fun b => b.totalPaid≤outerIterations δ*B) := by
  have hb : 15*C*(1/Real.sqrt (popt q))*N≤(B:ℝ) := by
    convert hbudget using 1; ring
  exact causal_minimum_theorem hL cost rank hzero horder p q hq h0 hnn oracle hno
    rows hlaw candidate hnext hjoint C N (1/Real.sqrt (popt q)) ε δ hC hN hδ (le_refl _)
    hrow hε hrowBad hunion fuel B initialFee hfuel fallback hinitFee hb

end Qatlib.Papers.QAOAScaling23.MainResults
