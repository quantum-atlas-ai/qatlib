/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.CausalSearch.MinimumCode
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.CausalSearch
open scoped Classical ENNReal
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open BiasedProcess WeightedCost BudgetPrefix

def initializedRisk {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) : ℝ :=
  (initialized p rows).probability (fun tr => tr.oracleBad=true ∨ B < initialFee+paid tr)

theorem initialized_risk_union {L : ℕ} (p : PMF (Fin L)) (rows : (r : ℕ) → Row r)
    (B initialFee : ℕ) : initializedRisk p rows B initialFee≤
      (initialized p rows).mean badIndicator+
      (initialized p rows).mean (overflowIndicator B initialFee) := by
  rw [initializedRisk,Tree.probability,← Tree.mean_add]
  apply Tree.mean_mono
  apply Tree.all_of_forall
  intro tr
  by_cases hb : tr.oracleBad=true
  · simp only [hb,true_or,if_true,badIndicator]
    have h : 0≤overflowIndicator B initialFee tr := by
      unfold overflowIndicator
      split_ifs <;> norm_num
    linarith
  · by_cases ho : B < initialFee+paid tr
    · have hor : (B:ℝ)<fullCost initialFee tr := by
        unfold fullCost
        exact_mod_cast ho
      simp [hb,ho,badIndicator,overflowIndicator,hor]
    · have hor : ¬(B:ℝ)<fullCost initialFee tr := by
        unfold fullCost
        exact_mod_cast ho
      simp [hb,ho,badIndicator,overflowIndicator,hor]

theorem initialized_risk_half {L : ℕ} (hL : 0<L) (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L,(p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (C N M ε : ℝ) (hC : 0<C) (hN : 0<N)
    (hM : 1/Real.sqrt (popt q)≤M)
    (hrow : ∀ j,0<j → rowCharge rows j≤2*C*N/Real.sqrt (prefixSum q j))
    (hε : 0≤ε) (hrowBad : ∀ r,rowBadMean rows r≤ε) (hunion : (L:ℝ)*ε≤1/6)
    (B initialFee : ℕ) (hinitFee : (initialFee:ℝ)≤C*N) (hbudget : 15*C*M*N≤(B:ℝ)) :
    initializedRisk p rows B initialFee≤1/2 := by
  have hq01 : q 0≤1 := by
    have h := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞)≠⊤) (PMF.coe_le_one p ⟨0,hL⟩)
    simpa only [hq,Fin.val_zero,ENNReal.toReal_one] using! h
  have hsq : 0 < Real.sqrt (popt q) := Real.sqrt_pos.2 h0
  have hsq1 : Real.sqrt (popt q)≤1 := by
    simpa only [popt,Real.sqrt_one] using! Real.sqrt_le_sqrt hq01
  have hM1 : 1≤M := ((one_le_div hsq).2 hsq1).trans hM
  have hCN : 0<C*N := mul_pos hC hN
  have hCNM : C*N≤C*M*N := by nlinarith [mul_le_mul_of_nonneg_left hM1 hCN.le]
  have hBr : 0<(B:ℝ) := by
    have hpos : 0<15*C*M*N := by positivity
    exact hpos.trans_le hbudget
  have hcost := actual_paid_bound hL p q hq h0 hnn rows hlaw C N hC hN.le hrow
  have htotal : (initialized p rows).mean (fullCost initialFee)≤5*C*M*N := by
    have he : (initialized p rows).mean (fullCost initialFee)=
        (initialFee:ℝ)+(initialized p rows).mean (fun tr => (paid tr:ℝ)) := by
      unfold fullCost
      simp only [Nat.cast_add,Tree.mean_add,Tree.mean_const]
    rw [he]
    have hs : 4*C*N/Real.sqrt (popt q)≤4*C*M*N := by
      have h:=mul_le_mul_of_nonneg_left hM (show 0≤4*C*N by positivity)
      convert! h using 1 <;> ring
    linarith
  have hover := actual_overflow_bound p rows B initialFee (by exact_mod_cast hBr)
  have hoverthird : (initialized p rows).mean (overflowIndicator B initialFee)≤1/3 := by
    apply hover.trans
    rw [div_le_iff₀ hBr]
    nlinarith [htotal,hbudget]
  have hbad := (initialized_bad_bound p rows ε hε hrowBad).trans hunion
  have hu := initialized_risk_union p rows B initialFee
  linarith
end Qatlib.Papers.QAOAScaling23.CausalSearch
