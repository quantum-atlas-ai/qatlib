/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail
import Mathlib.Order.ConditionallyCompleteLattice.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.MonteCarloInt20.RiskPayoff.StrictTail

namespace Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall

def atomWeight {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) (x : X) : ℝ :=
  if L x=q then p.prob x else 0

def atomMass {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) : ℝ :=
    ∑ x,atomWeight p L q x

def QuantileBracket {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ) : Prop :=
  tailMass p L q≤α ∧ α≤tailMass p L q+atomMass p L q

def atomFraction {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ) : ℝ :=
  (α-tailMass p L q)/atomMass p L q

theorem atomMass_nonneg {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q : ℝ) : 0≤atomMass p L q := by
  apply Finset.sum_nonneg
  intro x _
  by_cases h : L x=q <;> simp [atomWeight,h,p.nonneg x]

theorem atomFraction_bounds {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) : atomFraction p L q α ∈ Set.Icc (0:ℝ) 1 := by
  by_cases hz : atomMass p L q=0
  · simp [atomFraction,hz]
  · have hp : 0<atomMass p L q := lt_of_le_of_ne (atomMass_nonneg p L q) (Ne.symm hz)
    exact ⟨div_nonneg (sub_nonneg.mpr h.1) hp.le,(div_le_one hp).2 (by linarith [h.2])⟩

theorem atomFraction_mass {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) : atomFraction p L q α*atomMass p L q=α-tailMass p L q := by
  by_cases hz : atomMass p L q=0
  · have he : α=tailMass p L q := by have := h.1; have := h.2; rw [hz,add_zero] at this; linarith [h.1]
    simp [atomFraction,hz,he]
  · exact div_mul_cancel₀ _ hz

def selectedWeight {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ) (x : X) : ℝ :=
  tailWeight p L q x+atomFraction p L q α*atomWeight p L q x

theorem selectedWeight_bounds {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) (x : X) : 0≤selectedWeight p L q α x ∧ selectedWeight p L q α x≤p.prob x := by
  have hf := atomFraction_bounds p L q α h
  by_cases ht : q<L x
  · have hn : L x≠q := ne_of_gt ht
    simp [selectedWeight,tailWeight,atomWeight,ht,hn,p.nonneg x]
  · by_cases he : L x=q
    · simp only [selectedWeight,tailWeight,atomWeight,he,lt_self_iff_false,↓reduceIte,zero_add]
      exact ⟨mul_nonneg hf.1 (p.nonneg x),(mul_le_mul_of_nonneg_right hf.2 (p.nonneg x)).trans_eq (one_mul _)⟩
    · simp [selectedWeight,tailWeight,atomWeight,ht,he,p.nonneg x]

theorem selectedWeight_sum {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) : ∑ x,selectedWeight p L q α x=α := by
  simp only [selectedWeight,Finset.sum_add_distrib,← Finset.mul_sum]
  change tailMass p L q+atomFraction p L q α*atomMass p L q=α
  rw [atomFraction_mass p L q α h]
  ring

theorem selectedWeight_loss {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) :
    ∑ x,selectedWeight p L q α x*L x=tailLoss p L q+q*(α-tailMass p L q) := by
  have hw (x : X) : selectedWeight p L q α x*L x=
      tailWeight p L q x*L x+q*(atomFraction p L q α*atomWeight p L q x) := by
    by_cases he : L x=q <;> simp only [selectedWeight,atomWeight,he,↓reduceIte] <;> ring
  simp_rw [hw]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change tailLoss p L q+q*(atomFraction p L q α*atomMass p L q)=_
  rw [atomFraction_mass p L q α h]

def selectedLaw {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (hα : 0<α) (h : QuantileBracket p L q α) : FinDist X where
  prob x := selectedWeight p L q α x/α
  nonneg x := div_nonneg (selectedWeight_bounds p L q α h x).1 hα.le
  sum_one := by rw [← Finset.sum_div,selectedWeight_sum p L q α h]; exact div_self hα.ne'

theorem selectedLaw_expect_weights {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : X → ℝ) (q α : ℝ) (hα : 0<α) (h : QuantileBracket p L q α) :
    (selectedLaw p L q α hα h).expect L=(∑ x,selectedWeight p L q α x*L x)/α := by
  simp only [FinDist.expect,selectedLaw,div_mul_eq_mul_div,Finset.sum_div]

theorem selectedLaw_mean {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : X → ℝ) (q α : ℝ) (hα : 0<α) (h : QuantileBracket p L q α) :
    (selectedLaw p L q α hα h).expect L=(tailLoss p L q+q*(α-tailMass p L q))/α := by
  rw [selectedLaw_expect_weights,selectedWeight_loss p L q α h]

def selectionMeans {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (α : ℝ) : Set ℝ :=
  {m | ∃ r : X → ℝ,(∀ x,0≤r x ∧ r x≤p.prob x) ∧ (∑ x,r x)=α ∧ m=(∑ x,r x*L x)/α}

theorem selectedWeight_optimal {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (q α : ℝ)
    (h : QuantileBracket p L q α) (r : X → ℝ) (hr : ∀ x,0≤r x ∧ r x≤p.prob x) (hm : ∑ x,r x=α) :
    ∑ x,r x*L x≤∑ x,selectedWeight p L q α x*L x := by
  have hp (x : X) : (r x-selectedWeight p L q α x)*(L x-q)≤0 := by
    by_cases ht : q<L x
    · have he : L x≠q := ne_of_gt ht
      have hw : selectedWeight p L q α x=p.prob x := by
        simp [selectedWeight,tailWeight,atomWeight,ht,he]
      rw [hw]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hr x).2) (sub_nonneg.mpr ht.le)
    · by_cases he : L x=q
      · simp [he]
      · have hw : selectedWeight p L q α x=0 := by simp [selectedWeight,tailWeight,atomWeight,ht,he]
        rw [hw,sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos (hr x).1 (sub_nonpos.mpr (le_of_not_gt ht))
  have hsum := Finset.sum_nonpos (fun x (_hx : x∈Finset.univ) => hp x)
  have heq : (∑ x,(r x-selectedWeight p L q α x)*(L x-q))=
      (∑ x,r x*L x)-(∑ x,selectedWeight p L q α x*L x)-q*((∑ x,r x)-(∑ x,selectedWeight p L q α x)) := by
    calc
      _ = ∑ x,((r x*L x-selectedWeight p L q α x*L x)-q*(r x-selectedWeight p L q α x)) :=
        Finset.sum_congr rfl (fun x _ => by ring)
      _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [heq,hm,selectedWeight_sum p L q α h,sub_self,mul_zero,sub_zero] at hsum
  exact sub_nonpos.mp hsum

theorem selectedLaw_isGreatest {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : X → ℝ) (q α : ℝ) (hα : 0<α) (h : QuantileBracket p L q α) :
    IsGreatest (selectionMeans p L α) ((selectedLaw p L q α hα h).expect L) := by
  refine ⟨⟨selectedWeight p L q α,selectedWeight_bounds p L q α h,selectedWeight_sum p L q α h,selectedLaw_expect_weights p L q α hα h⟩,?_⟩
  intro m hm
  obtain ⟨r,hr,hrm,rfl⟩ := hm
  rw [selectedLaw_expect_weights]
  exact div_le_div_of_nonneg_right (selectedWeight_optimal p L q α h r hr hrm) hα.le

def expectedShortfall {X : Type} [Fintype X] (p : FinDist X) (L : X → ℝ) (α : ℝ) : ℝ :=
  sSup (selectionMeans p L α)

theorem expectedShortfall_formula {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (L : X → ℝ) (q α : ℝ) (hα : 0<α) (h : QuantileBracket p L q α) :
    expectedShortfall p L α=(tailLoss p L q+q*(α-tailMass p L q))/α := by
  rw [expectedShortfall,(selectedLaw_isGreatest p L q α hα h).csSup_eq,selectedLaw_mean]

end Qatlib.Papers.MonteCarloInt20.RiskPayoff.ExpectedShortfall
