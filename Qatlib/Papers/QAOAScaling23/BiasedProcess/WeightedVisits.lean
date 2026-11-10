/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.Execution
import Qatlib.Papers.QAOAScaling23.WeightedCost.Telescope
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess
open scoped Classical
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.WeightedCost

def RowLaw (q : ℕ → ℝ) (rows : (r : ℕ) → Row r) : Prop :=
  ∀ r (j : Fin (r+1)),
    (∑ a, if (rows r).next a=j then ((rows r).law a).toReal else 0)=
      q j.val / prefixSum q (r+1)

theorem row_next_mean (q : ℕ → ℝ) (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows)
    (r : ℕ) (f : ℕ → ℝ) :
    (∑ a, ((rows r).law a).toReal * f ((rows r).next a).val)=
      ∑ j : Fin (r+1), (q j.val / prefixSum q (r+1))*f j.val := by
  have hpoint (a : Fin (rows r).outcomes) :
      ((rows r).law a).toReal * f ((rows r).next a).val =
        ∑ j : Fin (r+1), (if (rows r).next a=j then ((rows r).law a).toReal else 0)*f j.val := by
    simp [eq_comm]
  calc
    _ = ∑ a, ∑ j : Fin (r+1), (if (rows r).next a=j then ((rows r).law a).toReal else 0)*f j.val :=
      Finset.sum_congr rfl (fun a _ => hpoint a)
    _ = ∑ j : Fin (r+1), (∑ a, if (rows r).next a=j then ((rows r).law a).toReal else 0)*f j.val := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Finset.sum_mul _ _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hlaw r j]

theorem prefix_positive (q : ℕ → ℝ) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (k : ℕ) (hk : 0<k) : 0<prefixSum q k := by
  have h : q 0≤prefixSum q k :=
    Finset.single_le_sum (fun j _ => hnn j) (by simpa using hk)
  exact h0.trans_le h

def hitValue (q : ℕ → ℝ) (j r : ℕ) : ℝ :=
  if r<j then 0 else if r=j then 1 else q j / prefixSum q (j+1)

theorem weighted_harmonic (q : ℕ → ℝ) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (j r : ℕ) (hr : j<r) :
    (∑ i : Fin r, q i.val * hitValue q j i.val)=
      prefixSum q r * (q j / prefixSum q (j+1)) := by
  revert hr
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
    intro hr
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin r, q i.val*hitValue q j i.val)+q r*hitValue q j r = _
    by_cases hjr : j<r
    · rw [ih hjr]
      have hneq : r≠j := by omega
      simp only [hitValue,show ¬r<j by omega,hneq,if_false]
      rw [show prefixSum q (r+1)=prefixSum q r+q r by simp [prefixSum,Finset.sum_range_succ]]
      change prefixSum q r * (q j/prefixSum q (j+1)) + q r * (q j/prefixSum q (j+1)) = _
      ring
    · have hj : j=r := by omega
      subst j
      have hz : (∑ i : Fin r, q i.val*hitValue q r i.val)=0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [hitValue,i.isLt]
      rw [hz]
      simp only [hitValue,lt_self_iff_false,if_false,if_true,mul_one,zero_add]
      have hp := prefix_positive q h0 hnn (r+1) (by omega)
      field_simp

theorem visits_prepend (j r cost sample : ℕ) (bad : Bool) (tr : Trace) :
    visits j (prepend r cost bad sample tr) = (if r=j then 1 else 0)+visits j tr := by
  by_cases h : r=j
  · subst r
    simp [visits,prepend,add_comm]
  · simp [visits,prepend,h]

theorem descend_visit_mean (q : ℕ → ℝ) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows) (j r : ℕ) :
    (descend rows r).mean (visits j)=hitValue q j r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      by_cases hj : j=0
      · subst j; simp [descend,Tree.mean,visits,hitValue]
      · have hjp : 0<j := by omega
        simp [descend,Tree.mean,visits,hitValue,hjp,show 0≠j by omega]
    | succ r =>
      rw [descend]
      change (∑ a, ((rows r).law a).toReal *
        ((descend rows ((rows r).next a).val).map _).mean (visits j)) = _
      simp_rw [Tree.mean_map,visits_prepend]
      simp_rw [Tree.mean_add,Tree.mean_const]
      simp_rw [ih _ ((rows r).next _).isLt]
      simp only [mul_add,Finset.sum_add_distrib]
      simp only [← Finset.sum_mul,Tree.weights_sum,one_mul]
      rw [row_next_mean q rows hlaw r (hitValue q j)]
      have hp := prefix_positive q h0 hnn (r+1) (by omega)
      by_cases hlt : r+1<j
      · have hz : (∑ i : Fin (r+1), (q i.val/prefixSum q (r+1))*hitValue q j i.val)=0 := by
          apply Finset.sum_eq_zero
          intro i _
          simp [hitValue,show i.val<j by omega]
        rw [hz]
        simp only [hitValue,hlt,show r+1≠j by omega,if_true,if_false,zero_add]
      · by_cases heq : r+1=j
        · subst j
          have hz : (∑ i : Fin (r+1), (q i.val/prefixSum q (r+1))*hitValue q (r+1) i.val)=0 := by
            apply Finset.sum_eq_zero
            intro i _
            simp [hitValue,i.isLt]
          rw [hz]
          simp [hitValue]
        · have hj : j<r+1 := by omega
          have wh := weighted_harmonic q h0 hnn j (r+1) hj
          have hsum : (∑ i : Fin (r+1), (q i.val/prefixSum q (r+1))*hitValue q j i.val)=
              q j/prefixSum q (j+1) := by
            simp_rw [div_mul_eq_mul_div]
            rw [← Finset.sum_div,wh]
            field_simp [ne_of_gt hp]
          simpa only [hitValue,hlt,heq,if_false,zero_add] using hsum

theorem initialized_visit_mean {L : ℕ} (p : PMF (Fin L)) (q : ℕ → ℝ)
    (hq : ∀ i : Fin L, (p i).toReal=q i.val) (h0 : 0<q 0) (hnn : ∀ j,0≤q j)
    (rows : (r : ℕ) → Row r) (hlaw : RowLaw q rows) (j : Fin L) :
    (initialized p rows).mean (visits j.val)=q j.val/prefixSum q (j.val+1) := by
  change (∑ i : Fin L, (p i).toReal*(descend rows i.val).mean (visits j.val)) = _
  simp_rw [hq,descend_visit_mean q h0 hnn rows hlaw]
  rw [weighted_harmonic q h0 hnn j.val L j.isLt]
  have hs : prefixSum q L=1 := by
    rw [prefixSum,← Fin.sum_univ_eq_sum_range q L]
    simp_rw [← hq]
    exact Tree.weights_sum p
  rw [hs,one_mul]
end Qatlib.Papers.QAOAScaling23.BiasedProcess
