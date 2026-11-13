/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.VariableTimeAmplificationDefs
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.GroverLowerBoundInstance
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.LowerBoundModels
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Overlap products and variable-time amplification bounds

This module derives overlap identities, gain-product estimates, and stage-time bounds for the
variable-time amplification analysis of [Ambainis2012]. The structure `VtOverlapChain` records
the overlap recurrence and endpoint identities; these yield the Lemma 3 product bound and the
equation (5) and (6) time estimates.

The module also relates the Grover hard-family norm to `groverRatio` and selects a dimension
whose ratio is comparable to a prescribed probability.

## Main statements

* `lemma3_product_bound`: Bound the remaining gain product using remaining stopping mass and
  success probability.
* `eq5_eq6_time_bounds`: Obtain both stagewise and unrolled time bounds.
* `clause63_endpoint`: Combine the hard-family norm identities and dimension-selection estimate.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

open Matrix Qatlib
open scoped Classical BigOperators

/-- A variable-time stage chain equipped with real overlaps satisfying a multiplicative step
recurrence and specified initial and final overlap identities. -/
structure VtOverlapChain (m : ℕ) where

  chain : VtStageChain m

  overlap : ℕ → ℕ → ℝ

  step : ∀ i j, 1 ≤ i → i < j → j ≤ m →
    overlap i j = overlap i (j - 1) *
      ((chain.stage j).ampWeight / (chain.stage j).baseWeight)

  head : ∀ i, 1 ≤ i → i ≤ m →
    overlap i i = (chain.stage i).ampWeight *
      (chain.psuccUpTo i /
        (chain.psuccUpTo i + remainingStopMass m chain.stopMass i))

  last : ∀ i, 1 ≤ i → i ≤ m →
    overlap i m = (chain.stage m).ampWeight * (chain.psuccUpTo i / chain.psucc)

/-- For `1 ≤ i ≤ j ≤ m`, the overlap from `i` to `j` equals its initial overlap times the
product of the intervening amplified-to-base weight ratios. -/
theorem VtOverlapChain.overlap_unroll {m : ℕ} (oc : VtOverlapChain m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) :
    ∀ j : ℕ, i ≤ j → j ≤ m →
      oc.overlap i j = oc.overlap i i *
        (∏ k ∈ Finset.Ico (i + 1) (j + 1),
          (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj1 hj2
    by_cases hj : j = i
    · subst hj
      simp
    · have hstep := oc.step i j h1 (by omega) hj2
      have hnorm : (j - 1) + 1 = j := by omega
      have hih := ih (j - 1) (by omega) (by omega) (by omega)
      rw [hstep, hih, hnorm]
      have hprod : (∏ k ∈ Finset.Ico (i + 1) (j + 1),
            (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight)
          = (∏ k ∈ Finset.Ico (i + 1) j,
            (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight) *
            ((oc.chain.stage (j)).ampWeight / (oc.chain.stage (j)).baseWeight) :=
        Finset.prod_Ico_succ_top (by omega) _
      rw [hprod]
      ring

/-- Every initial overlap with index between one and `m` is strictly positive. -/
theorem VtOverlapChain.head_pos {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) : 0 < oc.overlap i i := by
  have hamp : 0 < (oc.chain.stage i).ampWeight := by
    have hf := oc.chain.ampFloor hm h1 h2
    have h1' : 0 < 1 / (9 * (m : ℝ)) := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm'' : (0 : ℝ) < m := by linarith
      positivity
    exact lt_of_lt_of_le h1' hf
  have hsucc : 0 < oc.chain.psuccUpTo i := oc.chain.psuccUpToPos i h1 h2
  have htail : 0 ≤ remainingStopMass m oc.chain.stopMass i := by
    unfold remainingStopMass
    exact Finset.sum_nonneg fun j _ => by
      by_cases h : i < j
      · simp only [h, if_pos]
        exact oc.chain.stopMassNonneg j
      · simp only [h]
        exact le_rfl
  have hden : 0 < oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i := by
    linarith
  rw [oc.head i h1 h2]
  have hdiv : 0 < oc.chain.psuccUpTo i /
      (oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i) :=
    div_pos hsucc hden
  exact mul_pos hamp hdiv

/-- For `1 ≤ i ≤ m`, the product of amplified-to-base weight ratios after stage `i` equals the
final overlap divided by the initial overlap. -/
theorem VtOverlapChain.prod_eq_overlap_ratio {m : ℕ} (oc : VtOverlapChain m)
    (hm : 1 ≤ m) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    (∏ k ∈ Finset.Ico (i + 1) (m + 1),
      (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight)
      = oc.overlap i m / oc.overlap i i := by
  have hpos := oc.head_pos hm h1 h2
  have hunroll := oc.overlap_unroll h1 h2 m h2 (Nat.le_refl m)
  have hne : oc.overlap i i ≠ 0 := ne_of_gt hpos
  rw [eq_div_iff hne]
  rw [hunroll]
  ring

/-- For `1 ≤ i ≤ m`, the final-to-initial overlap ratio factors into the final-to-stage
amplified weight ratio and the ratio of accumulated success plus remaining stopping mass to
total success. -/
theorem VtOverlapChain.overlap_ratio_identity {m : ℕ} (oc : VtOverlapChain m)
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    oc.overlap i m / oc.overlap i i
      = ((oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight) *
        ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
          / oc.chain.psucc) := by
  have hampi : (oc.chain.stage i).ampWeight ≠ 0 := by
    have hfloor := oc.chain.ampFloor (m := m) (by omega) h1 h2
    have h1' : 0 < 1 / (9 * (m : ℝ)) := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast (by omega)
      have hm'' : (0 : ℝ) < m := by linarith
      positivity
    exact ne_of_gt (lt_of_lt_of_le h1' hfloor)
  have hsuccPos : 0 < oc.chain.psuccUpTo i := oc.chain.psuccUpToPos i h1 h2
  have hsucc : oc.chain.psuccUpTo i ≠ 0 := ne_of_gt hsuccPos
  have hsucc' : oc.chain.psucc ≠ 0 := ne_of_gt oc.chain.psuccPos
  have htail : 0 ≤ remainingStopMass m oc.chain.stopMass i := by
    unfold remainingStopMass
    exact Finset.sum_nonneg fun j _ => by
      by_cases h : i < j
      · simp only [h, if_pos]
        exact oc.chain.stopMassNonneg j
      · simp only [h]
        exact le_rfl
  have hden : oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i ≠ 0 := by
    have hpos : 0 < oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i := by
      linarith
    exact ne_of_gt hpos
  rw [oc.last i h1 h2, oc.head i h1 h2]
  field_simp

/-- For `1 ≤ i ≤ m`, the gain-ratio product after stage `i` is at most `3 * (1 +
√(remainingStopMass / psucc))`, as in Lemma 3 of [Ambainis2012]. -/
theorem lemma3_product_bound {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
      (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1)
      ≤ lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := by
  have htail : 0 ≤ remainingStopMass m oc.chain.stopMass i := by
    unfold remainingStopMass
    exact Finset.sum_nonneg fun j _ => by
      by_cases h : i < j
      · simp only [h, if_pos]
        exact oc.chain.stopMassNonneg j
      · simp only [h]
        exact le_rfl
  have hsuccpos : 0 < oc.chain.psucc := oc.chain.psuccPos

  have hampm : (oc.chain.stage m).ampWeight ≤ 1 / (m : ℝ) :=
    oc.chain.ampCap (by omega) (Nat.le_refl m)
  have hampi : 1 / (9 * (m : ℝ)) ≤ (oc.chain.stage i).ampWeight :=
    oc.chain.ampFloor hm h1 h2
  have hmm : (0 : ℝ) < m := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hampipos : 0 < (oc.chain.stage i).ampWeight := by
    have h1' : 0 < 1 / (9 * (m : ℝ)) := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm'' : (0 : ℝ) < m := by linarith
      positivity
    exact lt_of_lt_of_le h1' hampi
  have hratio : (oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight ≤ 9 := by
    rw [div_le_iff₀ hampipos]
    have hden : (oc.chain.stage m).ampWeight
        ≤ 9 * (oc.chain.stage i).ampWeight := by
      calc (oc.chain.stage m).ampWeight ≤ 1 / (m : ℝ) := hampm
        _ = 9 * (1 / (9 * (m : ℝ))) := by
          have hm0 : (m : ℝ) ≠ 0 := by linarith
          field_simp
        _ ≤ 9 * (oc.chain.stage i).ampWeight := by
          exact mul_le_mul_of_nonneg_left hampi (by norm_num)
    exact hden

  have hmono : oc.chain.psuccUpTo i ≤ oc.chain.psucc := oc.chain.psuccUpTo_le i h1 h2
  have hfactorNonneg : 0 ≤ (oc.chain.psuccUpTo i
      + remainingStopMass m oc.chain.stopMass i) / oc.chain.psucc := by
    have hpos : 0 ≤ oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i := by
      have := oc.chain.psuccUpToPos i h1 h2
      linarith [htail]
    exact div_nonneg hpos (le_of_lt hsuccpos)
  have hfactor : (oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
      / oc.chain.psucc
      ≤ 1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc := by
    rw [div_le_iff₀ hsuccpos]
    have heq : (1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)
          * oc.chain.psucc
        = oc.chain.psucc + remainingStopMass m oc.chain.stopMass i := by
      field_simp
    rw [heq]
    linarith

  have hsqrtratio : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      gainRatio (oc.chain.stage k).ampWeight (oc.chain.stage k).baseWeight
        = Real.sqrt ((oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight) := by
    intro k hk1 hk2
    unfold gainRatio
    have hnonneg : 0 ≤ (oc.chain.stage k).ampWeight := by
      have hfloor := oc.chain.ampFloor hm hk1 hk2
      have h1' : 0 < 1 / (9 * (m : ℝ)) := by
        have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hm'' : (0 : ℝ) < m := by linarith
        positivity
      exact le_of_lt (lt_of_lt_of_le h1' hfloor)
    rw [Real.sqrt_div (x := (oc.chain.stage k).ampWeight) hnonneg
      (oc.chain.stage k).baseWeight]
  have hbounds : ∀ k ∈ Finset.Ico (i + 1) (m + 1), 1 ≤ k ∧ k ≤ m := by
    intro k hk
    have hkmem := Finset.mem_Ico.mp hk
    omega
  have hprod_sqrt : (∏ k ∈ Finset.Ico (i + 1) (m + 1),
        gainRatio (oc.chain.stage k).ampWeight (oc.chain.stage k).baseWeight)
      = Real.sqrt (∏ k ∈ Finset.Ico (i + 1) (m + 1),
        (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight) := by
    have hnonneg : ∀ k ∈ Finset.Ico (i + 1) (m + 1),
        0 ≤ (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight := by
      intro k hk
      have hkmem := Finset.mem_Ico.mp hk
      have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ m := by omega
      have hbase := oc.chain.baseWeight_pos hk1 hk2
      have hamp := oc.chain.ampFloor hm hk1 hk2
      have h1' : 0 < 1 / (9 * (m : ℝ)) := by
        have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hm'' : (0 : ℝ) < m := by linarith
        positivity
      exact div_nonneg (le_of_lt (lt_of_lt_of_le h1' hamp)) (le_of_lt hbase)
    rw [Finset.prod_congr rfl fun k hk => hsqrtratio k (hbounds k hk).1 (hbounds k hk).2]
    exact prod_sqrt _ _ hnonneg
  have hprodpos : 0 ≤ (∏ k ∈ Finset.Ico (i + 1) (m + 1),
      (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight) := by
    refine Finset.prod_nonneg fun k hk => ?_
    have hkmem := Finset.mem_Ico.mp hk
    have hk1 : 1 ≤ k := by omega
    have hk2 : k ≤ m := by omega
    have hfloor := oc.chain.ampFloor hm hk1 hk2
    have h1' : 0 < 1 / (9 * (m : ℝ)) := by
      have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hm'' : (0 : ℝ) < m := by linarith
      positivity
    exact div_nonneg (le_of_lt (lt_of_lt_of_le h1' hfloor))
      (le_of_lt (oc.chain.baseWeight_pos hk1 hk2))

  have hprod := oc.prod_eq_overlap_ratio hm h1 h2
  have hid := oc.overlap_ratio_identity h1 h2
  have hbound : (∏ k ∈ Finset.Ico (i + 1) (m + 1),
        (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight)
      ≤ 9 * (1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc) := by
    calc (∏ k ∈ Finset.Ico (i + 1) (m + 1),
          (oc.chain.stage k).ampWeight / (oc.chain.stage k).baseWeight)
        = (oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight *
            ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
              / oc.chain.psucc) := by
          rw [hprod, hid]
        _ ≤ 9 * ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
            / oc.chain.psucc) := by
          exact mul_le_mul_of_nonneg_right hratio hfactorNonneg
        _ ≤ 9 * (1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc) := by
          exact mul_le_mul_of_nonneg_left hfactor (by norm_num : (0 : ℝ) ≤ 9)
  have hnonneg : 0 ≤ 9 * (1 + remainingStopMass m oc.chain.stopMass i
      / oc.chain.psucc) := by
    positivity
  have hsqrtbound : Real.sqrt (9 * (1 + remainingStopMass m oc.chain.stopMass i
      / oc.chain.psucc))
      ≤ 3 * (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) := by
    have hsq : 9 * (1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)
        ≤ (3 * (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i
            / oc.chain.psucc))) ^ 2 := by
      have h1 : 0 ≤ remainingStopMass m oc.chain.stopMass i / oc.chain.psucc := by
        positivity
      have h3 : (Real.sqrt (remainingStopMass m oc.chain.stopMass i
          / oc.chain.psucc)) ^ 2
          = remainingStopMass m oc.chain.stopMass i / oc.chain.psucc :=
        Real.sq_sqrt h1
      nlinarith [Real.sqrt_nonneg (remainingStopMass m oc.chain.stopMass i
        / oc.chain.psucc)]
    have h := (Real.sqrt_le_sqrt_iff (by positivity)).2 hsq
    rwa [Real.sqrt_sq (by positivity)] at h
  have hbound' : (oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight *
      ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
        / oc.chain.psucc)
      ≤ 9 * (1 + remainingStopMass m oc.chain.stopMass i / oc.chain.psucc) := by
    rw [hprod, hid] at hbound
    exact hbound
  unfold gainRatioProduct
  rw [hprod_sqrt]
  rw [hprod, hid]
  have hmain : Real.sqrt ((oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight *
      ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
        / oc.chain.psucc))
      ≤ Real.sqrt (9 * (1 + remainingStopMass m oc.chain.stopMass i
          / oc.chain.psucc)) :=
    (Real.sqrt_le_sqrt_iff hnonneg).2 hbound'
  have hfinal : Real.sqrt ((oc.chain.stage m).ampWeight / (oc.chain.stage i).ampWeight *
      ((oc.chain.psuccUpTo i + remainingStopMass m oc.chain.stopMass i)
        / oc.chain.psucc))
      ≤ 3 * (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i
          / oc.chain.psucc)) :=
    hmain.trans hsqrtbound
  have hgoal : 3 * (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i
      / oc.chain.psucc))
      = lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := rfl
  exact hfinal.trans_eq hgoal

/-- For `1 ≤ i ≤ m`, the gain product starting at `i` factors into the gain at `i` and the
product starting at `i + 1`. -/
theorem lemma3_product_bound_with_stage_gain {m : ℕ} (oc : VtOverlapChain m)
    (hm : 1 ≤ m) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
        (fun j => (oc.chain.stage j).baseWeight) i (m + 1)
      = gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
        gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1) :=
  clause89_prod_peel (fun j => (oc.chain.stage j).ampWeight)
    (fun j => (oc.chain.stage j).baseWeight) i (m + 1) (by omega)

/-- For a nonempty stage chain, establish the stagewise equation (5) time inequalities and the
unrolled equation (6) bound with overhead `(1 + 1 / (3m - 1)) ^ m`. [Ambainis2012] -/
theorem eq5_eq6_time_bounds {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m) :
    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      chain.time i ≤ eq5StageTimeBound m (chain.stage i).ampWeight
        (chain.stage i).baseWeight (chain.time (i - 1)) i) ∧
    chain.time m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct (fun j => (chain.stage j).ampWeight)
          (fun j => (chain.stage j).baseWeight) 1 (m + 1) * chain.time 0 +
        eq6ProductSum (fun j => (chain.stage j).ampWeight)
          (fun j => (chain.stage j).baseWeight) m) := by
  have h := clause89_event_bounds m (fun j => (chain.stage j).ampWeight)
    (fun j => (chain.stage j).baseWeight) (fun j => (chain.stage j).oddMultiplier)
    chain.time hm
    (fun j hj1 hj2 => chain.baseWeight_pos hj1 hj2)
    (fun j hj1 hj2 => chain.ampFloor hm hj1 hj2)
    (fun j hj1 hj2 => by
      have hw := chain.ampWindow hm hj1 hj2
      simpa [VtStage.oddCalls] using! hw)
    chain.timeZero
    (fun i hi1 hi2 => by
      have hr := chain.timeRec i hi1 hi2
      simpa [VtStage.oddCalls] using! hr)
  refine ⟨h.1, ?_⟩
  exact h.2

/-- The product-weighted time sum in equation (6) is at most the sum of `3 * gainRatio` times `1
+ √(remainingStopMass / psucc)` and the corresponding dyadic stage cost. [Ambainis2012] -/
theorem eq6_product_sum_le {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) :
    eq6ProductSum (fun j => (oc.chain.stage j).ampWeight)
      (fun j => (oc.chain.stage j).baseWeight) m
      ≤ ∑ i ∈ Finset.Ico 1 (m + 1),
        (3 : ℝ) * (gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
          (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) *
          (2 : ℝ) ^ ((i : ℕ) - 1)) := by
  have hstep : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) i (m + 1)
        = gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
          gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
            (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1) := by
    intro i hi1 hi2
    exact clause89_prod_peel (fun j => (oc.chain.stage j).ampWeight)
      (fun j => (oc.chain.stage j).baseWeight) i (m + 1) (by omega)
  have hlem : ∀ i : ℕ, 1 ≤ i → i ≤ m →
      gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1)
        ≤ lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc := by
    intro i hi1 hi2
    exact lemma3_product_bound oc hm hi1 hi2
  unfold eq6ProductSum
  refine Finset.sum_le_sum fun i hi => ?_
  have himem := Finset.mem_Ico.mp hi
  have hi1 : 1 ≤ i := himem.1
  have hi2 : i ≤ m := by omega
  have hrhs : lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc
      = 3 * (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i
          / oc.chain.psucc)) := rfl
  calc gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) i (m + 1) * (2 : ℝ) ^ ((i : ℕ) - 1)
      = gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
          gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
            (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1) *
          (2 : ℝ) ^ ((i : ℕ) - 1) := by rw [hstep i hi1 hi2]
    _ ≤ gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
          lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc *
          (2 : ℝ) ^ ((i : ℕ) - 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlem i hi1 hi2)
            (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
          (by positivity)
    _ = (3 : ℝ) * (gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
          (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) *
          (2 : ℝ) ^ ((i : ℕ) - 1)) := by rw [hrhs]; ring

/-- Package the stagewise equation (5) inequalities and the unrolled equation (6) time estimate
for a nonempty variable-time stage chain. [Ambainis2012] -/
theorem clause89_endpoint {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m) :
    (∀ i : ℕ, 1 ≤ i → i ≤ m →
      chain.time i ≤ eq5StageTimeBound m (chain.stage i).ampWeight
        (chain.stage i).baseWeight (chain.time (i - 1)) i) ∧
    chain.time m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct (fun j => (chain.stage j).ampWeight)
          (fun j => (chain.stage j).baseWeight) 1 (m + 1) * chain.time 0 +
        eq6ProductSum (fun j => (chain.stage j).ampWeight)
          (fun j => (chain.stage j).baseWeight) m) :=
  eq5_eq6_time_bounds chain hm

/-- For an overlap chain and `1 ≤ i ≤ m`, the remaining gain product satisfies the Lemma 3 bound
in terms of remaining stopping mass and total success. [Ambainis2012] -/
theorem clause68_endpoint {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) :
    gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
      (fun j => (oc.chain.stage j).baseWeight) (i + 1) (m + 1)
      ≤ lemma3Rhs (remainingStopMass m oc.chain.stopMass i) oc.chain.psucc :=
  lemma3_product_bound oc hm h1 h2

/-- For a nonempty overlap chain, bound the final time by the overhead factor times the sum of
the initial-time gain product and the explicit stopping-mass-weighted dyadic sum.
[Ambainis2012] -/
theorem clause64_endpoint {m : ℕ} (oc : VtOverlapChain m) (hm : 1 ≤ m) :
    oc.chain.time m ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
        (gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
          (fun j => (oc.chain.stage j).baseWeight) 1 (m + 1) * oc.chain.time 0 +
        ∑ i ∈ Finset.Ico 1 (m + 1),
          (3 : ℝ) * (gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
            (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) *
            (2 : ℝ) ^ ((i : ℕ) - 1))) := by
  have htime := eq5_eq6_time_bounds oc.chain hm
  have hsum := eq6_product_sum_le oc hm
  calc oc.chain.time m
      ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
          (gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
            (fun j => (oc.chain.stage j).baseWeight) 1 (m + 1) * oc.chain.time 0 +
          eq6ProductSum (fun j => (oc.chain.stage j).ampWeight)
            (fun j => (oc.chain.stage j).baseWeight) m) := htime.2
    _ ≤ (1 + 1 / (3 * (m : ℝ) - 1)) ^ m *
          (gainRatioProduct (fun j => (oc.chain.stage j).ampWeight)
            (fun j => (oc.chain.stage j).baseWeight) 1 (m + 1) * oc.chain.time 0 +
          ∑ i ∈ Finset.Ico 1 (m + 1),
            (3 : ℝ) * (gainRatio (oc.chain.stage i).ampWeight (oc.chain.stage i).baseWeight *
              (1 + Real.sqrt (remainingStopMass m oc.chain.stopMass i / oc.chain.psucc)) *
              (2 : ℝ) ^ ((i : ℕ) - 1))) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [hsum]
      · have hden : 0 < 3 * (m : ℝ) - 1 := by
          have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
          linarith
        have hinv : 0 ≤ 1 / (3 * (m : ℝ) - 1) := by positivity
        have hbase : 1 ≤ 1 + 1 / (3 * (m : ℝ) - 1) := by linarith
        positivity

/-- The hard-family squared-norm expression in dimension `d` equals `d * groverRatio d`. -/
theorem hard_family_norm_ratio_identity (d : ℕ) :
    hardFamilySolutionNormSq d = (d : ℝ) * groverRatio d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [hardFamilySolutionNormSq, groverRatio]
  · unfold hardFamilySolutionNormSq groverRatio
    field_simp

/-- The hard-family squared-norm expression at the cardinality of a finite nonempty type equals
the squared norm of the Grover-inverse target for any marked index. -/
theorem hard_family_actual_norm {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (x : I) :
    hardFamilySolutionNormSq (Fintype.card I)
      = ‖stateVector (groverInverse (I := I) *ᵥ bState x)‖ ^ 2 := by
  have h := grover_solution_norm_sq x
  simpa [hardFamilySolutionNormSq] using! h.symm

/-- For each `0 < p < 1`, there is a dimension `d ≥ 150` with `p / 38 ≤ groverRatio d ≤ 5 * p`. -/
theorem hard_family_dimension_selection (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ d : ℕ, 150 ≤ d ∧ p / 38 ≤ groverRatio d ∧ groverRatio d ≤ 5 * p := by
  have hceil_le : (1 / p : ℝ) ≤ Nat.ceil (1 / p) := Nat.le_ceil _
  have hceil_lt : (Nat.ceil (1 / p) : ℝ) < 1 / p + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  set d : ℕ := Nat.max 150 (Nat.ceil (1 / p)) with hd
  have hd150 : (150 : ℕ) ≤ d := Nat.le_max_left _ _
  have hDge : (1 / p : ℝ) ≤ (d : ℝ) := by
    rw [hd, Nat.cast_max]
    exact le_max_iff.mpr (Or.inr hceil_le)
  have hDle : (d : ℝ) ≤ 152 / p := by
    rw [hd, Nat.cast_max]
    have h150 : (150 : ℝ) ≤ 152 / p := by
      have hmul := mul_le_mul_of_nonneg_right (le_of_lt hp1) (by norm_num : (0 : ℝ) ≤ 150)
      field_simp
      nlinarith
    have hceil : (Nat.ceil (1 / p) : ℝ) ≤ 152 / p := by
      have h2 : 1 / p + 1 ≤ 152 / p := by
        have hmul := mul_le_mul_of_nonneg_right (le_of_lt hp1) (by norm_num : (0 : ℝ) ≤ 1)
        field_simp
        nlinarith
      exact le_trans (le_of_lt hceil_lt) h2
    calc max (150 : ℝ) (Nat.ceil (1 / p)) ≤ max (152 / p) (152 / p) := by gcongr
      _ = 152 / p := max_self _
  have hDpos : (0 : ℝ) < (d : ℝ) := by
    have : (150 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd150
    linarith
  have hD8 : (8 : ℝ) ≤ (d : ℝ) := by
    have : (150 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd150
    linarith
  have hbounds := grover_ratio_bounds (d : ℝ) hD8
  have hgr : groverRatio d = (5 * (d : ℝ) ^ 2 - 8 * (d : ℝ) + 4) / (d : ℝ) ^ 3 := by
    unfold groverRatio
    ring
  refine ⟨d, hd150, ?_, ?_⟩
  · rw [hgr]
    have hdp : (d : ℝ) * p ≤ 152 := (le_div_iff₀ hp).mp hDle
    have h4 : p / 38 ≤ (4 : ℝ) / (d : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 38)]
      rw [show (4 : ℝ) / (d : ℝ) * 38 = 152 / (d : ℝ) by ring]
      rw [le_div_iff₀ hDpos]
      nlinarith [hdp]
    linarith [hbounds.1]
  · rw [hgr]
    have hdp1 : (1 : ℝ) ≤ (d : ℝ) * p := (div_le_iff₀ hp).mp hDge
    have h5 : (5 : ℝ) / (d : ℝ) ≤ 5 * p := by
      rw [div_le_iff₀ hDpos]
      nlinarith [hdp1]
    linarith [hbounds.2]

/-- Combine the hard-family norm-to-ratio identity, its realization as the squared norm of the
Grover-inverse target, and dimension selection with `d ≥ 150` and ratio between `p / 38` and
`5 * p` for every `0 < p < 1`. -/
theorem clause63_endpoint :
    (∀ d : ℕ, hardFamilySolutionNormSq d = (d : ℝ) * groverRatio d) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (x : I),
      hardFamilySolutionNormSq (Fintype.card I)
        = ‖stateVector (groverInverse (I := I) *ᵥ bState x)‖ ^ 2) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ∃ d : ℕ, 150 ≤ d ∧ p / 38 ≤ groverRatio d ∧ groverRatio d ≤ 5 * p) :=
  ⟨hard_family_norm_ratio_identity, fun I _ _ _ x => hard_family_actual_norm x,
    fun p hp hp1 => hard_family_dimension_selection p hp hp1⟩

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem
