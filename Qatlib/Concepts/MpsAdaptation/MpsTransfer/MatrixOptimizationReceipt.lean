/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.GibbsMetropolis.RationalBath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AdversaryBounds.AdvDuality.CoinCode
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open Qatlib
open scoped ENNReal Classical

variable {K D m : ℕ}

theorem stop_marginal (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (u : Fin K) :
    ((rationalStopLaw w b hW hb).map Prod.fst) u =
      (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) := by
  classical
  rw [PMF.map_apply, tsum_prod_type', tsum_fintype]
  rw [Finset.sum_eq_single u]
  swap
  · intro x _ hx
    simp only [if_neg (Ne.symm hx), tsum_zero]
  swap
  · simp
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [rationalStopLaw_apply, rationalStopMass, if_true,
    Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel, zero_add]
  exact (rational_unbounded_actual_first_stop_law K w b hW hb).2.2.1 u |>.2.1

structure Family (K D m : ℕ) where
  program : Fin K → HybridProgram D (Fin m)
  legal : ∀ u, (program u).Legal
  oracle : Operator D
  oracle_unitary : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ
  state : Operator D
  density : IsDensityOperator state

namespace Family

noncomputable def leaves (F : Family K D m) (u : Fin K) :
    PMF (Fin (F.program u).leafCount) :=
  instrumentPMF ((F.program u).instrument F.oracle F.oracle_unitary (F.legal u)) F.density

noncomputable def output (F : Family K D m) (u : Fin K) : PMF (Fin m) :=
  (F.leaves u).map fun i => ((F.program u).leaf F.oracle i).value

theorem leaf_cost_finite (F : Family K D m) (u : Fin K) (g : HybridCounts → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
      (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞)) < ⊤ := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ((F.leaves u).apply_ne_top i)) (by simp)

abbrev Receipt (F : Family K D m) := Σ u : Fin K, ℕ × Fin (F.program u).leafCount

noncomputable def stopped (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) : PMF F.Receipt :=
  (rationalStopLaw w b hW hb).bind fun z =>
    (F.leaves z.1).map fun i => (⟨z.1, z.2, i⟩ : F.Receipt)

noncomputable def value (F : Family K D m) (z : F.Receipt) : Fin m :=
  ((F.program z.1).leaf F.oracle z.2.2).value

noncomputable def counts (F : Family K D m) (b : ℕ) (z : F.Receipt) : HybridCounts :=
  (⟨0, 0, 0, b * z.2.1⟩ : HybridCounts).plus
    ((F.program z.1).leaf F.oracle z.2.2).counts

def comparisons (F : Family K D m) (z : F.Receipt) : ℕ :=
  K * (z.2.1 - 1) + z.1.val + 1

theorem stopped_output (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (i : Fin m) :
    ((F.stopped w b hW hb).map F.value) i =
      ∑ u : Fin K, ((w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) * F.output u i := by
  have hm : (F.stopped w b hW hb).map F.value =
      ((rationalStopLaw w b hW hb).map Prod.fst).bind F.output := by
    simp only [stopped, PMF.map_bind, PMF.map_comp, PMF.bind_map,
      output, value, Function.comp_def]
  rw [hm, PMF.bind_apply, tsum_fintype]
  exact Finset.sum_congr rfl fun u _ => by rw [stop_marginal]

theorem counts_same_leaf (F : Family K D m) (b : ℕ) (z : F.Receipt) :
    (F.counts b z).queries = ((F.program z.1).leaf F.oracle z.2.2).queries ∧
    (F.counts b z).gates = ((F.program z.1).leaf F.oracle z.2.2).gates ∧
    (F.counts b z).measurements = ((F.program z.1).leaf F.oracle z.2.2).measurements ∧
    (F.counts b z).reads = b * z.2.1 +
      ((F.program z.1).leaf F.oracle z.2.2).coins.length := by
  simp [counts, HybridCounts.plus, HybridLeaf.counts]

end Family

abbrev SelectorResult (K : ℕ) :=
  (RandomizedExecution.Configuration (ℕ × ℕ) (Fin K × ℕ × ℕ) × ℕ) × ℕ

def selected (z : SelectorResult K) : Fin K ⊕ Unit := rejectionOutcome z.1.1

theorem map_apply_event {A B : Type} (p : PMF A) (f : A → B) (x : B) :
    (p.map f) x = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => f z = x) := by
  simp only [PMF.map_apply, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
    mul_ite, mul_one, mul_zero, eq_comm]

theorem map_some_apply {A : Type} (p : PMF A) (i : A) :
    (p.map some) (some i) = p i := by
  classical
  simp only [PMF.map_apply, Option.some.injEq]
  simpa only [eq_comm] using tsum_ite_eq i p

theorem map_some_none {A : Type} (p : PMF A) :
    (p.map some) none = 0 := by
  simp [PMF.map_apply]

theorem selector_success (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (u : Fin K) :
    ((weightedSampler w b fuel).law.map selected) (.inl u) =
      (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
        (1 - rationalRejectMass w b ^ fuel) := by
  rw [map_apply_event]
  exact weightedSampler_return w b fuel hW hb u

theorem selector_timeout (w : Fin K → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    ((weightedSampler w b fuel).law.map selected) (.inr ()) =
      rationalRejectMass w b ^ fuel := by
  rw [map_apply_event]
  exact weightedSampler_timeout w b fuel hb

namespace Family

abbrev CappedReceipt (F : Family K D m) :=
  (Σ u : Fin K, SelectorResult K × Fin (F.program u).leafCount) ⊕ SelectorResult K

noncomputable def cappedNext (F : Family K D m) (z : SelectorResult K) :
    PMF F.CappedReceipt :=
  match selected z with
  | .inl u => (F.leaves u).map fun i => .inl ⟨u,z,i⟩
  | .inr _ => PMF.pure (.inr z)

noncomputable def capped (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    PMF F.CappedReceipt :=
  PMF.bind (weightedSampler w b fuel).law F.cappedNext

noncomputable def cappedValue (F : Family K D m) : F.CappedReceipt → Option (Fin m)
  | .inl z => some ((F.program z.1).leaf F.oracle z.2.2).value
  | .inr _ => none

def cappedSelector (F : Family K D m) : F.CappedReceipt → SelectorResult K
  | .inl z => z.2.1
  | .inr z => z

noncomputable def cappedLeafCost (F : Family K D m) (g : HybridCounts → ℕ) :
    F.CappedReceipt → ℕ
  | .inl z => g ((F.program z.1).leaf F.oracle z.2.2).counts
  | .inr _ => 0

noncomputable def cappedCounts (F : Family K D m) : F.CappedReceipt → HybridCounts
  | .inl z => (⟨0,0,0,z.2.1.2⟩ : HybridCounts).plus
      ((F.program z.1).leaf F.oracle z.2.2).counts
  | .inr z => ⟨0,0,0,z.2⟩

def cappedComparisons (F : Family K D m) (z : F.CappedReceipt) : ℕ :=
  rejectionComparisons (F.cappedSelector z).1.1

theorem capped_selector_marginal (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    (F.capped w b fuel).map F.cappedSelector = (weightedSampler w b fuel).law := by
  rw [capped, PMF.map_bind]
  have h (z : SelectorResult K) : (F.cappedNext z).map F.cappedSelector = PMF.pure z := by
    cases hs : selected z with
    | inl u =>
        simp only [cappedNext, hs, PMF.map_comp, cappedSelector, Function.comp_def]
        exact PMF.map_const _ _
    | inr u => simp [cappedNext, hs, PMF.pure_map, cappedSelector]
  simp_rw [h]
  exact PMF.bind_pure _

theorem capped_selector_expectation (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (g : SelectorResult K → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => g (F.cappedSelector z)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law g := by
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map _ F.cappedSelector g,
      F.capped_selector_marginal]

theorem capped_leaf_expectation (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) (g : HybridCounts → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => (F.cappedLeafCost g z : ℝ≥0∞)) =
      (1-rationalRejectMass w b ^ fuel) *
        ∑ u, (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
            (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞)) := by
  let G : Fin K ⊕ Unit → ℝ≥0∞ := Sum.elim
    (fun u => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
      (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞))) (fun _ => 0)
  rw [capped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  have h (z : SelectorResult K) : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.cappedNext z)
      (fun r => (F.cappedLeafCost g r : ℝ≥0∞)) = G (selected z) := by
    cases hs : selected z with
    | inl u => simp [cappedNext, hs, cappedLeafCost, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map, G]
    | inr u => simp [cappedNext, hs, cappedLeafCost, G]
  simp_rw [h]
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map _ selected G, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
    tsum_fintype, Fintype.sum_sum_type]
  simp only [G, Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [selector_success w b fuel hW hb]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

theorem capped_reads (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => ((F.cappedCounts z).reads : ℝ≥0∞)) =
      (b : ℝ≥0∞) * ∑ t ∈ Finset.range fuel, rationalRejectMass w b ^ t +
      (1-rationalRejectMass w b ^ fuel) *
        ∑ u, (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
            (fun i => (((F.program u).leaf F.oracle i).counts.reads : ℝ≥0∞)) := by
  have h (z : F.CappedReceipt) : ((F.cappedCounts z).reads : ℝ≥0∞) =
      ((F.cappedSelector z).2 : ℝ≥0∞) + (F.cappedLeafCost HybridCounts.reads z : ℝ≥0∞) := by
    cases z <;> simp [cappedCounts, cappedSelector, cappedLeafCost, HybridCounts.plus, Nat.cast_add]
  simp_rw [h]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    F.capped_selector_expectation w b fuel (fun z => (z.2 : ℝ≥0∞)),
    F.capped_leaf_expectation w b fuel hW hb HybridCounts.reads]
  congr 1
  exact (weightedSampler_expectations w b fuel hW hb).1

theorem capped_comparisons (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => (F.cappedComparisons z : ℝ≥0∞)) =
      rationalMeanComparisons w b * ∑ t ∈ Finset.range fuel, rationalRejectMass w b ^ t := by
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel)
    (fun z => (rejectionComparisons (F.cappedSelector z).1.1 : ℝ≥0∞)) = _
  rw [F.capped_selector_expectation w b fuel
    (fun z => (rejectionComparisons z.1.1 : ℝ≥0∞))]
  exact (weightedSampler_expectations w b fuel hW hb).2

noncomputable def outcomeNext (F : Family K D m) : Fin K ⊕ Unit → PMF (Option (Fin m))
  | .inl u => (F.output u).map some
  | .inr _ => PMF.pure none

theorem capped_output_bind (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    (F.capped w b fuel).map F.cappedValue =
      ((weightedSampler w b fuel).law.map selected).bind F.outcomeNext := by
  rw [capped, PMF.map_bind, PMF.bind_map]
  congr 1
  funext z
  cases h : selected z with
  | inl u => simp [cappedNext, h, cappedValue, outcomeNext, output,
      PMF.map_comp, Function.comp_def]
  | inr u => simp [cappedNext, h, cappedValue, outcomeNext, PMF.pure_map]

theorem capped_some (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (i : Fin m) :
    ((F.capped w b fuel).map F.cappedValue) (some i) =
      (1 - rationalRejectMass w b ^ fuel) *
        ∑ u : Fin K, (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) * F.output u i := by
  classical
  rw [capped_output_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [outcomeNext, map_some_apply, PMF.pure_apply,
    reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [selector_success w b fuel hW hb]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

theorem capped_none (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    ((F.capped w b fuel).map F.cappedValue) none = rationalRejectMass w b ^ fuel := by
  classical
  rw [capped_output_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [outcomeNext, map_some_none,
    mul_zero, Finset.sum_const_zero, PMF.pure_apply, if_true, mul_one,
    Fintype.sum_unique, zero_add]
  exact selector_timeout w b fuel hb

def cappedProgram (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    HybridProgram D (Option (Fin m)) :=
  .ofCoins (weightedSampler w b fuel) fun z =>
    match rejectionOutcome z.1 with
    | .inl u => (F.program u).bind fun i => .ret (some i)
    | .inr _ => .ret none

theorem cappedProgram_legal (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    (F.cappedProgram w b fuel).Legal := by
  apply HybridProgram.ofCoins_legal
  intro z
  cases rejectionOutcome z.1 with
  | inl u => exact HybridProgram.bind_legal _ (F.legal u) _ (fun _ => trivial)
  | inr _ => trivial

theorem stopped_selector_expectation (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b)
    (g : Fin K × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb) (fun z => g (z.1,z.2.1)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w b hW hb) g := by
  simp only [stopped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const, Prod.eta]

theorem stopped_leaf_expectation (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b)
    (g : (u : Fin K) → Fin (F.program u).leafCount → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb) (fun z => g z.1 z.2.2) =
      ∑ u : Fin K, ((w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u) (g u) := by
  rw [stopped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind]
  simp only [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map]
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map (rationalStopLaw w b hW hb) Prod.fst
      (fun u => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u) (g u)),
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  exact Finset.sum_congr rfl fun u _ => by rw [stop_marginal]

theorem stopped_cost (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b)
    (g : HybridCounts → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
      (fun z => (g ((F.program z.1).leaf F.oracle z.2.2).counts : ℝ≥0∞)) =
      ∑ u : Fin K, ((w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
          (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞)) :=
  F.stopped_leaf_expectation w b hW hb
    (fun u i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞))

theorem stopped_cost_finite (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (g : HybridCounts → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
      (fun z => (g ((F.program z.1).leaf F.oracle z.2.2).counts : ℝ≥0∞)) < ⊤ := by
  rw [F.stopped_cost w b hW hb g]
  apply ENNReal.sum_lt_top.mpr
  intro u _
  apply ENNReal.mul_lt_top
  · exact ENNReal.div_lt_top (by simp) (by positivity)
  · exact F.leaf_cost_finite u g

theorem stopped_reads (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
      (fun z => ((F.counts b z).reads : ℝ≥0∞)) =
      (b : ℝ≥0∞) / (1 - rationalRejectMass w b) +
      ∑ u : Fin K, ((w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞)) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
          (fun i => (((F.program u).leaf F.oracle i).coins.length : ℝ≥0∞)) := by
  simp only [counts, HybridCounts.plus, HybridLeaf.counts, Nat.cast_add]
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add,
    F.stopped_selector_expectation w b hW hb (fun z => (b*z.2 : ℕ)),
    F.stopped_leaf_expectation w b hW hb
      (fun u i => (((F.program u).leaf F.oracle i).coins.length : ℝ≥0∞))]
  congr 1
  exact (rational_unbounded_expected_resources_and_limits K w b hW hb).2.1

theorem stopped_comparisons (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb) (fun z => (F.comparisons z : ℝ≥0∞)) =
      rationalMeanComparisons w b / (1 - rationalRejectMass w b) := by
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
    (fun z => ((K*(z.2.1-1)+z.1.val+1 : ℕ) : ℝ≥0∞)) = _
  rw [F.stopped_selector_expectation w b hW hb
    (fun z => ((K*(z.2-1)+z.1.val+1 : ℕ) : ℝ≥0∞))]
  exact (rational_unbounded_expected_resources_and_limits K w b hW hb).2.2.1

theorem stopped_reads_finite (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
      (fun z => ((F.counts b z).reads : ℝ≥0∞)) < ⊤ := by
  rw [F.stopped_reads w b hW hb]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact (rational_unbounded_expected_resources_and_limits K w b hW hb).2.2.2.1
  · have hc := F.stopped_cost w b hW hb HybridCounts.reads
    simp only [HybridLeaf.counts] at hc
    rw [← hc]
    exact F.stopped_cost_finite w b hW hb HybridCounts.reads

theorem selector_implementation (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    (weightedSampler w b fuel).law =
      (rationalRejectionRun w b fuel).map (fun z => (z,b*z.2)) ∧
    Filter.Tendsto (fun n => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (weightedSampler w b n).law
      (fun z => rejectionOutcome z.1.1 = .inr ())) Filter.atTop (nhds (0 : ℝ≥0∞)) ∧
    ∀ u, rationalStopLaw w b hW hb (u,0) = 0 ∧
      ∀ t, rationalStopLaw w b hW hb (u,t+1) = rationalFirstStop w b t u :=
  ⟨weightedSampler_law w b fuel, weightedSampler_timeout_tendsto_zero w b hW hb,
    (rational_unbounded_actual_first_stop_law K w b hW hb).2.2.2.2⟩

end Family

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
