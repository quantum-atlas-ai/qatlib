/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ExecutionRemainder

/-!
# Weighted hybrid-program execution receipts

`Family` packages legal hybrid programs with a common unitary oracle and density operator. Its
receipt laws combine rational rejection sampling with the leaf distribution of the selected
program, retaining output values and resource counts.

`Family.stopped` models unbounded selection, while `Family.capped` and `Family.cappedProgram`
retain a timeout outcome for bounded selection. The quantum instruments and classical control
used here have background in [NielsenChuang2010].

## Main statements

* `Family.stopped_output`: The stopped output law is the normalized weighted mixture of program
  outputs.
* `Family.capped_some`: The successful capped output law is the mixture multiplied by the
  selection success probability.
* `Family.stopped_reads`: Expected reads split into rejection-sampling reads and selected leaf
  reads.
* `selector_implementation`: The coin sampler realizes the rejection run and its timeout
  probability tends to zero.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

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

/-- The selected-index marginal of the rational stopping law is the normalized integer weight. -/
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

/-- A finite family of legal hybrid programs sharing a unitary oracle and a density operator. -/
structure Family (K D m : ℕ) where
  program : Fin K → HybridProgram D (Fin m)
  legal : ∀ u, (program u).Legal
  oracle : Operator D
  oracle_unitary : oracle ∈ Matrix.unitaryGroup (Fin D) ℂ
  state : Operator D
  density : IsDensityOperator state

namespace Family

/-- The probability law of execution leaves of the selected family member on the common density
operator. -/
noncomputable def leaves (F : Family K D m) (u : Fin K) :
    PMF (Fin (F.program u).leafCount) :=
  instrumentPMF ((F.program u).instrument F.oracle F.oracle_unitary (F.legal u)) F.density

/-- The output law obtained by mapping a family member's leaf distribution to its leaf values. -/
noncomputable def output (F : Family K D m) (u : Fin K) : PMF (Fin m) :=
  (F.leaves u).map fun i => ((F.program u).leaf F.oracle i).value

/-- Every natural-valued function of a family member's leaf counts has finite expectation. -/
theorem leaf_cost_finite (F : Family K D m) (u : Fin K) (g : HybridCounts → ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.leaves u)
      (fun i => (g ((F.program u).leaf F.oracle i).counts : ℝ≥0∞)) < ⊤ := by
  rw [Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation, tsum_fintype]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ((F.leaves u).apply_ne_top i)) (by simp)

/-- An execution receipt consisting of a family index, a number of selection rounds, and an
execution leaf. -/
abbrev Receipt (F : Family K D m) := Σ u : Fin K, ℕ × Fin (F.program u).leafCount

/-- The receipt law obtained by sampling an unbounded rational stopping outcome and then a leaf
of the selected program. -/
noncomputable def stopped (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) : PMF F.Receipt :=
  (rationalStopLaw w b hW hb).bind fun z =>
    (F.leaves z.1).map fun i => (⟨z.1, z.2, i⟩ : F.Receipt)

/-- The output value recorded by the program leaf in a stopped receipt. -/
noncomputable def value (F : Family K D m) (z : F.Receipt) : Fin m :=
  ((F.program z.1).leaf F.oracle z.2.2).value

/-- The selected leaf's resource counts augmented by `b` random-bit reads per selection round. -/
noncomputable def counts (F : Family K D m) (b : ℕ) (z : F.Receipt) : HybridCounts :=
  (⟨0, 0, 0, b * z.2.1⟩ : HybridCounts).plus
    ((F.program z.1).leaf F.oracle z.2.2).counts

/-- The comparison count `K * (t - 1) + u.val + 1` associated with the recorded index and
selection round. -/
def comparisons (F : Family K D m) (z : F.Receipt) : ℕ :=
  K * (z.2.1 - 1) + z.1.val + 1

/-- The stopped receipt output law is the mixture of family output laws with normalized integer
weights. -/
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

/-- A stopped receipt preserves its leaf's query, gate, and measurement counts, while adding `b`
reads per selection round to the leaf's coin count. -/
theorem counts_same_leaf (F : Family K D m) (b : ℕ) (z : F.Receipt) :
    (F.counts b z).queries = ((F.program z.1).leaf F.oracle z.2.2).queries ∧
    (F.counts b z).gates = ((F.program z.1).leaf F.oracle z.2.2).gates ∧
    (F.counts b z).measurements = ((F.program z.1).leaf F.oracle z.2.2).measurements ∧
    (F.counts b z).reads = b * z.2.1 +
      ((F.program z.1).leaf F.oracle z.2.2).coins.length := by
  simp [counts, HybridCounts.plus, HybridLeaf.counts]

end Family

/-- The weighted selector's execution configuration and counters, together with its random-bit
read count. -/
abbrev SelectorResult (K : ℕ) :=
  (RandomizedExecution.Configuration (ℕ × ℕ) (Fin K × ℕ × ℕ) × ℕ) × ℕ

/-- The selected family index, or the timeout marker, extracted from a selector result. -/
def selected (z : SelectorResult K) : Fin K ⊕ Unit := rejectionOutcome z.1.1

/-- The mass of a mapped probability law at a value equals the probability of its preimage
event. -/
theorem map_apply_event {A B : Type} (p : PMF A) (f : A → B) (x : B) :
    (p.map f) x = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun z => f z = x) := by
  simp only [PMF.map_apply, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- Mapping a probability law through `some` preserves the mass at each corresponding `some`
value. -/
theorem map_some_apply {A : Type} (p : PMF A) (i : A) :
    (p.map some) (some i) = p i := by
  classical
  simp only [PMF.map_apply, Option.some.injEq]
  simpa only [eq_comm] using tsum_ite_eq i p

/-- A probability law mapped through `some` assigns zero mass to `none`. -/
theorem map_some_none {A : Type} (p : PMF A) :
    (p.map some) none = 0 := by
  simp [PMF.map_apply]

/-- The probability of selecting an index within the fuel bound is its normalized weight times
`1 - rationalRejectMass w b ^ fuel`. -/
theorem selector_success (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) (u : Fin K) :
    ((weightedSampler w b fuel).law.map selected) (.inl u) =
      (w u : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
        (1 - rationalRejectMass w b ^ fuel) := by
  rw [map_apply_event]
  exact weightedSampler_return w b fuel hW hb u

/-- The bounded selector's timeout probability is `rationalRejectMass w b ^ fuel` when the
bit-block capacity covers the total weight. -/
theorem selector_timeout (w : Fin K → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    ((weightedSampler w b fuel).law.map selected) (.inr ()) =
      rationalRejectMass w b ^ fuel := by
  rw [map_apply_event]
  exact weightedSampler_timeout w b fuel hb

namespace Family

/-- A capped execution receipt recording either a selected program leaf and selector result, or
a timeout selector result. -/
abbrev CappedReceipt (F : Family K D m) :=
  (Σ u : Fin K, SelectorResult K × Fin (F.program u).leafCount) ⊕ SelectorResult K

/-- The receipt law that samples the selected program's leaf on success and retains the selector
result on timeout. -/
noncomputable def cappedNext (F : Family K D m) (z : SelectorResult K) :
    PMF F.CappedReceipt :=
  match selected z with
  | .inl u => (F.leaves u).map fun i => .inl ⟨u,z,i⟩
  | .inr _ => PMF.pure (.inr z)

/-- The receipt law obtained by running the bounded weighted selector and then its selected
program. -/
noncomputable def capped (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    PMF F.CappedReceipt :=
  PMF.bind (weightedSampler w b fuel).law F.cappedNext

/-- The output of a successful capped receipt, with `none` representing a selector timeout. -/
noncomputable def cappedValue (F : Family K D m) : F.CappedReceipt → Option (Fin m)
  | .inl z => some ((F.program z.1).leaf F.oracle z.2.2).value
  | .inr _ => none

/-- The selector result retained in either a successful or timed-out capped receipt. -/
def cappedSelector (F : Family K D m) : F.CappedReceipt → SelectorResult K
  | .inl z => z.2.1
  | .inr z => z

/-- The selected leaf's cost under `g`, with zero cost assigned to a selector timeout. -/
noncomputable def cappedLeafCost (F : Family K D m) (g : HybridCounts → ℕ) :
    F.CappedReceipt → ℕ
  | .inl z => g ((F.program z.1).leaf F.oracle z.2.2).counts
  | .inr _ => 0

/-- The selected leaf's counts augmented by selector reads, or only selector reads in the
timeout case. -/
noncomputable def cappedCounts (F : Family K D m) : F.CappedReceipt → HybridCounts
  | .inl z => (⟨0,0,0,z.2.1.2⟩ : HybridCounts).plus
      ((F.program z.1).leaf F.oracle z.2.2).counts
  | .inr z => ⟨0,0,0,z.2⟩

/-- The rejection-comparison count extracted from a capped receipt's selector configuration. -/
def cappedComparisons (F : Family K D m) (z : F.CappedReceipt) : ℕ :=
  rejectionComparisons (F.cappedSelector z).1.1

/-- Projecting the capped receipt law onto selector results recovers the weighted sampler's law. -/
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

/-- The expectation of any function of the retained selector equals its expectation under the
weighted sampler's law. -/
theorem capped_selector_expectation (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (g : SelectorResult K → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => g (F.cappedSelector z)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (weightedSampler w b fuel).law g := by
  rw [← Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map _ F.cappedSelector g,
      F.capped_selector_marginal]

/-- The expected capped leaf cost is the normalized mixture of leaf costs multiplied by the
selector's success probability. -/
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

/-- Expected capped reads equal the truncated geometric selector-read cost plus the
success-weighted mixture of leaf reads. -/
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

/-- Expected capped comparisons equal the mean comparison cost of one round times the truncated
geometric rejection sum. -/
theorem capped_comparisons (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2^b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel) (fun z => (F.cappedComparisons z : ℝ≥0∞)) =
      rationalMeanComparisons w b * ∑ t ∈ Finset.range fuel, rationalRejectMass w b ^ t := by
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.capped w b fuel)
    (fun z => (rejectionComparisons (F.cappedSelector z).1.1 : ℝ≥0∞)) = _
  rw [F.capped_selector_expectation w b fuel
    (fun z => (rejectionComparisons z.1.1 : ℝ≥0∞))]
  exact (weightedSampler_expectations w b fuel hW hb).2

/-- The output law for a selector outcome, producing the selected program's output under `some`
or `none` on timeout. -/
noncomputable def outcomeNext (F : Family K D m) : Fin K ⊕ Unit → PMF (Option (Fin m))
  | .inl u => (F.output u).map some
  | .inr _ => PMF.pure none

/-- The capped output law factors through the selector-outcome law followed by
`Family.outcomeNext`. -/
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

/-- The mass of a successful capped output equals the normalized weighted output mixture times
the selection success probability. -/
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

/-- The mass of `none` in the capped output law equals the selector's geometric timeout
probability. -/
theorem capped_none (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ)
    (hb : weightTotal w ≤ 2 ^ b) :
    ((F.capped w b fuel).map F.cappedValue) none = rationalRejectMass w b ^ fuel := by
  classical
  rw [capped_output_bind, PMF.bind_apply, tsum_fintype, Fintype.sum_sum_type]
  simp only [outcomeNext, map_some_none,
    mul_zero, Finset.sum_const_zero, PMF.pure_apply, if_true, mul_one,
    Fintype.sum_unique, zero_add]
  exact selector_timeout w b fuel hb

/-- The hybrid program that runs the bounded weighted selector, executes the selected family
member, and returns `none` on timeout. -/
def cappedProgram (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    HybridProgram D (Option (Fin m)) :=
  .ofCoins (weightedSampler w b fuel) fun z =>
    match rejectionOutcome z.1 with
    | .inl u => (F.program u).bind fun i => .ret (some i)
    | .inr _ => .ret none

/-- The bounded weighted mixture of a legal program family is a legal hybrid program. -/
theorem cappedProgram_legal (F : Family K D m) (w : Fin K → ℕ) (b fuel : ℕ) :
    (F.cappedProgram w b fuel).Legal := by
  apply HybridProgram.ofCoins_legal
  intro z
  cases rejectionOutcome z.1 with
  | inl u => exact HybridProgram.bind_legal _ (F.legal u) _ (fun _ => trivial)
  | inr _ => trivial

/-- Functions of the selected index and stopping round have the same expectation under stopped
receipts and the rational stopping law. -/
theorem stopped_selector_expectation (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b)
    (g : Fin K × ℕ → ℝ≥0∞) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb) (fun z => g (z.1,z.2.1)) =
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (rationalStopLaw w b hW hb) g := by
  simp only [stopped, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_bind, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_map,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_const, Prod.eta]

/-- The expectation of a function of the selected execution leaf is the normalized weighted
mixture of its leaf expectations. -/
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

/-- The expected selected-leaf cost under stopped receipts is the normalized weighted mixture of
the individual program costs. -/
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

/-- Every natural-valued function of the selected leaf's resource counts has finite expectation
under the stopped receipt law. -/
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

/-- Expected stopped reads split into `b / (1 - rationalRejectMass w b)` selector reads and the
weighted mixture of leaf coin counts. -/
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

/-- Expected stopped comparisons equal the mean comparison cost per round divided by the
rejection success probability. -/
theorem stopped_comparisons (F : Family K D m) (w : Fin K → ℕ) (b : ℕ)
    (hW : 0 < weightTotal w) (hb : weightTotal w ≤ 2 ^ b) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb) (fun z => (F.comparisons z : ℝ≥0∞)) =
      rationalMeanComparisons w b / (1 - rationalRejectMass w b) := by
  change Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (F.stopped w b hW hb)
    (fun z => ((K*(z.2.1-1)+z.1.val+1 : ℕ) : ℝ≥0∞)) = _
  rw [F.stopped_selector_expectation w b hW hb
    (fun z => ((K*(z.2-1)+z.1.val+1 : ℕ) : ℝ≥0∞))]
  exact (rational_unbounded_expected_resources_and_limits K w b hW hb).2.2.1

/-- The total random-bit read count of the stopped receipt law has finite expectation. -/
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

/-- The weighted sampler realizes the rational rejection run with `b` reads per round, its
timeout probability tends to zero, and its stopping law has the stated first-stop masses. -/
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
