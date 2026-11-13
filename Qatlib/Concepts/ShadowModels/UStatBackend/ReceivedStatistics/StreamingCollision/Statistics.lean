/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.StreamingCollision.Signed
import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.SignedCollisionStatistics

/-!
# Streaming collision statistics and medians

This module transfers finite pair U-statistic mean and variance formulas to the signed streaming
collision evaluator. It constructs a counted median over independent blocks and proves its
value, comparison, resource, and failure bounds, giving a streaming implementation of the
nonlinear estimation backend related to [HuangKuengPreskill2020].

## Main statements

* `stream_variance`: exact statistical variance of the streaming output.
* `median_counts`: total event counts across all blocks.
* `median_failure_bound`: concentration of the streaming median.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision

/-- Casting the signed streaming output to the reals gives the pair U-statistic of the real cast
of `rawKernel`. -/
theorem stream_cast {m n : ℕ} (a b : ℚ) (u : Vector ℚ m) (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ) =
      Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (fun l r => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ)) w := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn,
      Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]

/-- For blocks of at least two independent records, the real streaming output has expectation
equal to the mean of the cast raw collision kernel. -/
theorem stream_mean {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (n : ℕ) (hn : 2≤n) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).expect
      (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ)) =
      Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun l r => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ)) := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_mean p
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n hn

/-- For blocks of at least two independent records, the real streaming output has variance
exactly `varianceBudget` for the raw collision kernel. -/
theorem stream_variance {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (n : ℕ) (hn : 2≤n) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).variance
      (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ)) =
      Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_variance p
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n hn
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel_symmetric a b u)

/-- The real cast of `rawKernel` equals the real residual collision kernel with the
corresponding cast coefficients and vector entries. -/
theorem cast_to_residual {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ) =
      Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision (a : ℝ) (b : ℝ)
        (fun i => ((u[i] : ℚ) : ℝ)) l r := by
  have hs (z : Bool) : ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign z : ℚ) : ℝ) = Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign z := by
    cases z <;> simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign,
        Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.recordSign]
  by_cases h : l.1=r.1 <;>
    simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel,
        Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted, Qatlib.Concepts.ShadowModels.UStatBackend.SignedCollisionStatistics.residualCollision, h, hs]

/-- A rational streaming median with accumulated scheduled gate and event counts and a separate
median-selection comparison count. -/
structure MedianResult where
  value : ℚ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  selectionComparisons : ℕ

/-- Run signed streaming estimation on each of `2 * r + 1` blocks, select the rational median,
and aggregate the block costs. -/
def medianRun {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : MedianResult :=
  let saved :=
      Vector.ofFn (fun i => Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn (w i)))
  let selected :=
      Qatlib.Concepts.ShadowModels.SampleBudget.qSelect (saved.toList.map (fun run => run.value)) r
  ⟨selected.1, ∑ i : Fin (2*r+1), saved[i].scheduledGates,
    (fun e => ∑ i : Fin (2*r+1), saved[i].counts e), selected.2⟩

/-- The streaming median equals the value of the counted rational pair median for the raw
collision kernel. -/
theorem median_value {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).value =
      (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n r w).1 := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn, Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun]

/-- Selecting the streaming median uses at most `10000 * (2 * r + 1)` comparisons. -/
theorem median_comparisons {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).selectionComparisons ≤ 10000*(2*r+1) := by
  have hc := (Qatlib.Concepts.ShadowModels.SampleBudget.rational_selection_median_exact_real_sorted_semantics r
    (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn (w i))).value)).2
  simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun,
      Vector.toList_ofFn, List.map_ofFn, Function.comp_def] using! hc

/-- Each streaming-median event count is `2 * r + 1` times the initialization, `n` signed-step
costs, and finalization cost of one block. -/
theorem median_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts e =
      (2*r+1)*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m e+n*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts e)+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts e) := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_counts]

/-- The streaming median uses `(2 * r + 1) * n` record accesses, bank reads, bank writes, and
coefficient reads, and `(2 * r + 1) * m` initial slots. -/
theorem median_record_calls {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .records = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .bankReads = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .bankWrites = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .coefficientReads = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .initialSlots = (2*r+1)*m := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.median_counts,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts]

/-- If the block variance budget is at most `eps ^ 2 / 3` and `n ≥ 2`, the streaming median
deviates from the pair-kernel mean by more than `eps` with probability at most `(8 / 9) ^
r`. -/
theorem median_failure_bound {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (n r : ℕ) (hn : 2≤n) (eps : ℝ) (heps : 0<eps)
    (hbudget : Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n ≤ eps^2/3) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).probEvent
      (fun w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m =>
        eps < |((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).value : ℝ)-
          Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun l r => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ))|) ≤ (8/9 : ℝ)^r := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.median_value]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.counted_failure_bound p (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n r hn
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel_symmetric a b u) eps heps hbudget

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
