/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.StreamingCollision.Signed
import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.SignedCollisionStatistics
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
set_option warningAsError false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision

theorem stream_cast {m n : ℕ} (a b : ℚ) (u : Vector ℚ m) (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ) =
      Qatlib.Concepts.ShadowModels.UStatBackend.pairUStatistic (fun l r => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ)) w := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn,
      Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.cast_evaluate]

theorem stream_mean {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (n : ℕ) (hn : 2≤n) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).expect
      (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ)) =
      Qatlib.Concepts.ShadowModels.UStatBackend.pairKernelMean p (fun l r => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r : ℝ)) := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_mean p
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n hn

theorem stream_variance {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (n : ℕ) (hn : 2≤n) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.blockLaw p n).variance
      (fun w => ((Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value : ℝ)) =
      Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.varianceBudget p (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn]
  exact Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.actual_variance p
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n hn
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel_symmetric a b u)

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

structure MedianResult where
  value : ℚ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  selectionComparisons : ℕ

def medianRun {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : MedianResult :=
  let saved :=
      Vector.ofFn (fun i => Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn (w i)))
  let selected :=
      Qatlib.Concepts.ShadowModels.SampleBudget.qSelect (saved.toList.map (fun run => run.value)) r
  ⟨selected.1, ∑ i : Fin (2*r+1), saved[i].scheduledGates,
    (fun e => ∑ i : Fin (2*r+1), saved[i].counts e), selected.2⟩

theorem median_value {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).value =
      (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) n r w).1 := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun, Vector.toList_ofFn, List.map_ofFn, Function.comp_def,
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_ofFn, Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.countedRun]

theorem median_comparisons {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).selectionComparisons ≤ 10000*(2*r+1) := by
  have hc := (Qatlib.Concepts.ShadowModels.SampleBudget.rational_selection_median_exact_real_sorted_semantics r
    (fun i => (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn (w i))).value)).2
  simpa only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun,
      Vector.toList_ofFn, List.map_ofFn, Function.comp_def] using! hc

theorem median_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts e =
      (2*r+1)*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m e+n*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts e)+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts e) := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_counts]

theorem median_record_calls {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (n r : ℕ)
    (w : Fin (2*r+1) → Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .records = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .bankReads = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .bankWrites = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .coefficientReads = (2*r+1)*n ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.medianRun a b u n r w).counts .initialSlots = (2*r+1)*m := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.median_counts,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts]

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
