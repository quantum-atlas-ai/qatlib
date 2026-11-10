/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.CVaREstimation.CVaRAlgorithmFiniteRestrictedQuan
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.NativeAeReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SqEstimation.HierarchicalSQ
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RiskEstimation.PopulationGap
open scoped Classical BigOperators ENNReal

def riskNativeSample {M : ℕ} (bits r : ℕ) (p : FinDist (Fin M)) : PMF ℚ :=
  (closurePMF ({
    prob := p.probOf
    nonneg := fun ω => Finset.prod_nonneg (fun z _ => p.nonneg (ω z))
    sum_one := p.sum_probOf (2*r+1) } : FinDist (Fin (2*r+1) → Fin M))).map
      (fun ω => (((List.ofFn (fun z => nativeAEDecode M bits (ω z))).mergeSort
        (fun a b => a ≤ b)).getD r 0))

def riskNativeBisect (sampler : ℚ → PMF ℚ) (xs : List ℚ) (q : ℚ)
    (fuel lo hi : ℕ) : PMF (ℕ × ℕ) :=
  Nat.rec (motive := fun _ => ℕ → ℕ → PMF (ℕ × ℕ))
    (fun lo _ => PMF.pure (lo,0))
    (fun _ rec lo hi => if hi ≤ lo then PMF.pure (lo,0) else
      let mid := (lo+hi)/2
      (sampler (xs.getD mid 0)).bind (fun z =>
        (if q ≤ z then rec lo mid else rec (mid+1) hi).map
          (fun out => (out.1,out.2+1)))) fuel lo hi

def riskNativeVaR {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q : ℚ)
    (bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hM : 2 ≤ M) : PMF (ℕ × ℕ) :=
  riskNativeBisect (fun t => riskNativeSample bits r (riskCDFLaw A j loss t M hA hM)) xs q
    (Nat.clog 2 xs.length+1) 0 (xs.length-1)

def riskNativeCVaR {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (loss : I → ℚ) (xs : List ℚ) (q ε : ℚ)
    (rotationBits bits M r : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hloss : ∀ i, 0 ≤ loss i ∧ loss i ≤ 1) (hM : 2 ≤ M) : PMF (ℕ × ℚ × ℕ) :=
  (riskNativeVaR A j loss xs q bits M r hA hM).bind (fun z =>
    (riskNativeSample bits r (riskCDFLaw A j loss (xs.getD z.1 0) M hA hM)).bind (fun phat =>
      (riskNativeSample bits r
        (riskNumeratorLaw A j loss (xs.getD z.1 0) rotationBits M hA hloss hM)).map
          (fun μhat => (z.1,μhat/max ε phat,z.2+2))))

theorem risk_native_median_cast (r : ℕ) (v : Fin (2*r+1) → ℚ) :
    (((List.ofFn v).mergeSort (fun a b => a ≤ b)).getD r 0 : ℝ) =
      sortedBlockMedian r (fun z => (v z : ℝ)) := by
  have hs := List.map_mergeSort (l := List.ofFn v) (f := fun a : ℚ => (a : ℝ))
    (s := fun a b : ℝ => a ≤ b) (r := fun a b : ℚ => a ≤ b)
    (by intro a _ b _; simp)
  have heq (l : List ℝ) : l.mergeSort (fun a b => a ≤ b) = (insertionSortCounted l).1 :=
    ((List.mergeSort_perm l _).trans (insertionSortCounted_perm l).symm).eq_of_pairwise'
      List.sortedLE_mergeSort.pairwise (insertionSortCounted_sorted l).pairwise
  simp only [List.map_ofFn, Function.comp_def] at hs
  unfold sortedBlockMedian
  rw [← heq, ← hs]
  simp only [List.getD, List.getElem?_map]
  cases ((List.ofFn v).mergeSort (fun a b => a ≤ b))[r]? <;> simp

theorem risk_native_readout_charges {I : Type} [Fintype I] [DecidableEq I]
    (B : Matrix I I ℂ) (j : I) (M r calls : ℕ) (hM : 2 ≤ M) :
    calls*(2*r+1)*aeForwardAccesses (aeAccessWord (I := I) M) = calls*(2*r+1)*M ∧
    calls*(2*r+1)*aeBackwardAccesses (aeAccessWord (I := I) M) = calls*(2*r+1)*(M-1) ∧
    calls*(2*r+1)*QueryCount (countedAECircuit M B j) = calls*(2*r+1)*(M-1) ∧
    calls*(2*r+1)*GateCount (countedAECircuit M B j) = calls*(2*r+1)*(5*(M-1)+3) := by
  have hpos : 0 < M := by omega
  have hsep := prepared_ae_separate_access_counts (I := I) M hpos
  have hc := prepared_ae_access_ledger M hpos B j
  rw [hsep.1, hsep.2.1, hc.1, hc.2.1]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Qatlib.Concepts.RiskEstimation.PopulationGap
