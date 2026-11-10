/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.ConeSeparation.SharedMatrixOptimizationDefs
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationS1ContractEvidence
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow
import Qatlib.Concepts.SdpDuality.StrongDuality.PsdConeGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.AmpTransform.LegendreWindow
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9
open Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.SdpDuality.StrongDuality

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.MatrixWeights.ApproxGibbs
open Qatlib.Concepts.RationalScan.Step2Scan
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section

open Classical

theorem gtEqualityBoundary_iff {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ) :
    gtHermitianGap H K = 0 ↔ gtEqualityBoundary H K := by
  unfold gtHermitianGap gtEqualityBoundary
  constructor
  · intro h
    linarith
  · intro h
    linarith

theorem gt_logInput_boundary {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    gtLogInputBoundary A B :=
  log_input_gt_le A B hA hB

theorem gt_hermitian_equality_boundary {n : ℕ} (H K : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) (hK : K.IsHermitian) :
    0 ≤ gtHermitianGap H K ∧ (gtEqualityBoundary H K ↔ Commute H K) :=
  ⟨gt_gap_nonneg H K hH hK,
    (gtEqualityBoundary_iff H K).symm.trans (gt_gap_zero_iff_commute H K hH hK)⟩

theorem gt_psd_infimum_le_product {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) :
    psdRegularizedInfimum A B ≤ (Matrix.trace (A.mat * B.mat)).re := by
  have hbdd : BddBelow (Set.range fun ε : Set.Ioi (0:ℝ) => psdRegularizedGT A B ε) := by
    refine ⟨0, ?_⟩
    rintro x ⟨ε, rfl⟩
    exact regularized_gt_nonneg A B ε
  have hle : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0),
      psdRegularizedInfimum A B ≤ psdRegularizedProductTrace A.mat B.mat ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have h1 : psdRegularizedInfimum A B ≤ psdRegularizedGT A B ε := by
      show (⨅ t : Set.Ioi (0:ℝ), psdRegularizedGT A B t) ≤ psdRegularizedGT A B ε
      exact ciInf_le_of_le hbdd ⟨ε, Set.mem_Ioi.mpr (Set.mem_Ioi.mp hε)⟩ le_rfl
    exact h1.trans (regularized_gt_le A B hA hB (Set.mem_Ioi.mp hε))
  exact ge_of_tendsto (regularized_product_trace_tendsto A B) hle

theorem gt_psd_infimum_nonneg {n : ℕ} (A B : HermitianMat (Fin n) ℂ) :
    0 ≤ psdRegularizedInfimum A B := by
  have hzero : psdGTInfimum A B = psdRegularizedInfimum A B ⊓ sInf (∅ : Set ℝ) := by
    rw [psdGTInfimum_eq_trueInf_inf_sInf_empty]
    rfl
  have hnonneg : 0 ≤ psdGTInfimum A B := psd_inf_nonneg A B
  have hempty : sInf (∅ : Set ℝ) = 0 := Real.sInf_empty
  rw [hzero, hempty] at hnonneg
  exact (le_inf_iff.mp hnonneg).1

theorem gt_psd_regularization_limit {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) :
    Filter.Tendsto (fun ε : ℝ => psdRegularizedGT A B ε)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (psdRegularizedInfimum A B)) := by
  show Filter.Tendsto (fun ε : ℝ => psdRegularizedGT A B ε)
    (nhdsWithin (0:ℝ) (Set.Ioi 0))
    (nhds (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε))
  exact psd_regularized_gt_tendsto_trueInf A B hA hB

theorem gt_psd_commuting_infimum {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosSemidef) (hB : B.mat.PosSemidef) (hcomm : Commute A.mat B.mat) :
    psdRegularizedInfimum A B = (Matrix.trace (A.mat * B.mat)).re := by
  show (⨅ ε : Set.Ioi (0:ℝ), psdRegularizedGT A B ε) = (Matrix.trace (A.mat * B.mat)).re
  exact psd_inf_commuting_trueInf A B hA hB hcomm

theorem gt_logInput_commuting {n : ℕ} (A B : HermitianMat (Fin n) ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) (hcomm : Commute A.mat B.mat) :
    gtLogInputBoundary A B ∧ gtEqualityBoundary (spectralLog A) (spectralLog B) := by
  have hlog : Commute (spectralLog A) (spectralLog B) := by
    show Commute (HermitianMat.log A).mat (HermitianMat.log B).mat
    exact Commute.log_right (Commute.log_left hcomm)
  refine ⟨log_input_gt_le A B hA hB, ?_⟩
  have hgap : gtHermitianGap (spectralLog A) (spectralLog B) = 0 :=
    (gt_gap_zero_iff_commute (spectralLog A) (spectralLog B)
      (HermitianMat.log A).H (HermitianMat.log B).H).2 hlog
  exact (gtEqualityBoundary_iff _ _).1 hgap

theorem gt_zero_dimensional (H K : Matrix (Fin 0) (Fin 0) ℂ)
    (_hH : H.IsHermitian) (_hK : K.IsHermitian) :
    gtEqualityBoundary H K ∧ Commute H K := by
  have hzero (M : Matrix (Fin 0) (Fin 0) ℂ) : M = 0 := by
    apply Matrix.ext
    intro i j
    exact (Nat.not_lt_zero i.val i.isLt).elim
  have htrace (M : Matrix (Fin 0) (Fin 0) ℂ) : Matrix.trace M = 0 := by
    rw [hzero M, Matrix.trace_zero]
  have hexp : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, NormedSpace.exp M = 0 := by
    intro M
    apply Matrix.ext
    intro i j
    exact (Nat.not_lt_zero i.val i.isLt).elim
  refine ⟨?_, ?_⟩
  · unfold gtEqualityBoundary
    have h1 : NormedSpace.exp H = 0 := hexp H
    have h2 : NormedSpace.exp K = 0 := hexp K
    have h3 : NormedSpace.exp (H + K) = 0 := hexp (H + K)
    rw [h1, h2, h3]
    simp
  · apply Matrix.ext
    intro i j
    exact (Nat.not_lt_zero i.val i.isLt).elim

theorem clause21_endpoint :

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosDef → B.mat.PosDef →
      gtLogInputBoundary A B) ∧

    (∀ (n : ℕ) (H K : Matrix (Fin n) (Fin n) ℂ),
      H.IsHermitian → K.IsHermitian →
      0 ≤ gtHermitianGap H K ∧ (gtEqualityBoundary H K ↔ Commute H K)) ∧

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosSemidef → B.mat.PosSemidef →
      psdRegularizedInfimum A B ≤ (Matrix.trace (A.mat * B.mat)).re) ∧

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      0 ≤ psdRegularizedInfimum A B) ∧

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosSemidef → B.mat.PosSemidef →
      Filter.Tendsto (fun ε : ℝ => psdRegularizedGT A B ε)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (psdRegularizedInfimum A B))) ∧

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosSemidef → B.mat.PosSemidef → Commute A.mat B.mat →
      psdRegularizedInfimum A B = (Matrix.trace (A.mat * B.mat)).re) ∧

    (∀ (n : ℕ) (A B : HermitianMat (Fin n) ℂ),
      A.mat.PosDef → B.mat.PosDef → Commute A.mat B.mat →
      gtLogInputBoundary A B ∧ gtEqualityBoundary (spectralLog A) (spectralLog B)) ∧

    (∀ (H K : Matrix (Fin 0) (Fin 0) ℂ),
      H.IsHermitian → K.IsHermitian →
      gtEqualityBoundary H K ∧ Commute H K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n A B hA hB
    exact gt_logInput_boundary A B hA hB
  · intro n H K hH hK
    exact gt_hermitian_equality_boundary H K hH hK
  · intro n A B hA hB
    exact gt_psd_infimum_le_product A B hA hB
  · intro n A B
    exact gt_psd_infimum_nonneg A B
  · intro n A B hA hB
    exact gt_psd_regularization_limit A B hA hB
  · intro n A B hA hB hcomm
    exact gt_psd_commuting_infimum A B hA hB hcomm
  · intro n A B hA hB hcomm
    exact gt_logInput_commuting A B hA hB hcomm
  · intro H K hH hK
    exact gt_zero_dimensional H K hH hK

theorem eventMass_mono {O D T : ℕ} (R : MmwRun O D T)
    {E F : Finset (MmwTranscript T O)} (hEF : E ⊆ F) :
    R.eventMass E ≤ R.eventMass F := by
  unfold MmwRun.eventMass
  refine Finset.sum_le_sum_of_subset_of_nonneg hEF (fun ω _ _ => R.support.prob_nonneg ω)

theorem eventMass_union_disjoint {O D T : ℕ} (R : MmwRun O D T)
    {E F : Finset (MmwTranscript T O)} (hEF : Disjoint E F) :
    R.eventMass (E ∪ F) = R.eventMass E + R.eventMass F := by
  unfold MmwRun.eventMass
  rw [Finset.sum_union hEF]

theorem transcript_expect_coord {T O : ℕ} (p : Fin T → Fin O → ℝ) (t : Fin T)
    (f : Fin O → ℝ) (hnorm : ∀ s, s ≠ t → (∑ o, p s o) = 1) :
    (∑ ω : Fin T → Fin O, (∏ s, p s (ω s)) * f (ω t)) = ∑ o, p t o * f o := by
  set g : Fin T → Fin O → ℝ := fun s o => if s = t then p s o * f o else p s o with hg
  have htmem : t ∈ (Finset.univ : Finset (Fin T)) := Finset.mem_univ t
  have hne (s : Fin T) (hs : s ∈ (Finset.univ : Finset (Fin T)).erase t) : s ≠ t :=
    (Finset.mem_erase.mp hs).1
  have hsplit (ω : Fin T → Fin O) :
      (∏ s, g s (ω s)) = (∏ s, p s (ω s)) * f (ω t) := by
    have he : (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, g s (ω s))
        = ∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, p s (ω s) := by
      refine Finset.prod_congr rfl (fun s hs => ?_)
      simp [hg, hne s hs]
    have hh : (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, g s (ω s)) * g t (ω t)
        = ∏ s, g s (ω s) := by
      have h := Finset.prod_erase_mul Finset.univ (fun s => g s (ω s)) htmem
      exact h
    have hp : (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, p s (ω s)) * p t (ω t)
        = ∏ s, p s (ω s) := by
      have h := Finset.prod_erase_mul Finset.univ (fun s => p s (ω s)) htmem
      exact h
    calc
      (∏ s, g s (ω s))
          = (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, g s (ω s)) * g t (ω t) := by
              rw [hh]
      _ = ((∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, p s (ω s)) * p t (ω t))
            * f (ω t) := by
              rw [he]
              simp [hg]
              ring
      _ = (∏ s, p s (ω s)) * f (ω t) := by
              rw [hp]
  have hprod : (∏ s, (∑ o, g s o)) = (∑ o, p t o * f o) := by
    have hh : (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, g s o))
        * (∑ o, g t o) = ∏ s, (∑ o, g s o) := by
      have h := Finset.prod_erase_mul Finset.univ (fun s => ∑ o, g s o) htmem
      exact h
    have he : (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, g s o))
        = ∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, p s o) := by
      refine Finset.prod_congr rfl (fun s hs => ?_)
      simp [hg, hne s hs]
    have hone : ∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, p s o) = 1 := by
      refine Finset.prod_eq_one (fun s hs => ?_)
      exact hnorm s (hne s hs)
    calc
      (∏ s, (∑ o, g s o))
          = (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, g s o))
            * (∑ o, g t o) := by
              rw [hh]
      _ = (∏ s ∈ (Finset.univ : Finset (Fin T)).erase t, (∑ o, p s o))
            * (∑ o, p t o * f o) := by
              rw [he]
              simp [hg]
      _ = (∑ o, p t o * f o) := by rw [hone]; ring
  calc
    (∑ ω : Fin T → Fin O, (∏ s, p s (ω s)) * f (ω t))
        = ∑ ω : Fin T → Fin O, ∏ s, g s (ω s) := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          rw [hsplit]
    _ = ∏ s, (∑ o, g s o) := by
          have h := Fintype.prod_sum (κ := fun _ : Fin T => Fin O) g
          exact h.symm
    _ = ∑ o, p t o * f o := hprod

theorem mmwRound_record_mean {O D : ℕ} (r : MmwRound O D) :
    (r.law).expect r.f = r.actualPayoff := by
  unfold MmwRound.actualPayoff MmwRound.observable
  exact povm_payoff_mean r.Λ r.ρ r.hρ r.f

theorem mmwRound_record_psd_unit {O D : ℕ} (r : MmwRound O D) :
    r.observable.PosSemidef ∧ ‖r.observable‖ ≤ 1 := by
  unfold MmwRound.observable
  exact payoffObservable_psd_unit r.Λ r.f r.hf

theorem mmwRun_record_mean {O D T : ℕ} (R : MmwRun O D T) (t : Fin T) :
    (∑ ω : MmwTranscript T O, R.transcriptProb ω * (R.rounds t).record (ω t))
      = (R.rounds t).actualPayoff := by
  have h := transcript_expect_coord
    (p := fun s o => (R.rounds s).law.prob o) (t := t) (f := (R.rounds t).f)
    (fun s hs => (R.rounds s).law.sum_one)
  unfold MmwRun.transcriptProb MmwRound.record
  rw [h]
  exact mmwRound_record_mean (R.rounds t)

theorem mmwRun_expected_recorded_payoff {O D T : ℕ} (R : MmwRun O D T) :
    (∑ ω : MmwTranscript T O, R.transcriptProb ω * R.recordedPayoff ω)
      = ∑ t : Fin T, (R.rounds t).actualPayoff := by
  unfold MmwRun.recordedPayoff
  have hdistrib : (∑ ω : MmwTranscript T O,
        R.transcriptProb ω * ∑ t : Fin T, (R.rounds t).record (ω t))
      = ∑ ω : MmwTranscript T O,
        ∑ t : Fin T, R.transcriptProb ω * (R.rounds t).record (ω t) := by
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [Finset.mul_sum]
  rw [hdistrib, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => mmwRun_record_mean R t

theorem mmwRun_ledger_discipline {O D T : ℕ} (R : MmwRun O D T) (ζ : Fin T → ℝ)
    (stopped timedOut : Finset (MmwTranscript T O))
    (hζ : ∀ t, 0 ≤ ζ t)
    (hdisj : Disjoint stopped timedOut)
    (hsub : stopped ∪ timedOut ⊆ R.failureSet ζ) :
    (R.ledger ζ stopped timedOut).discipline := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [MmwRun.ledger]
    exact Finset.sum_nonneg fun t _ => hζ t
  · simp only [MmwRun.ledger]
    exact Finset.sum_nonneg fun ω _ => R.support.prob_nonneg ω
  · simp only [MmwRun.ledger]
    exact Finset.sum_nonneg fun ω _ => R.support.prob_nonneg ω
  · simp only [MmwRun.ledger]
    exact Finset.sum_nonneg fun ω _ => R.support.prob_nonneg ω
  · simp only [MmwRun.ledger]
    have h1 : R.eventMass stopped + R.eventMass timedOut
        = R.eventMass (stopped ∪ timedOut) := (eventMass_union_disjoint R hdisj).symm
    have h2 : R.eventMass (stopped ∪ timedOut)
        ≤ R.eventMass (R.failureSet ζ) := eventMass_mono R hsub
    linarith

theorem clause23_clause22_transport
    (D T : ℕ) (M : ℕ → Operator D) (η : ℝ) (σ : Operator D)
    (approx : ℕ → Operator D) (_z ξ ζ : ℕ → ℝ) (O : ℕ)
    (R : MmwRun O D T)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1)
    (hM : ∀ s < T, (M s).IsHermitian ∧ ‖M s‖ ≤ 1)
    (hσ : IsDensityOperator σ)
    (happ : ∀ s < T, IsDensityOperator (approx s))
    (hxi : ∀ s < T, 0 ≤ ξ s ∧ 0 ≤ ζ s)
    (hstate : ∀ s < T,
      Qatlib.Concepts.MixedFidelity.FidelityMetric.traceDistance (approx s) (Qatlib.Concepts.MatrixWeights.WeightsCore.mmwState D M η s) ≤ ξ s)
    (hrecord : ∀ s < T, ∀ ω : MmwTranscript T O,
      |R.recordAt s ω - (Matrix.trace (M s * approx s)).re| ≤ ζ s) :
    (∑ s ∈ Finset.range T,
        ∑ ω : MmwTranscript T O, R.support.prob ω * R.recordAt s ω)
      - ∑ s ∈ Finset.range T, (Matrix.trace (M s * σ)).re
      ≤ η * T + Real.log D / η + ∑ s ∈ Finset.range T, (2 * ξ s + ζ s) := by
  have hz : ∀ t < T,
      |(Matrix.trace (M t * approx t)).re - (Matrix.trace (M t * approx t)).re| ≤ ζ t := by
    intro t ht
    have hz0 : (Matrix.trace (M t * approx t)).re - (Matrix.trace (M t * approx t)).re = 0 := by
      ring
    rw [hz0, abs_zero]
    exact (hxi t ht).2
  have hg22 := clause22 D T M η σ approx (fun t => (Matrix.trace (M t * approx t)).re) ξ ζ
    hD hη hη1 hM hσ happ hxi hstate hz
  have hthird := hg22.2.2
  have hhyp : ∀ s < T, ∀ ω : MmwTranscript T O,
      |R.recordAt s ω - (Matrix.trace (M s * approx s)).re| ≤ ζ s := hrecord
  have hconc := hthird (MmwTranscript T O)
    (inferInstance : Fintype (MmwTranscript T O)) (R.support) R.recordAt hhyp
  exact hconc

theorem clause23_endpoint :
    (∀ (O D : ℕ) (r : MmwRound O D),
      (r.law).expect r.f = r.actualPayoff) ∧
    (∀ (O D : ℕ) (r : MmwRound O D),
      r.observable.PosSemidef ∧ ‖r.observable‖ ≤ 1) ∧
    (∀ (O D T : ℕ) (R : MmwRun O D T),
      (∑ ω : MmwTranscript T O, R.transcriptProb ω * R.recordedPayoff ω)
        = ∑ t : Fin T, (R.rounds t).actualPayoff) ∧
    (∀ (O D T : ℕ) (R : MmwRun O D T) (ζ : Fin T → ℝ)
        (stopped timedOut : Finset (MmwTranscript T O)),
      (∀ t, 0 ≤ ζ t) → Disjoint stopped timedOut →
      stopped ∪ timedOut ⊆ R.failureSet ζ →
      (R.ledger ζ stopped timedOut).discipline) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O D r
    exact mmwRound_record_mean r
  · intro O D r
    exact mmwRound_record_psd_unit r
  · intro O D T R
    exact mmwRun_expected_recorded_payoff R
  · intro O D T R ζ stopped timedOut hζ hdisj hsub
    exact mmwRun_ledger_discipline R ζ stopped timedOut hζ hdisj hsub

theorem step2_budget_identities (α R κ ν ε : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (hκν' : κ + ν ≤ ε) :
    sdpSampledWidthBudget α R κ ν = sourceWidthBudget α R (κ + ν) ∧
    sdpSampledWidthBudget α R κ ν ≤ sourceWidthBudget α R ε ∧
    sdpSampledSeparationSlack α κ ν = 2 * α * (κ + ν) ∧
    sdpSampledSeparationSlack α κ ν ≤ 2 * α * ε := by
  have h2 : 2 * α * R * (κ + ν) ≤ 2 * α * R * ε := by
    have h := mul_le_mul_of_nonneg_right hκν'
      (mul_nonneg (mul_nonneg hα hR) (by norm_num : (0:ℝ) ≤ 2))
    nlinarith [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · unfold sdpSampledWidthBudget sourceWidthBudget
    nlinarith [h2]
  · rfl
  · unfold sdpSampledSeparationSlack
    exact mul_le_mul_of_nonneg_left hκν' (mul_nonneg (by norm_num) hα)

theorem step2_threshold_identities {D : ℕ} (Cv ρ : Operator D) (α R ε : ℝ) :
    eq75Threshold Cv ρ α ε = (Matrix.trace (Cv * ρ)).re - 3 * α * ε ∧
    Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε = α * (1 - 3 * R * ε) := by
  refine ⟨rfl, rfl⟩

theorem step2_grid_identities {m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q)
    (κ : ℝ) (k : Fin γ) (N : Fin Nmax) :
    Step2Search.gridMass κ N = κ * ((N : ℕ) + 1) ∧
    (∀ i, S.roundVector κ k N i = Step2Search.gridMass κ N * S.law k i) := by
  refine ⟨rfl, fun i => rfl⟩

theorem clause16_corrected_direction :
    ∀ {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (ρ : Operator D) (α R ε : ℝ),
    Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator A Cv b ρ α R ε ↔
      step2CheapSeparator A Cv b ρ α R ε := by
  intro D m A Cv b ρ α R ε
  constructor
  · intro h z hz hcheap
    exact lt_of_not_ge (fun hge => (h z hz hge) hcheap)
  · intro h z hz hsep hcheap
    exact absurd (h z hz hcheap) (not_lt_of_ge hsep)

theorem clause16_law_mean_bound :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
    step2GoodEvent S b A Cv ρ α κ R ν →
    (∑ i : Fin m, S.law k i * (∑ l : Fin L, S.measA k N i l) / L)
      ≤ (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re) + (κ + ν) := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν k N hgood
  have hC := (hgood.1 k N).2.2.1
  have hlaw0 : ∀ i, 0 ≤ S.law k i := fun i => (hgood.2 k).1 i
  have hlaw1 : (∑ i : Fin m, S.law k i) = 1 := (hgood.2 k).2
  have hmeas : ∀ i, (∑ l : Fin L, S.measA k N i l) / L
      ≤ (Matrix.trace (A i * ρ)).re + (κ + ν) := by
    intro i
    have h := (abs_le.mp (hC i)).2
    linarith
  have hstep : (∑ i : Fin m, S.law k i * (∑ l : Fin L, S.measA k N i l) / L)
      ≤ ∑ i : Fin m, S.law k i * ((Matrix.trace (A i * ρ)).re + (κ + ν)) := by
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hmeas i) (hlaw0 i)
    convert! h using 1; ring
  calc (∑ i : Fin m, S.law k i * (∑ l : Fin L, S.measA k N i l) / L)
      ≤ ∑ i : Fin m, S.law k i * ((Matrix.trace (A i * ρ)).re + (κ + ν)) := hstep
    _ = (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re) + (κ + ν) := by
        calc ∑ i : Fin m, S.law k i * ((Matrix.trace (A i * ρ)).re + (κ + ν))
            = ∑ i : Fin m, (S.law k i * (Matrix.trace (A i * ρ)).re
                + S.law k i * (κ + ν)) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  ring
          _ = (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re)
              + ∑ i : Fin m, S.law k i * (κ + ν) := Finset.sum_add_distrib
          _ = (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re)
              + (∑ i : Fin m, S.law k i) * (κ + ν) := by
                rw [← Finset.sum_mul]
          _ = (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re) + (κ + ν) := by
                rw [hlaw1]
                ring

theorem clause16_width_side :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
    step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
    Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
    0 ≤ R → 0 ≤ κ + ν →
    (∑ i, b i * S.roundVector κ k N i) ≤ sdpSampledWidthBudget α R κ ν := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν k N hgood hacc hgrid hscale hR htol
  have hcost : ∑ i, S.law k i * b i ≤ (∑ j : Fin M, b (S.draws k N j)) / M + R * (κ + ν) := by
    have h := (abs_le.mp (hgood.1 k N).1).2
    linarith
  have hlaw : ∑ i, S.law k i * b i
      ≤ α / Step2Search.gridMass κ N + 2 * R * (κ + ν) := by
    linarith [hacc.2]
  have hrv : 0 ≤ 2 * R * (κ + ν) := by positivity
  have hcan : Step2Search.gridMass κ N * (α / Step2Search.gridMass κ N) = α :=
    mul_div_cancel₀ α hscale.ne'
  have hsum : (∑ i, b i * S.roundVector κ k N i)
      = Step2Search.gridMass κ N * (∑ i, S.law k i * b i) := by
    unfold Step2Search.roundVector
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgm : Step2Search.gridMass κ N
        * (α / Step2Search.gridMass κ N + 2 * R * (κ + ν))
      ≤ α + 2 * R * (κ + ν) * α := by
    have h := mul_le_mul_of_nonneg_right hgrid hrv
    calc Step2Search.gridMass κ N * (α / Step2Search.gridMass κ N + 2 * R * (κ + ν))
        = Step2Search.gridMass κ N * (α / Step2Search.gridMass κ N)
            + Step2Search.gridMass κ N * (2 * R * (κ + ν)) := by ring
      _ ≤ α + α * (2 * R * (κ + ν)) := add_le_add hcan.le h
      _ = α + 2 * R * (κ + ν) * α := by ring
  calc (∑ i, b i * S.roundVector κ k N i)
      = Step2Search.gridMass κ N * (∑ i, S.law k i * b i) := hsum
    _ ≤ Step2Search.gridMass κ N
        * (α / Step2Search.gridMass κ N + 2 * R * (κ + ν)) :=
        mul_le_mul_of_nonneg_left hlaw (le_of_lt hscale)
    _ ≤ α + 2 * R * (κ + ν) * α := hgm
    _ = sdpSampledWidthBudget α R κ ν := by
        unfold sdpSampledWidthBudget
        ring

theorem clause16_separation_side :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
    step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
    Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
    0 ≤ α → 0 ≤ κ + ν →
    S.estC k N - 3 * α * (κ + ν)
      ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν k N hgood hacc hgrid hscale hα htol
  have hB := (hgood.1 k N).2.1
  have hD := (hgood.1 k N).2.2.2.1
  have hlawmean := clause16_law_mean_bound S b A Cv ρ α κ R ν k N hgood
  have hD' : S.estC k N ≥ (Matrix.trace (Cv * ρ)).re - (κ + ν) := by
    have h := (abs_le.mp hD).1
    linarith
  have hest : (∑ j : Fin M, S.estA k N j) / M
      ≤ (∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re) + 2 * (κ + ν) := by
    have h2 : (∑ j : Fin M, S.estA k N j) / M
        ≤ (∑ i : Fin m, S.law k i * (∑ l : Fin L, S.measA k N i l) / L) + (κ + ν) := by
      have h := (abs_le.mp hB).2
      linarith
    linarith
  have hstep : S.estC k N / Step2Search.gridMass κ N - 3 * (κ + ν)
      ≤ ∑ i : Fin m, S.law k i * (Matrix.trace (A i * ρ)).re := by
    have h := hacc.1
    linarith [hest, hD']
  have hcan : Step2Search.gridMass κ N
      * (S.estC k N / Step2Search.gridMass κ N - 3 * (κ + ν))
      = S.estC k N - 3 * (κ + ν) * Step2Search.gridMass κ N := by
    rw [mul_sub, mul_div_cancel₀ _ hscale.ne']
    ring
  have h3 : 0 ≤ 3 * (κ + ν) := by positivity
  have hgm : 3 * (κ + ν) * Step2Search.gridMass κ N ≤ 3 * (κ + ν) * α :=
    mul_le_mul_of_nonneg_left hgrid h3
  have hsum : (∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re)
      = Step2Search.gridMass κ N * (∑ i, S.law k i * (Matrix.trace (A i * ρ)).re) := by
    unfold Step2Search.roundVector
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsc : S.estC k N - 3 * (κ + ν) * Step2Search.gridMass κ N
      ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re := by
    have h := mul_le_mul_of_nonneg_left hstep (le_of_lt hscale)
    rwa [hcan, ← hsum] at h
  linarith [hsc, hgm]

theorem clause16_idealised_transport :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
    step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
    step2Concentration S A ρ κ ν k N → step2IdealAcceptance S A ρ κ ν k N →
    Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
    0 ≤ R → 0 ≤ κ + ν →
    (∑ i, b i * S.roundVector κ k N i) ≤ sdpSampledWidthBudget α R κ ν ∧
      S.estC k N - sdpSampledSeparationSlack α κ ν ≤
        ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν k N hgood hacc hconc hideal hgrid
    hscale hR htol
  have hcost : (∑ i, S.law k i * b i)
      ≤ (∑ j : Fin M, b (S.draws k N j)) / M + R * (κ + ν) := by
    have h := (abs_le.mp (hgood.1 k N).1).2
    linarith
  have hbridge := sdpStep2SampledOracleOnGoodEvent m M (N + 1)
    b (fun i => (Matrix.trace (A i * ρ)).re) (S.law k) (S.draws k N)
    (S.estC k N) α R κ ν
    (by simpa only [Step2Search.gridMass, Nat.cast_add, Nat.cast_one] using! hscale)
    (by simpa only [Step2Search.gridMass, Nat.cast_add, Nat.cast_one] using! hgrid)
    hR htol hcost
    (by simpa only [step2Concentration, Step2Search.gridMass, Nat.cast_add, Nat.cast_one]
      using! hconc)
    (by simpa only [Step2Search.gridMass, Nat.cast_add, Nat.cast_one] using! hacc.2)
    (by simpa only [step2IdealAcceptance, Step2Search.gridMass, Nat.cast_add, Nat.cast_one]
      using! hideal)
  refine ⟨?_, ?_⟩
  · simpa only [Step2Search.roundVector, Step2Search.gridMass, Nat.cast_add, Nat.cast_one]
      using! hbridge.1
  · simpa only [Step2Search.roundVector, Step2Search.gridMass, Nat.cast_add, Nat.cast_one]
      using! hbridge.2

theorem clause16_deviation_gap :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
    step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
    step2Concentration S A ρ κ ν k N → step2IdealAcceptance S A ρ κ ν k N →
    Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
    0 ≤ R → 0 ≤ α → 0 ≤ κ + ν →
    (S.estC k N - 3 * α * (κ + ν)
        ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧
      (S.estC k N - 2 * α * (κ + ν)
        ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧
      (3 * α * (κ + ν) - 2 * α * (κ + ν) = α * (κ + ν)) := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν k N hgood hacc hconc hideal hgrid
    hscale hR hα htol
  have hexec := clause16_separation_side S b A Cv ρ α κ R ν k N hgood hacc hgrid hscale
    hα htol
  have hideal' := clause16_idealised_transport S b A Cv ρ α κ R ν k N hgood hacc hconc
    hideal hgrid hscale hR htol
  refine ⟨hexec, ?_, ?_⟩
  · have hslack : sdpSampledSeparationSlack α κ ν = 2 * α * (κ + ν) := rfl
    linarith [hideal'.2]
  · ring

theorem clause16_no_output_cost :
    ∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ),
    step2GoodEvent S b A Cv ρ α κ R ν → S.noOutput b α R κ ν →
    ∀ (k : Fin γ) (N : Fin Nmax),
      (S.estC k N / Step2Search.gridMass κ N - (κ + ν)
          ≤ (∑ j : Fin M, S.estA k N j) / M) →
      ∑ i, S.law k i * b i > α / Step2Search.gridMass κ N := by
  intro m γ Nmax M L Q D S b A Cv ρ α κ R ν hgood hno k N hpay
  have hnot : ¬ S.accepts b α R κ ν k N := hno k N
  have hcl2 : ¬ ((∑ j : Fin M, b (S.draws k N j)) / M
      ≤ α / Step2Search.gridMass κ N + R * (κ + ν)) := by
    intro h
    exact hnot ⟨hpay, h⟩
  have hneg : (∑ j : Fin M, b (S.draws k N j)) / M
      > α / Step2Search.gridMass κ N + R * (κ + ν) := not_le.mp hcl2
  have hcost : ∑ i, S.law k i * b i
      ≥ (∑ j : Fin M, b (S.draws k N j)) / M - R * (κ + ν) := by
    have h := (abs_le.mp (hgood.1 k N).1).1
    linarith
  linarith

theorem clause16_refuted_boundary :
    ¬ Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator
        Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.A0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.Cv0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.b0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.ρ8 (3:ℝ) (1:ℝ) (1/6:ℝ) := by
  intro h
  have hp : eq75Threshold Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.Cv0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.ρ8 (3:ℝ) (1/6:ℝ)
      ≤ ∑ i : Fin 1, ((1:ℝ) / 4) * (Matrix.trace (Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.A0 i * Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.ρ8)).re := by
    unfold eq75Threshold
    rw [Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.trC,
        Fin.sum_univ_one, Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.trA 0]
    norm_num
  have habs := h (fun _ => (1:ℝ) / 4) (fun _ => by norm_num) hp
  rw [Fin.sum_univ_one] at habs
  exact absurd habs (by
    norm_num [Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.b0, Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth])

theorem clause24_endpoint :

    (∀ {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (ρ : Operator D) (α R ε : ℝ),
      Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator A Cv b ρ α R ε ↔
        step2CheapSeparator A Cv b ρ α R ε) ∧

    (∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
      step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
      Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
      0 ≤ R → 0 ≤ κ + ν →
      (∑ i, b i * S.roundVector κ k N i) ≤ sdpSampledWidthBudget α R κ ν) ∧

    (∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
      step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
      Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
      0 ≤ α → 0 ≤ κ + ν →
      S.estC k N - 3 * α * (κ + ν)
        ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧

    (∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
      step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
      step2Concentration S A ρ κ ν k N → step2IdealAcceptance S A ρ κ ν k N →
      Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
      0 ≤ R → 0 ≤ κ + ν →
      (∑ i, b i * S.roundVector κ k N i) ≤ sdpSampledWidthBudget α R κ ν ∧
        S.estC k N - sdpSampledSeparationSlack α κ ν ≤
          ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧

    (∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ)
      (k : Fin γ) (N : Fin Nmax),
      step2GoodEvent S b A Cv ρ α κ R ν → S.accepts b α R κ ν k N →
      step2Concentration S A ρ κ ν k N → step2IdealAcceptance S A ρ κ ν k N →
      Step2Search.gridMass κ N ≤ α → 0 < Step2Search.gridMass κ N →
      0 ≤ R → 0 ≤ α → 0 ≤ κ + ν →
      (S.estC k N - 3 * α * (κ + ν)
          ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧
        (S.estC k N - 2 * α * (κ + ν)
          ≤ ∑ i, (S.roundVector κ k N i) * (Matrix.trace (A i * ρ)).re) ∧
        (3 * α * (κ + ν) - 2 * α * (κ + ν) = α * (κ + ν))) ∧

    (∀ {m γ Nmax M L Q D : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α κ R ν : ℝ),
      step2GoodEvent S b A Cv ρ α κ R ν → S.noOutput b α R κ ν →
      ∀ (k : Fin γ) (N : Fin Nmax),
        (S.estC k N / Step2Search.gridMass κ N - (κ + ν)
            ≤ (∑ j : Fin M, S.estA k N j) / M) →
        ∑ i, S.law k i * b i > α / Step2Search.gridMass κ N) ∧

    (¬ Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator
        Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.A0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.Cv0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.b0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8.ρ8 (3:ℝ) (1:ℝ) (1/6:ℝ)) := by
  refine ⟨clause16_corrected_direction, clause16_width_side, clause16_separation_side,
    clause16_idealised_transport, clause16_deviation_gap, clause16_no_output_cost,
    clause16_refuted_boundary⟩

theorem width_bridge_identity {D : ℕ} (Cv ρ : Operator D) (α R ε : ℝ) :
    widthSampled α R ε = widthExact α + widthBridgeSlack α R ε ∧
    widthBridgeSlack α R ε = exactWidthSlack α R ε ∧
    separationSlack α ε = 2 * α * ε ∧
    sourcePayoffTarget D Cv ρ α ε = (Matrix.trace (Cv * ρ)).re - 2 * α * ε := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · unfold widthSampled widthExact widthBridgeSlack
    ring
  · unfold widthBridgeSlack exactWidthSlack
    ring

theorem width_rescale_transport {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ)
    (α R ε : ℝ) (hc : 0 < 1 + 2 * R * ε) :
    certificateObjective m b (fun i => y i / (1 + 2 * R * ε)) ≤ widthExact α ↔
      certificateObjective m b y ≤ widthSampled α R ε := by
  set c : ℝ := 1 + 2 * R * ε with hcdef
  have hkey : certificateObjective m b (fun i => y i / c) * c
      = certificateObjective m b y := by
    unfold certificateObjective
    calc
      (∑ i, (y i / c) * b i) * c = ∑ i, ((y i / c) * b i) * c := by rw [Finset.sum_mul]
      _ = ∑ i, y i * b i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp [hc.ne']
  constructor
  · intro h
    have hX : certificateObjective m b (fun i => y i / c) * c ≤ widthExact α * c :=
      mul_le_mul_of_nonneg_right h (le_of_lt hc)
    rw [hkey] at hX
    have hc' : widthExact α * c = widthSampled α R ε := by
      unfold widthSampled widthExact
      rw [hcdef]
    rw [← hc']
    exact hX
  · intro h
    have hc' : widthSampled α R ε = widthExact α * c := by
      unfold widthSampled widthExact
      rw [hcdef]
    have h' : certificateObjective m b y ≤ widthExact α * c := by
      rw [hc'] at h
      exact h
    have hX : certificateObjective m b (fun i => y i / c) * c ≤ widthExact α * c := by
      rw [hkey]
      exact h'
    exact le_of_mul_le_mul_right hX hc

theorem clause17_source_budget_bridge (α R κ ν : ℝ) :
    sdpSampledWidthBudget α R κ ν = widthSampled α R (κ + ν) ∧
    sdpSampledSeparationSlack α κ ν = separationSlack α (κ + ν) ∧
    widthSampled α R (κ + ν) = widthExact α + widthBridgeSlack α R (κ + ν) := by
  refine ⟨rfl, rfl, ?_⟩
  unfold widthSampled widthExact widthBridgeSlack
  ring

theorem clause25_endpoint :
    (∀ {D : ℕ} (Cv ρ : Operator D) (α R ε : ℝ),
      widthSampled α R ε = widthExact α + widthBridgeSlack α R ε ∧
      widthBridgeSlack α R ε = exactWidthSlack α R ε ∧
      separationSlack α ε = 2 * α * ε ∧
      sourcePayoffTarget D Cv ρ α ε = (Matrix.trace (Cv * ρ)).re - 2 * α * ε) ∧
    (∀ {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ) (α R ε : ℝ)
      (_hc : 0 < 1 + 2 * R * ε),
      certificateObjective m b (fun i => y i / (1 + 2 * R * ε)) ≤ widthExact α ↔
        certificateObjective m b y ≤ widthSampled α R ε) ∧
    (∀ (α R κ ν : ℝ),
      sdpSampledWidthBudget α R κ ν = widthSampled α R (κ + ν) ∧
      sdpSampledSeparationSlack α κ ν = separationSlack α (κ + ν) ∧
      widthSampled α R (κ + ν) = widthExact α + widthBridgeSlack α R (κ + ν)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D Cv ρ α R ε
    exact width_bridge_identity Cv ρ α R ε
  · intro m b y α R ε hc
    exact width_rescale_transport b y α R ε hc
  · intro α R κ ν
    exact clause17_source_budget_bridge α R κ ν

theorem dualMixtureWeights_zero {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) :
    dualMixtureWeights a μ 0 = a / dualMixtureScale a μ := by
  rfl

theorem dualMixtureWeights_succ {T : ℕ} (a : ℝ) (μ : Fin T → ℝ) (t : Fin T) :
    dualMixtureWeights a μ t.succ = μ t / (T * dualMixtureScale a μ) := by
  rfl

theorem mixtureComponent_zero {m T : ℕ} (j₀ : Fin m) (q : Fin T → Fin m → ℝ) (j : Fin m) :
    (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
      (fun i => if i = j₀ then (1 : ℝ) else 0) q) 0 j
      = if j = j₀ then 1 else 0 := by
  rfl

theorem mixtureComponent_succ {m T : ℕ} (j₀ : Fin m) (q : Fin T → Fin m → ℝ) (t : Fin T)
    (j : Fin m) :
    (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
      (fun i => if i = j₀ then (1 : ℝ) else 0) q) t.succ j = q t j := by
  rfl

theorem dual_mixture_identity :
    ∀ {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ),
    (∀ t, 0 ≤ μ t) → 0 < a → 0 < T →
    0 < dualMixtureScale a μ ∧
    (∀ i, dualMixtureVector j₀ a μ q i
        = dualMixtureScale a μ * dualMixtureLaw j₀ a μ q i) ∧
    IsWeighting (dualMixtureWeights a μ) ∧
    dualMixtureLaw j₀ a μ q =
      Qatlib.Concepts.SdpDuality.ConeSeparation.mixtureLaw (dualMixtureWeights a μ)
        (fun k : Fin (T + 1) =>
          Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = j₀ then (1 : ℝ) else 0) q k) := by
  intro m T j₀ a μ q hμ ha hT
  have hμsum : 0 ≤ ∑ t : Fin T, μ t := Finset.sum_nonneg fun t _ => hμ t
  have hscale : 0 < dualMixtureScale a μ := by
    unfold dualMixtureScale
    have h1 : (0:ℝ) < a := ha
    have h2 : 0 ≤ (∑ t : Fin T, μ t) / T := by positivity
    linarith
  have hs : dualMixtureScale a μ ≠ 0 := ne_of_gt hscale
  refine ⟨hscale, ?_, ?_, ?_⟩
  · intro i
    unfold dualMixtureVector dualMixtureLaw
    field_simp
  · constructor
    · intro k
      refine Fin.cases (motive := fun k : Fin (T + 1) => 0 ≤ dualMixtureWeights a μ k)
        ?_ (fun t => ?_) k
      · simp only [dualMixtureWeights_zero]
        exact div_nonneg (le_of_lt ha) (le_of_lt hscale)
      · simp only [dualMixtureWeights_succ]
        exact div_nonneg (hμ t)
          (le_of_lt (mul_pos (by exact_mod_cast hT) hscale))
    · have hsum : (∑ k : Fin (T + 1), dualMixtureWeights a μ k)
          = dualMixtureWeights a μ 0 + ∑ t : Fin T, dualMixtureWeights a μ t.succ :=
        Fin.sum_univ_succ (dualMixtureWeights a μ)
      have hzero : dualMixtureWeights a μ 0 = a / dualMixtureScale a μ :=
        dualMixtureWeights_zero a μ
      have hsucc : (∑ t : Fin T, dualMixtureWeights a μ t.succ)
          = ∑ t : Fin T, μ t / (T * dualMixtureScale a μ) := by
        apply Finset.sum_congr rfl
        intro t _
        exact dualMixtureWeights_succ a μ t
      have hdiv : (∑ t : Fin T, μ t / (T * dualMixtureScale a μ))
          = (∑ t : Fin T, μ t) / (T * dualMixtureScale a μ) := by
        rw [← Finset.sum_div]
      rw [hsum, hzero, hsucc, hdiv]
      unfold dualMixtureScale
      field_simp [ne_of_gt hscale, ne_of_gt hT]
  · funext j
    change dualMixtureLaw j₀ a μ q j =
      ∑ k : Fin (T + 1), dualMixtureWeights a μ k *
        (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
          (fun i => if i = j₀ then (1 : ℝ) else 0) q k) j
    have hsum : (∑ k : Fin (T + 1), dualMixtureWeights a μ k *
          (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = j₀ then (1 : ℝ) else 0) q k) j)
        = dualMixtureWeights a μ 0 *
            (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
              (fun i => if i = j₀ then (1 : ℝ) else 0) q 0) j
          + ∑ t : Fin T, dualMixtureWeights a μ t.succ *
            (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
              (fun i => if i = j₀ then (1 : ℝ) else 0) q t.succ) j :=
      Fin.sum_univ_succ (fun k => dualMixtureWeights a μ k *
        (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
          (fun i => if i = j₀ then (1 : ℝ) else 0) q k) j)
    have hzero : dualMixtureWeights a μ 0 = a / dualMixtureScale a μ :=
      dualMixtureWeights_zero a μ
    have hsucc : (∑ t : Fin T, dualMixtureWeights a μ t.succ *
          (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = j₀ then (1 : ℝ) else 0) q t.succ) j)
        = ∑ t : Fin T, μ t / (T * dualMixtureScale a μ) *
          (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = j₀ then (1 : ℝ) else 0) q t.succ) j := by
      apply Finset.sum_congr rfl
      intro t _
      have h := dualMixtureWeights_succ a μ t
      rw [h]
    have hcomp : (∑ t : Fin T, μ t / (T * dualMixtureScale a μ) *
          (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = j₀ then (1 : ℝ) else 0) q t.succ) j)
        = ∑ t : Fin T, μ t / (T * dualMixtureScale a μ) * q t j := by
      apply Finset.sum_congr rfl
      intro t _
      have h := mixtureComponent_succ j₀ q t j
      rw [h]
    have hcomp0 : (Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
          (fun i => if i = j₀ then (1 : ℝ) else 0) q 0) j
        = if j = j₀ then 1 else 0 := mixtureComponent_zero j₀ q j
    have hsum2 : (∑ t : Fin T, μ t / (T * dualMixtureScale a μ) * q t j)
        = (∑ t : Fin T, μ t * q t j) / (T * dualMixtureScale a μ) := by
      calc (∑ t : Fin T, μ t / (T * dualMixtureScale a μ) * q t j)
          = ∑ t : Fin T, (μ t * q t j) / (T * dualMixtureScale a μ) := by
            apply Finset.sum_congr rfl
            intro t _
            ring
        _ = (∑ t : Fin T, μ t * q t j) / (T * dualMixtureScale a μ) := by
          rw [Finset.sum_div]
    rw [hsum, hzero, hsucc, hcomp, hcomp0, hsum2]
    unfold dualMixtureLaw
    by_cases hj : j = j₀
    · simp [hj]
      field_simp [ne_of_gt hscale, ne_of_gt hT]
    · simp [hj]
      field_simp [ne_of_gt hscale, ne_of_gt hT]

theorem clause18_receipt_transport :
    ∀ {m T : ℕ} (S : DualMixtureReceipt m T),
      0 < S.a → (∀ t, 0 ≤ S.μ t) → 0 < T →
      S.law = dualMixtureLaw S.j₀ S.a S.μ S.q ∧
      S.vector = dualMixtureVector S.j₀ S.a S.μ S.q ∧
      IsWeighting (dualMixtureWeights S.a S.μ) ∧
      S.law = Qatlib.Concepts.SdpDuality.ConeSeparation.mixtureLaw (dualMixtureWeights S.a S.μ)
        (fun k : Fin (T + 1) =>
          Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = S.j₀ then (1 : ℝ) else 0) S.q k) := by
  intro m T S ha hμ hT
  have h := dual_mixture_identity S.j₀ S.a S.μ S.q hμ ha hT
  exact ⟨rfl, rfl, h.2.2.1, h.2.2.2⟩

theorem dual_mixture_finite_tree_obstruction :
    ¬ ∃ (choose : SamplerTree (Fin 2)),
        treeRealizes (dualMixtureLaw (0 : Fin 2) (1:ℝ) Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.mu0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.q0) choose := by
  rintro ⟨choose, h⟩
  have hd :=
      Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.samplerTree_law_dyadic choose 1
  have h13 : IsDyadic ((1:ℝ) / 3) := by
    rw [← Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.dualMixtureLaw_q0_one]
    rw [← h 1]
    exact hd
  exact Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.not_isDyadic_one_div_three h13

theorem clause26_endpoint :
    (∀ {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ),
      (∀ t, 0 ≤ μ t) → 0 < a → 0 < T →
      0 < dualMixtureScale a μ ∧
      (∀ i, dualMixtureVector j₀ a μ q i
          = dualMixtureScale a μ * dualMixtureLaw j₀ a μ q i) ∧
      IsWeighting (dualMixtureWeights a μ) ∧
      dualMixtureLaw j₀ a μ q =
        Qatlib.Concepts.SdpDuality.ConeSeparation.mixtureLaw (dualMixtureWeights a μ)
          (fun k : Fin (T + 1) =>
            Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
              (fun i => if i = j₀ then (1 : ℝ) else 0) q k)) ∧
    (∀ {m T : ℕ} (S : DualMixtureReceipt m T),
      0 < S.a → (∀ t, 0 ≤ S.μ t) → 0 < T →
      S.law = dualMixtureLaw S.j₀ S.a S.μ S.q ∧
      S.vector = dualMixtureVector S.j₀ S.a S.μ S.q ∧
      IsWeighting (dualMixtureWeights S.a S.μ) ∧
      S.law = Qatlib.Concepts.SdpDuality.ConeSeparation.mixtureLaw (dualMixtureWeights S.a S.μ)
        (fun k : Fin (T + 1) =>
          Fin.cases (motive := fun _ : Fin (T + 1) => Fin m → ℝ)
            (fun i => if i = S.j₀ then (1 : ℝ) else 0) S.q k)) ∧
    (¬ ∃ (choose : SamplerTree (Fin 2)),
        treeRealizes (dualMixtureLaw (0 : Fin 2) (1:ℝ) Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.mu0 Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9.q0) choose) := by
  refine ⟨dual_mixture_identity, clause18_receipt_transport,
    dual_mixture_finite_tree_obstruction⟩

theorem clause27_rescale_transport :
    ∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (α R δ : ℝ),
    0 < D → 0 < m → 0 < α → 0 < R → 0 < δ →
    (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
    Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
    (∀ i, 1 ≤ b i) →
    (∃ S : Lemma2Rescale A b, S.legal ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i)) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i + S.valueError)) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
          ∃ σ' : Operator D, IsDensityOperator σ' ∧
            (∀ i, (Matrix.trace (A i * σ')).re ≤ S.bp i) ∧
            (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError) ∧
      (∀ σ : Operator D, IsDensityOperator σ →
        (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
          ∃ σ' : Operator D, IsDensityOperator σ' ∧
            (∀ i, (Matrix.trace (A i * σ')).re ≤ b i + S.valueError) ∧
            (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError)) :=
  clause4_lemma2_part

theorem clause19_bisection_ledger :
    ∀ {N : ℕ} (spend : Fin N → BisectionBudget) (L : rescaleLedger),
      0 < N → L.calls = N →
      (∀ i, (spend i).legal (L.failMass / N) (L.errorMass / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ L.failMass) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ L.errorMass) ∧
      L.budget = ⟨N, L.failMass, L.errorMass⟩ := by
  intro N spend L hN hcalls hlegal
  have hfail : ∀ i, (spend i).failMass ≤ L.failMass / N := fun i => (hlegal i).2.2.1
  have herr : ∀ i, (spend i).errorMass ≤ L.errorMass / N := fun i => (hlegal i).2.2.2
  have hN0 : (N : ℝ) ≠ 0 := by
    intro h0
    exact absurd (Nat.cast_eq_zero.mp h0) (Nat.ne_of_gt hN)
  refine ⟨?_, ?_, ?_⟩
  · calc (∑ i : Fin N, (spend i).failMass) ≤ ∑ i : Fin N, L.failMass / N :=
        Finset.sum_le_sum fun i _ => hfail i
      _ = N * (L.failMass / N) := by
          rw [Finset.sum_const, Finset.card_fin]
          simp only [nsmul_eq_mul]
      _ = L.failMass := by field_simp
  · calc (∑ i : Fin N, (spend i).errorMass) ≤ ∑ i : Fin N, L.errorMass / N :=
        Finset.sum_le_sum fun i _ => herr i
      _ = N * (L.errorMass / N) := by
          rw [Finset.sum_const, Finset.card_fin]
          simp only [nsmul_eq_mul]
      _ = L.errorMass := by field_simp
  · unfold rescaleLedger.budget
    rw [hcalls]

theorem clause27_bisection_boundary :
    ¬ (∀ (R δ : ℝ) (N : ℕ) (guess : Fin N → ℝ) (spend : Fin N → BisectionBudget)
        (totalFail totalError : ℝ),
      (∀ i, (spend i).legal (totalFail / N) (totalError / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ totalFail) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ totalError) ∧
      (∀ i, guess i = 0 ∨ guess i = 2 * R ∨ guess i ≤ 0 →
        (spend i).errorMass ≤ totalError / N) ∧
      N ≤ 2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2) :=
  clause4_conj3_refuted

theorem clause27_endpoint :
    (∀ (D m : ℕ) (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (α R δ : ℝ),
      0 < D → 0 < m → 0 < α → 0 < R → 0 < δ →
      (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
      Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
      (∀ i, 1 ≤ b i) →
      (∃ S : Lemma2Rescale A b, S.legal ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
            (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i)) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
            (∀ i, (Matrix.trace (A i * σ)).re ≤ b i + S.valueError)) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ b i) →
            ∃ σ' : Operator D, IsDensityOperator σ' ∧
              (∀ i, (Matrix.trace (A i * σ')).re ≤ S.bp i) ∧
              (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError) ∧
        (∀ σ : Operator D, IsDensityOperator σ →
          (∀ i, (Matrix.trace (A i * σ)).re ≤ S.bp i) →
            ∃ σ' : Operator D, IsDensityOperator σ' ∧
              (∀ i, (Matrix.trace (A i * σ')).re ≤ b i + S.valueError) ∧
              (Matrix.trace (Cv * σ)).re ≤ (Matrix.trace (Cv * σ')).re + S.valueError))) ∧
    (∀ {N : ℕ} (spend : Fin N → BisectionBudget) (L : rescaleLedger),
      0 < N → L.calls = N →
      (∀ i, (spend i).legal (L.failMass / N) (L.errorMass / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ L.failMass) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ L.errorMass) ∧
      L.budget = ⟨N, L.failMass, L.errorMass⟩) ∧
    (¬ (∀ (R δ : ℝ) (N : ℕ) (guess : Fin N → ℝ) (spend : Fin N → BisectionBudget)
        (totalFail totalError : ℝ),
      (∀ i, (spend i).legal (totalFail / N) (totalError / N)) →
      (∑ i : Fin N, (spend i).failMass ≤ totalFail) ∧
      (∑ i : Fin N, (spend i).errorMass ≤ totalError) ∧
      (∀ i, guess i = 0 ∨ guess i = 2 * R ∨ guess i ≤ 0 →
        (spend i).errorMass ≤ totalError / N) ∧
      N ≤ 2 * Nat.ceil (Real.log (4 * R / δ) / Real.log 2) + 2)) := by
  refine ⟨clause27_rescale_transport, clause19_bisection_ledger, clause27_bisection_boundary⟩

theorem clause28_compiled_cost :
    ∀ (steps₁ steps₂ : List MmwCompiledStep),
    (MmwCompiledRun.cost (steps₁ ++ steps₂)).bitTime
        = (MmwCompiledRun.cost steps₁).bitTime + (MmwCompiledRun.cost steps₂).bitTime ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).queries
        = (MmwCompiledRun.cost steps₁).queries + (MmwCompiledRun.cost steps₂).queries ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).gates
        = (MmwCompiledRun.cost steps₁).gates + (MmwCompiledRun.cost steps₂).gates ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).peakSpace
        = max (MmwCompiledRun.cost steps₁).peakSpace
          (MmwCompiledRun.cost steps₂).peakSpace := by
  intro steps₁ steps₂
  have hfold : ∀ (l : List MmwCompiledStep) (acc : ℕ),
      l.foldl (fun a s => max a s.cost.peakSpace) acc
        = max acc (l.foldl (fun a s => max a s.cost.peakSpace) 0) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons s l ih =>
        intro acc
        have h1 := ih (max acc s.cost.peakSpace)
        have h2 := ih s.cost.peakSpace
        simp only [List.foldl_cons]
        rw [h1]
        have hz : max 0 s.cost.peakSpace = s.cost.peakSpace := by omega
        have h3 : l.foldl (fun a s => max a s.cost.peakSpace) (max 0 s.cost.peakSpace)
            = l.foldl (fun a s => max a s.cost.peakSpace) s.cost.peakSpace := by
          rw [hz]
        rw [h3]
        rw [h2]
        exact Nat.max_assoc acc s.cost.peakSpace _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [MmwCompiledRun.cost, List.map_append, List.sum_append]
  · simp [MmwCompiledRun.cost, List.map_append, List.sum_append]
  · simp [MmwCompiledRun.cost, List.map_append, List.sum_append]
  · unfold MmwCompiledRun.cost
    rw [List.foldl_append]
    exact hfold steps₂ (steps₁.foldl (fun a s => max a s.cost.peakSpace) 0)

theorem clause28_compiled_accesses :
    ∀ (steps₁ steps₂ : List MmwCompiledStep),
    MmwCompiledRun.accesses (steps₁ ++ steps₂)
      = MmwCompiledRun.accesses steps₁ ++ MmwCompiledRun.accesses steps₂ := by
  intro steps₁ steps₂
  simp [MmwCompiledRun.accesses, List.flatMap_append]

theorem clause28_fixed_gates :
    ∀ (steps : List MmwCompiledStep), MmwCompiledRun.usesFixedGates steps := by
  intro steps s hs
  cases s <;> simp [MmwGateSet.all, MmwCompiledStep.gateKind]

theorem clause28_fair_bits :
    ∀ (steps : List MmwCompiledStep),
    MmwCompiledRun.fairBits steps
      = (steps.filter (fun s => match s with
          | .rejection _ _ => true
          | _ => false)).length ∧
      MmwCompiledRun.fairBits steps ≤ steps.length := by
  intro steps
  refine ⟨rfl, ?_⟩
  simp only [MmwCompiledRun.fairBits]
  exact List.length_filter_le _ _

theorem clause28_ledger_agreement :
    ∀ (steps : List MmwCompiledStep) (fairBits : ℕ),
    (MmwCompiledRun.ledger steps fairBits).bitTime = (MmwCompiledRun.cost steps).bitTime ∧
      (MmwCompiledRun.ledger steps fairBits).peakQubits
        = (MmwCompiledRun.cost steps).peakSpace ∧
      (MmwCompiledRun.ledger steps fairBits).fairBits = fairBits ∧
      (MmwCompiledRun.ledger steps fairBits).calls.length = steps.length := by
  intro steps fairBits
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold backendCostLedger.bitTime MmwCompiledRun.ledger MmwCompiledRun.cost
    simp only [List.map_map]
    rfl
  · rfl
  · rfl
  · unfold MmwCompiledRun.ledger
    simp

theorem clause28_endpoint :
    (∀ (steps₁ steps₂ : List MmwCompiledStep),
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).bitTime
          = (MmwCompiledRun.cost steps₁).bitTime + (MmwCompiledRun.cost steps₂).bitTime ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).queries
          = (MmwCompiledRun.cost steps₁).queries + (MmwCompiledRun.cost steps₂).queries ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).gates
          = (MmwCompiledRun.cost steps₁).gates + (MmwCompiledRun.cost steps₂).gates ∧
      (MmwCompiledRun.cost (steps₁ ++ steps₂)).peakSpace
          = max (MmwCompiledRun.cost steps₁).peakSpace
            (MmwCompiledRun.cost steps₂).peakSpace) ∧
    (∀ (steps₁ steps₂ : List MmwCompiledStep),
      MmwCompiledRun.accesses (steps₁ ++ steps₂)
        = MmwCompiledRun.accesses steps₁ ++ MmwCompiledRun.accesses steps₂) ∧
    (∀ (steps : List MmwCompiledStep), MmwCompiledRun.usesFixedGates steps) ∧
    (∀ (steps : List MmwCompiledStep),
      MmwCompiledRun.fairBits steps
        = (steps.filter (fun s => match s with
            | .rejection _ _ => true
            | _ => false)).length ∧
      MmwCompiledRun.fairBits steps ≤ steps.length) ∧
    (∀ (steps : List MmwCompiledStep) (fairBits : ℕ),
      (MmwCompiledRun.ledger steps fairBits).bitTime = (MmwCompiledRun.cost steps).bitTime ∧
      (MmwCompiledRun.ledger steps fairBits).peakQubits
        = (MmwCompiledRun.cost steps).peakSpace ∧
      (MmwCompiledRun.ledger steps fairBits).fairBits = fairBits ∧
      (MmwCompiledRun.ledger steps fairBits).calls.length = steps.length) := by
  refine ⟨clause28_compiled_cost, clause28_compiled_accesses, clause28_fixed_gates, clause28_fair_bits,
    clause28_ledger_agreement⟩

end
end Qatlib.Concepts.SdpDuality.ConeSeparation

namespace Qatlib.Concepts.SdpDuality.ConeSeparation.SdpDuality
open Matrix Qatlib.Concepts.DyadicFloor.FloorRounding Qatlib.Concepts.SdpDuality.StrongDuality
open scoped InnerProductSpace ComplexOrder BigOperators
set_option warningAsError false
noncomputable section

def ApproxFeasible {𝕜 : Type} [RCLike 𝕜] {D m : ℕ}
    (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X : HermitianMat (Fin D) 𝕜, 0 ≤ X ∧ ‖A X-b‖ < ε

theorem approximate_iff_closed_image {𝕜 : Type} [RCLike 𝕜] {D m : ℕ}
    (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    ApproxFeasible A b ↔ b ∈ (finitePsdCone 𝕜 D).map A := by
  change ApproxFeasible A b ↔ b ∈ closure (A '' {X : HermitianMat (Fin D) 𝕜 | 0 ≤ X})
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨X,hX,he⟩ := h ε hε
    exact ⟨A X, ⟨X,hX,rfl⟩, by simpa only [dist_eq_norm, norm_sub_rev] using! he⟩
  · intro h ε hε
    obtain ⟨y,⟨X,hX,rfl⟩,he⟩ := h ε hε
    exact ⟨X,hX,by simpa only [dist_eq_norm, norm_sub_rev] using! he⟩

theorem approximate_farkas {𝕜 : Type} [RCLike 𝕜] {D m : ℕ}
    (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    ApproxFeasible A b ↔ ∀ y, 0 ≤ A.adjoint y → 0 ≤ ⟪b,y⟫_ℝ := by
  rw [approximate_iff_closed_image]
  exact ((finitePsdGeometry 𝕜 D).2.2.2.2 m A b).1

theorem strict_separator_iff_not_approximate {𝕜 : Type} [RCLike 𝕜] {D m : ℕ}
    (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) :
    (∃ y, 0 ≤ A.adjoint y ∧ ⟪b,y⟫_ℝ < 0) ↔ ¬ ApproxFeasible A b := by
  rw [approximate_iff_closed_image]
  exact ((finitePsdGeometry 𝕜 D).2.2.2.2 m A b).2.symm

theorem separator_residual_lower_bound {𝕜 : Type} [RCLike 𝕜] {D m : ℕ}
    (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b y : EuclideanSpace ℝ (Fin m)) (hy : 0 ≤ A.adjoint y)
    (X : HermitianMat (Fin D) 𝕜) (hX : 0 ≤ X) :
    -⟪b,y⟫_ℝ ≤ ‖A X-b‖*‖y‖ := by
  have hp : 0 ≤ ⟪A X,y⟫_ℝ := by
    have hh := A.adjoint_inner_right X y
    exact hh ▸ HermitianMat.inner_ge_zero hX hy
  have hb := real_inner_le_norm (A X-b) y
  rw [inner_sub_left] at hb
  linarith

def cornerMap : HermitianMat (Fin 2) ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => WithLp.toLp 2 ![(X.mat 0 0).re, (X.mat 0 1).re]
      map_add' := by
        intro X Y
        ext i
        fin_cases i
        · change ((X.mat + Y.mat) 0 0).re = (X.mat 0 0).re + (Y.mat 0 0).re
          exact Complex.add_re _ _
        · change ((X.mat + Y.mat) 0 1).re = (X.mat 0 1).re + (Y.mat 0 1).re
          exact Complex.add_re _ _
      map_smul' := by
        intro c X
        ext i
        fin_cases i <;> simp }

def cornerTarget : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![0,1]

@[simp] theorem cornerMap_zero (X : HermitianMat (Fin 2) ℂ) : cornerMap X 0 = (X.mat 0 0).re := rfl

@[simp] theorem cornerMap_one (X : HermitianMat (Fin 2) ℂ) : cornerMap X 1 = (X.mat 0 1).re := rfl

theorem corner_infeasible : ¬ ∃ X : HermitianMat (Fin 2) ℂ, 0 ≤ X ∧ cornerMap X = cornerTarget := by
  rintro ⟨X,hX,h⟩
  exact weak_corner_infeasible ⟨X,hX,congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h,
    congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h⟩

theorem corner_residual_family (ε : ℝ) (hε : 0 < ε) :
    ∃ X : HermitianMat (Fin 2) ℂ, 0 ≤ X ∧ ‖cornerMap X-cornerTarget‖ = ε := by
  obtain ⟨X,hX,h0,h1⟩ := weak_corner_approximate ε hε
  refine ⟨X,hX,?_⟩
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, cornerMap_zero, cornerMap_one, h0,h1,
    cornerTarget, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Real.norm_eq_abs, sq_abs, Real.sqrt_sq_eq_abs, abs_of_pos hε]

theorem corner_approximately_feasible : ApproxFeasible cornerMap cornerTarget := by
  intro ε hε
  obtain ⟨X,hX,hres⟩ := corner_residual_family (ε/2) (by positivity)
  exact ⟨X,hX,by rw [hres]; linarith⟩

theorem corner_no_strict_separator : ¬ ∃ y, 0 ≤ cornerMap.adjoint y ∧ ⟪cornerTarget,y⟫_ℝ < 0 := by
  rw [strict_separator_iff_not_approximate]
  exact not_not.mpr corner_approximately_feasible

theorem corner_image_not_closed : ¬ IsClosed (cornerMap '' {X : HermitianMat (Fin 2) ℂ | 0 ≤ X}) := by
  intro hc
  have ht := (approximate_iff_closed_image cornerMap cornerTarget).mp corner_approximately_feasible
  change cornerTarget ∈ closure (cornerMap '' {X : HermitianMat (Fin 2) ℂ | 0 ≤ X}) at ht
  rw [hc.closure_eq] at ht
  obtain ⟨X,hX,hEq⟩ := ht
  exact corner_infeasible ⟨X,hX,hEq⟩

theorem frontier1 : FinitePsdGeometry ℝ ∧ FinitePsdGeometry ℂ ∧
    (∀ (𝕜 : Type) [RCLike 𝕜] (D m : ℕ)
      (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m)),
      (ApproxFeasible A b ↔ ∀ y, 0 ≤ A.adjoint y → 0 ≤ ⟪b,y⟫_ℝ) ∧
      ((∃ y, 0 ≤ A.adjoint y ∧ ⟪b,y⟫_ℝ < 0) ↔ ¬ ApproxFeasible A b)) ∧
    (¬ ∃ X : HermitianMat (Fin 2) ℂ, 0 ≤ X ∧ cornerMap X = cornerTarget) ∧
    (∀ ε : ℝ, 0 < ε → ∃ X : HermitianMat (Fin 2) ℂ, 0 ≤ X ∧ ‖cornerMap X-cornerTarget‖ = ε) ∧
    ApproxFeasible cornerMap cornerTarget ∧
    (¬ ∃ y, 0 ≤ cornerMap.adjoint y ∧ ⟪cornerTarget,y⟫_ℝ < 0) ∧
    ¬ IsClosed (cornerMap '' {X : HermitianMat (Fin 2) ℂ | 0 ≤ X}) := by
  exact ⟨finitePsdGeometry ℝ, finitePsdGeometry ℂ,
    fun _ _ _ _ A b => ⟨approximate_farkas A b, strict_separator_iff_not_approximate A b⟩,
    corner_infeasible, corner_residual_family, corner_approximately_feasible,
    corner_no_strict_separator, corner_image_not_closed⟩

end
end Qatlib.Concepts.SdpDuality.ConeSeparation.SdpDuality
