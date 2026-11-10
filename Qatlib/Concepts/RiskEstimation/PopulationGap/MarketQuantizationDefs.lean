/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.ContinuousMarketCDFDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib
open Matrix
open scoped ENNReal Classical BigOperators
open Qatlib
open Qatlib.Concepts.RiskEstimation.CDFEstimation
open Qatlib.Concepts.RiskEstimation.CVaREstimation
open Qatlib
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.RiskEstimation.VaRQuantile
open Qatlib.Concepts.RiskEstimation.VaRQuantile.Papers.QuantumRiskAnalysis2018
open Qatlib
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
variable {n N : ℕ}

namespace Qatlib.Concepts.RiskEstimation.PopulationGap

def gridThreshold (Δ : ℝ) (i : ℕ) : ℝ := (i : ℝ) * Δ

theorem gridThreshold_zero (Δ : ℝ) : gridThreshold Δ 0 = 0 := by
  simp only [gridThreshold, Nat.cast_zero, zero_mul]

theorem gridThreshold_mono {Δ : ℝ} (hΔ : 0 ≤ Δ) {i j : ℕ} (h : i ≤ j) :
    gridThreshold Δ i ≤ gridThreshold Δ j := by
  unfold gridThreshold
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hΔ

theorem gridThreshold_step (Δ : ℝ) (i : ℕ) :
    gridThreshold Δ (i+1) = gridThreshold Δ i + Δ := by
  unfold gridThreshold
  push_cast
  ring

theorem marketCDF_mono {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {t t' : ℝ} (ht : t ≤ t') :
    marketCDF p loss t ≤ marketCDF p loss t' := by
  unfold marketCDF
  apply Finset.sum_le_sum
  intro a _
  have h : (if loss a ≤ t then (1 : ℝ) else (0 : ℝ))
      ≤ (if loss a ≤ t' then (1 : ℝ) else (0 : ℝ)) := by
    by_cases h1 : loss a ≤ t
    · by_cases h2 : loss a ≤ t'
      · simp [h1, h2]
      · exact absurd (h1.trans ht) h2
    · by_cases h2 : loss a ≤ t'
      · simp [h1, h2]
      · simp [h1, h2]
  exact mul_le_mul_of_nonneg_left h (p.nonneg a)

theorem marketCDF_eq_zero_of_neg {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a) {t : ℝ} (ht : t < 0) :
    marketCDF p loss t = 0 := by
  unfold marketCDF
  apply Finset.sum_eq_zero
  intro a _
  have hlt : t < loss a := lt_of_lt_of_le ht (hloss a)
  rw [if_neg (not_le_of_gt hlt)]
  ring

def marketVaRAt {n : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℝ)
    (q t : ℝ) : Prop :=
  q ≤ marketCDF p loss t ∧ ∀ s < t, marketCDF p loss s < q

theorem marketVaRAt_unique {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {q t t' : ℝ}
    (ht : marketVaRAt p loss q t) (ht' : marketVaRAt p loss q t') (h : t < t') : False := by
  rcases ht with ⟨htq, hts⟩
  rcases ht' with ⟨ht'q, ht's⟩
  have h1 : marketCDF p loss t < q := ht's t h
  linarith [htq]

noncomputable def marketGridSet {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) : Finset (Fin (iT+1)) :=
  Finset.univ.filter (fun i : Fin (iT+1) => q ≤ marketCDF p loss (gridThreshold Δ i.1))

noncomputable def marketGridIndex {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) : ℕ :=
  if h : (marketGridSet p loss Δ q iT).Nonempty then
    (Finset.min' (marketGridSet p loss Δ q iT) h).1
  else iT + 1

theorem marketGridIndex_spec {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ)
    (hcap : q ≤ marketCDF p loss (gridThreshold Δ iT)) :
    marketGridIndex p loss Δ q iT ≤ iT ∧
    q ≤ marketCDF p loss (gridThreshold Δ (marketGridIndex p loss Δ q iT)) ∧
    (∀ j : ℕ, j < marketGridIndex p loss Δ q iT →
      marketCDF p loss (gridThreshold Δ j) < q) := by
  classical
  have hne : (marketGridSet p loss Δ q iT).Nonempty := by
    refine ⟨⟨iT, by omega⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcap⟩
  rw [marketGridIndex, dif_pos hne]
  have hmem : Finset.min' (marketGridSet p loss Δ q iT) hne ∈ marketGridSet p loss Δ q iT :=
    Finset.min'_mem _ _
  have hmem' := Finset.mem_filter.mp hmem
  have hxlt : (Finset.min' (marketGridSet p loss Δ q iT) hne).val < iT + 1 :=
    (Finset.min' (marketGridSet p loss Δ q iT) hne).isLt
  refine ⟨Nat.le_of_lt_succ hxlt, hmem'.2, ?_⟩
  intro j hj
  by_contra hcon
  push Not at hcon
  have hfin : j < iT + 1 := by omega
  have hmemj : (⟨j, hfin⟩ : Fin (iT+1)) ∈ marketGridSet p loss Δ q iT :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩
  have hmin : Finset.min' (marketGridSet p loss Δ q iT) hne ≤ ⟨j, hfin⟩ :=
    Finset.min'_le (marketGridSet p loss Δ q iT) ⟨j, hfin⟩ hmemj
  have hv : (Finset.min' (marketGridSet p loss Δ q iT) hne).val ≤ j :=
    Fin.le_iff_val_le_val.mp hmin
  exact absurd (Nat.lt_of_lt_of_le hj hv) (Nat.lt_irrefl _)

theorem marketGrid_bracket {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) (t : ℝ)
    (hloss : ∀ a, 0 ≤ loss a) (hq : 0 < q)
    (hcap : q ≤ marketCDF p loss (gridThreshold Δ iT))
    (hv : marketVaRAt p loss q t) :
    (marketGridIndex p loss Δ q iT = 0 ∧ t = gridThreshold Δ 0) ∨
    (0 < marketGridIndex p loss Δ q iT ∧
      gridThreshold Δ (marketGridIndex p loss Δ q iT) - Δ < t ∧
      t ≤ gridThreshold Δ (marketGridIndex p loss Δ q iT)) := by
  classical
  rcases marketGridIndex_spec p loss Δ q iT hcap with ⟨hle, hreach, hbelow⟩
  rcases hv with ⟨htq, hts⟩
  have hupper : t ≤ gridThreshold Δ (marketGridIndex p loss Δ q iT) := by
    by_contra hcon
    push Not at hcon
    have h1 : marketCDF p loss (gridThreshold Δ (marketGridIndex p loss Δ q iT)) < q :=
      hts _ hcon
    linarith [hreach]
  by_cases hzero : marketGridIndex p loss Δ q iT = 0
  · left
    refine ⟨hzero, ?_⟩
    have hnonneg : 0 ≤ t := by
      by_contra hcon
      push Not at hcon
      have hz : marketCDF p loss t = 0 := marketCDF_eq_zero_of_neg p loss hloss hcon
      linarith [htq]
    have hupper' : t ≤ gridThreshold Δ 0 := by
      rw [hzero] at hupper
      exact hupper
    have hz : t = 0 := by
      rw [gridThreshold_zero] at hupper'
      exact le_antisymm hupper' hnonneg
    rw [gridThreshold_zero]
    exact hz
  · right
    refine ⟨by omega, ?_, hupper⟩
    have hpos : 0 < marketGridIndex p loss Δ q iT := by omega
    have hprev : gridThreshold Δ (marketGridIndex p loss Δ q iT - 1) < t := by
      by_contra hcon
      push Not at hcon
      have hmono := marketCDF_mono p loss hcon
      have h1 : marketCDF p loss (gridThreshold Δ (marketGridIndex p loss Δ q iT - 1)) < q :=
        hbelow (marketGridIndex p loss Δ q iT - 1) (by omega)
      linarith [htq]
    have hstep : gridThreshold Δ (marketGridIndex p loss Δ q iT)
        = gridThreshold Δ (marketGridIndex p loss Δ q iT - 1) + Δ := by
      have h := gridThreshold_step Δ (marketGridIndex p loss Δ q iT - 1)
      have h2 : marketGridIndex p loss Δ q iT - 1 + 1 = marketGridIndex p loss Δ q iT :=
        Nat.sub_add_cancel (by omega)
      rw [h2] at h
      exact h
    linarith [hprev, hstep]

theorem marketGrid_quantization {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) (t : ℝ)
    (hloss : ∀ a, 0 ≤ loss a) (hΔ : 0 < Δ) (hq : 0 < q)
    (hcap : q ≤ marketCDF p loss (gridThreshold Δ iT))
    (hv : marketVaRAt p loss q t) :
    |gridThreshold Δ (marketGridIndex p loss Δ q iT) - t| ≤ Δ := by
  classical
  rcases marketGrid_bracket p loss Δ q iT t hloss hq hcap hv with h0 | ⟨hi, hlow, hhi⟩
  · rw [h0.1, h0.2, gridThreshold_zero, sub_self, abs_zero]
    exact le_of_lt hΔ
  · rw [abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith [hlow]

noncomputable def marketGridRecordSet {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) : Finset (Fin (iT+1)) :=
  Finset.univ.filter (fun i : Fin (iT+1) =>
    q ≤ marketEmpiricalCDF ω loss (gridThreshold Δ i.1))

noncomputable def marketGridRecordIndex {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) : ℕ :=
  if h : (marketGridRecordSet ω loss Δ q iT).Nonempty then
    (Finset.min' (marketGridRecordSet ω loss Δ q iT) h).1
  else iT + 1

theorem marketGridRecordIndex_spec {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ q : ℝ) (iT : ℕ) :
    (marketGridRecordIndex ω loss Δ q iT ≤ iT ∧
      q ≤ marketEmpiricalCDF ω loss
        (gridThreshold Δ (marketGridRecordIndex ω loss Δ q iT))) ∨
    (marketGridRecordIndex ω loss Δ q iT = iT + 1 ∧
      ∀ j : ℕ, j ≤ iT →
        marketEmpiricalCDF ω loss (gridThreshold Δ j) < q) := by
  classical
  by_cases hne : (marketGridRecordSet ω loss Δ q iT).Nonempty
  · left
    rw [marketGridRecordIndex, dif_pos hne]
    have hmem := Finset.min'_mem (marketGridRecordSet ω loss Δ q iT) hne
    have hmem' := Finset.mem_filter.mp hmem
    have hxlt : (Finset.min' (marketGridRecordSet ω loss Δ q iT) hne).val < iT + 1 :=
      (Finset.min' (marketGridRecordSet ω loss Δ q iT) hne).isLt
    refine ⟨Nat.le_of_lt_succ hxlt, hmem'.2⟩
  · right
    rw [marketGridRecordIndex, dif_neg hne]
    refine ⟨rfl, ?_⟩
    intro j hj
    by_contra hcon
    push Not at hcon
    have hfin : j < iT + 1 := by omega
    have hmem : (⟨j, hfin⟩ : Fin (iT+1)) ∈ marketGridRecordSet ω loss Δ q iT :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩
    exact hne ⟨⟨j, hfin⟩, hmem⟩

def marketGridGood {n N : ℕ} (p : FinDist (Option (Fin n))) (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℝ) (Δ ν : ℝ) (iT : ℕ) : Prop :=
  ∀ j : Fin (iT+1),
    |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
      - marketCDF p loss (gridThreshold Δ j.1)| ≤ ν

def marketGridGap {n : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℝ)
    (Δ q ν : ℝ) (iT : ℕ) : Prop :=
  q + ν ≤ marketCDF p loss (gridThreshold Δ (marketGridIndex p loss Δ q iT)) ∧
  ∀ j : ℕ, j < marketGridIndex p loss Δ q iT →
    marketCDF p loss (gridThreshold Δ j) < q - ν

theorem marketGridRecordIndex_eq_of_good {n N : ℕ} (p : FinDist (Option (Fin n)))
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q ν : ℝ) (iT : ℕ)
    (hcap : q ≤ marketCDF p loss (gridThreshold Δ iT))
    (hgood : marketGridGood p ω loss Δ ν iT)
    (hgap : marketGridGap p loss Δ q ν iT) :
    marketGridRecordIndex ω loss Δ q iT = marketGridIndex p loss Δ q iT := by
  classical
  rcases marketGridIndex_spec p loss Δ q iT hcap with ⟨hle, hreach, hbelow⟩
  rcases hgap with ⟨hcross, hlow⟩
  have hle' : marketGridIndex p loss Δ q iT < iT + 1 := by omega
  have hmemI : (⟨marketGridIndex p loss Δ q iT, hle'⟩ : Fin (iT+1))
      ∈ marketGridRecordSet ω loss Δ q iT := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have habs := abs_le.mp (hgood ⟨marketGridIndex p loss Δ q iT, hle'⟩)
    linarith [hcross]
  have hno : ∀ j : Fin (iT+1), j.1 < marketGridIndex p loss Δ q iT →
      j ∉ marketGridRecordSet ω loss Δ q iT := by
    intro j hj hmem
    have hmem' := Finset.mem_filter.mp hmem
    have habs := abs_le.mp (hgood j)
    have hlowj := hlow j.1 hj
    linarith
  have hneR : (marketGridRecordSet ω loss Δ q iT).Nonempty :=
    ⟨⟨marketGridIndex p loss Δ q iT, hle'⟩, hmemI⟩
  rw [marketGridRecordIndex, dif_pos hneR]
  have hmin_le : Finset.min' (marketGridRecordSet ω loss Δ q iT) hneR
      ≤ ⟨marketGridIndex p loss Δ q iT, hle'⟩ :=
    Finset.min'_le (marketGridRecordSet ω loss Δ q iT)
      ⟨marketGridIndex p loss Δ q iT, hle'⟩ hmemI
  have hmin_ge : ⟨marketGridIndex p loss Δ q iT, hle'⟩
      ≤ Finset.min' (marketGridRecordSet ω loss Δ q iT) hneR :=
    Finset.le_min' (marketGridRecordSet ω loss Δ q iT) hneR
      ⟨marketGridIndex p loss Δ q iT, hle'⟩ (fun y hy => by
      have hy' := Finset.mem_filter.mp hy
      by_contra hc
      push Not at hc
      exact hno ⟨y.1, y.isLt⟩ hc
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩))
  exact le_antisymm hmin_le hmin_ge

theorem marketGrid_uniform_sampling_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ ν : ℝ) (iT : ℕ) (hN : 0 < N) (hν : 0 < ν) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ j : Fin (iT+1),
          ν < |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
            - marketCDF p loss (gridThreshold Δ j.1)|)
      ≤ ((iT+1 : ℝ))/(4*(N : ℝ)*ν^2) := by
  classical
  let E : Fin (iT+1) → (Fin N → Option (Fin n)) → Prop := fun j ω =>
    ν < |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
      - marketCDF p loss (gridThreshold Δ j.1)|
  have h := p.union_bound E
  have hs : FinDist.probEvent (L := N) p
      (fun ω : Fin N → Option (Fin n) => ∃ j : Fin (iT+1), E j ω)
      = FinDist.probEvent (L := N) p
      (fun ω : Fin N → Option (Fin n) => ∃ j : Fin (iT+1),
          ν < |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
            - marketCDF p loss (gridThreshold Δ j.1)|) := by
    unfold FinDist.probEvent
    congr 1
  rw [hs]
  apply h.trans
  calc
    (∑ j : Fin (iT+1), FinDist.probEvent (L := N) p (E j))
      ≤ ∑ j : Fin (iT+1), 1/(4*(N : ℝ)*ν^2) :=
      Finset.sum_le_sum (fun j _ =>
        marketCDF_sampling_bound p loss (gridThreshold Δ j.1) ν hN hν)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

theorem marketGrid_sample_budget {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (Δ ν : ℝ) (iT : ℕ) (hN : 0 < N) (hν : 0 < ν)
    (hbudget : ((iT+1 : ℝ))/(4*(N : ℝ)*ν^2) ≤ 1/2) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ j : Fin (iT+1),
          ν < |marketEmpiricalCDF ω loss (gridThreshold Δ j.1)
            - marketCDF p loss (gridThreshold Δ j.1)|) ≤ 1/2 :=
  le_trans (marketGrid_uniform_sampling_bound p loss Δ ν iT hN hν) hbudget

theorem marketGrid_quantization_of_good {n N : ℕ} (p : FinDist (Option (Fin n)))
    (ω : Fin N → Option (Fin n)) (loss : Option (Fin n) → ℝ) (Δ q ν : ℝ) (iT : ℕ) (t : ℝ)
    (hloss : ∀ a, 0 ≤ loss a) (hΔ : 0 < Δ) (hq : 0 < q)
    (hcap : q ≤ marketCDF p loss (gridThreshold Δ iT))
    (hv : marketVaRAt p loss q t)
    (hgood : marketGridGood p ω loss Δ ν iT)
    (hgap : marketGridGap p loss Δ q ν iT) :
    marketGridRecordIndex ω loss Δ q iT = marketGridIndex p loss Δ q iT ∧
    |gridThreshold Δ (marketGridRecordIndex ω loss Δ q iT) - t| ≤ Δ := by
  refine ⟨marketGridRecordIndex_eq_of_good p ω loss Δ q ν iT hcap hgood hgap, ?_⟩
  rw [marketGridRecordIndex_eq_of_good p ω loss Δ q ν iT hcap hgood hgap]
  exact marketGrid_quantization p loss Δ q iT t hloss hΔ hq hcap hv

noncomputable def marketTailMoment {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) : ℝ :=
  ∑ a, p.prob a * (if loss a ≤ t then loss a else 0)

noncomputable def marketCVaR {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (t : ℝ) : ℝ :=
  marketTailMoment p loss t / marketCDF p loss t

theorem marketTailMoment_nonneg {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a) (t : ℝ) :
    0 ≤ marketTailMoment p loss t := by
  unfold marketTailMoment
  apply Finset.sum_nonneg
  intro a _
  by_cases h : loss a ≤ t
  · simp only [if_pos h]
    exact mul_nonneg (p.nonneg a) (hloss a)
  · simp only [if_neg h]
    exact mul_nonneg (p.nonneg a) (le_refl 0)

theorem marketTailMoment_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a) (t : ℝ) :
    marketTailMoment p loss t ≤ t * marketCDF p loss t := by
  have hpoint : ∀ a : Option (Fin n),
      (if loss a ≤ t then loss a else 0) ≤ (if loss a ≤ t then t else 0) := by
    intro a
    by_cases h : loss a ≤ t <;> simp [h]
  have hmain : (∑ a, p.prob a * (if loss a ≤ t then loss a else 0))
      ≤ ∑ a, p.prob a * (if loss a ≤ t then t else 0) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a))
  calc
    marketTailMoment p loss t = ∑ a, p.prob a * (if loss a ≤ t then loss a else 0) := rfl
    _ ≤ ∑ a, p.prob a * (if loss a ≤ t then t else 0) := hmain
    _ = t * marketCDF p loss t := by
      unfold marketCDF
      calc
        (∑ a, p.prob a * (if loss a ≤ t then t else 0))
            = ∑ a, p.prob a * (t * (if loss a ≤ t then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro a _
              by_cases h : loss a ≤ t
              · have h1 : (if loss a ≤ t then (t:ℝ) else (0:ℝ)) = t := if_pos h
                have h2 : (if loss a ≤ t then (1:ℝ) else (0:ℝ)) = 1 := if_pos h
                rw [h1, h2]
                ring
              · have h1 : (if loss a ≤ t then (t:ℝ) else (0:ℝ)) = 0 := if_neg h
                have h2 : (if loss a ≤ t then (1:ℝ) else (0:ℝ)) = 0 := if_neg h
                rw [h1, h2]
                ring
        _ = t * (∑ a, p.prob a * (if loss a ≤ t then 1 else 0)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              ring

theorem marketTailMoment_mono {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a) {t g : ℝ} (ht : t ≤ g) :
    marketTailMoment p loss t ≤ marketTailMoment p loss g := by
  have hpoint : ∀ a : Option (Fin n),
      (if loss a ≤ t then loss a else 0) ≤ (if loss a ≤ g then loss a else 0) := by
    intro a
    by_cases h1 : loss a ≤ t
    · have h2 : loss a ≤ g := h1.trans ht
      simp [h1, h2]
    · by_cases h2 : loss a ≤ g
      · simp [h1, h2]
        exact hloss a
      · simp [h1, h2]
  unfold marketTailMoment
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a))

theorem marketCVaR_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a) (t : ℝ)
    (hF : 0 < marketCDF p loss t) : marketCVaR p loss t ≤ t := by
  have h := marketTailMoment_le p loss hloss t
  unfold marketCVaR
  rw [div_le_iff₀ hF]
  exact h

theorem marketTailMoment_window {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {t g : ℝ} (ht : t ≤ g) :
    marketTailMoment p loss g - marketTailMoment p loss t
      = ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then loss a else 0) := by
  have hpoint : ∀ a : Option (Fin n),
      (if loss a ≤ g then loss a else 0) - (if loss a ≤ t then loss a else 0)
        = (if t < loss a ∧ loss a ≤ g then loss a else 0) := by
    intro a
    by_cases hg : loss a ≤ g
    · by_cases ht' : loss a ≤ t
      · simp [hg, ht']
      · have hlt : t < loss a := lt_of_not_ge ht'
        simp [hg, ht', hlt]
    · have hltg : g < loss a := lt_of_not_ge hg
      have hlt : t < loss a := lt_of_le_of_lt ht hltg
      have hnlt : ¬ loss a ≤ t := not_le_of_gt hlt
      simp [hg, hnlt]
  calc
    marketTailMoment p loss g - marketTailMoment p loss t
        = (∑ a, p.prob a * (if loss a ≤ g then loss a else 0))
          - (∑ a, p.prob a * (if loss a ≤ t then loss a else 0)) := rfl
    _ = ∑ a, (p.prob a * (if loss a ≤ g then loss a else 0)
          - p.prob a * (if loss a ≤ t then loss a else 0)) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ a, p.prob a * ((if loss a ≤ g then loss a else 0)
          - (if loss a ≤ t then loss a else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then loss a else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hpoint a]

theorem marketCDF_window {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {t g : ℝ} (ht : t ≤ g) :
    marketCDF p loss g - marketCDF p loss t
      = ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then 1 else 0) := by
  have hpoint : ∀ a : Option (Fin n),
      ((if loss a ≤ g then (1:ℝ) else (0:ℝ)) - (if loss a ≤ t then (1:ℝ) else (0:ℝ)))
        = (if t < loss a ∧ loss a ≤ g then (1:ℝ) else (0:ℝ)) := by
    intro a
    by_cases hg : loss a ≤ g
    · by_cases ht' : loss a ≤ t
      · simp [hg, ht']
      · have hlt : t < loss a := lt_of_not_ge ht'
        simp [hg, ht', hlt]
    · have hltg : g < loss a := lt_of_not_ge hg
      have hlt : t < loss a := lt_of_le_of_lt ht hltg
      have hnlt : ¬ loss a ≤ t := not_le_of_gt hlt
      simp [hg, hnlt]
  calc
    marketCDF p loss g - marketCDF p loss t
        = (∑ a, p.prob a * (if loss a ≤ g then 1 else 0))
          - (∑ a, p.prob a * (if loss a ≤ t then 1 else 0)) := rfl
    _ = ∑ a, (p.prob a * (if loss a ≤ g then 1 else 0)
          - p.prob a * (if loss a ≤ t then 1 else 0)) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ a, p.prob a * ((if loss a ≤ g then 1 else 0)
          - (if loss a ≤ t then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
    _ = ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hpoint a]

theorem marketTailMoment_window_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, loss a ≤ 1) {t g : ℝ} (ht : t ≤ g) :
    marketTailMoment p loss g - marketTailMoment p loss t
      ≤ marketCDF p loss g - marketCDF p loss t := by
  have hpoint : ∀ a : Option (Fin n),
      (if t < loss a ∧ loss a ≤ g then loss a else 0)
        ≤ (if t < loss a ∧ loss a ≤ g then 1 else 0) := by
    intro a
    by_cases h : t < loss a ∧ loss a ≤ g
    · simp [h, hloss a]
    · simp [h]
  have hmain : (∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then loss a else 0))
      ≤ ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then 1 else 0) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a))
  rw [marketTailMoment_window p loss ht, marketCDF_window p loss ht]
  exact hmain

theorem marketTailMoment_window_ge {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {t g : ℝ} (ht : t ≤ g) :
    t * (marketCDF p loss g - marketCDF p loss t)
      ≤ marketTailMoment p loss g - marketTailMoment p loss t := by
  have hpoint : ∀ a : Option (Fin n),
      t * (if t < loss a ∧ loss a ≤ g then 1 else 0)
        ≤ (if t < loss a ∧ loss a ≤ g then loss a else 0) := by
    intro a
    by_cases h : t < loss a ∧ loss a ≤ g
    · have h1 : t ≤ loss a := h.1.le
      simp [h]
      linarith
    · simp [h]
  have hmain : (∑ a, p.prob a * (t * (if t < loss a ∧ loss a ≤ g then 1 else 0)))
      ≤ ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then loss a else 0) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hpoint a) (p.nonneg a))
  rw [marketTailMoment_window p loss ht, marketCDF_window p loss ht]
  calc
    t * (∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then 1 else 0))
        = ∑ a, p.prob a * (t * (if t < loss a ∧ loss a ≤ g then 1 else 0)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            ring
    _ ≤ ∑ a, p.prob a * (if t < loss a ∧ loss a ≤ g then loss a else 0) := hmain

theorem marketCVaR_sub_cleared {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) {t g : ℝ}
    (hFt : 0 < marketCDF p loss t) (hFg : 0 < marketCDF p loss g) :
    marketCDF p loss g * marketCDF p loss t
        * (marketCVaR p loss g - marketCVaR p loss t)
      = marketTailMoment p loss g * marketCDF p loss t
        - marketTailMoment p loss t * marketCDF p loss g := by
  unfold marketCVaR
  field_simp

theorem marketCVaR_window_deviation {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    {t g : ℝ} (ht : t ≤ g)
    (hFt : 0 < marketCDF p loss t) (hFg : 0 < marketCDF p loss g) :
    marketCVaR p loss g - marketCVaR p loss t
      ≤ (marketCDF p loss g - marketCDF p loss t) / marketCDF p loss g := by
  have hcleared := marketCVaR_sub_cleared p loss hFt hFg
  have hC : marketTailMoment p loss g - marketTailMoment p loss t
      ≤ marketCDF p loss g - marketCDF p loss t :=
    marketTailMoment_window_le p loss (fun a => (hloss a).2) ht
  have hnum : marketTailMoment p loss g * marketCDF p loss t
      - marketTailMoment p loss t * marketCDF p loss g
      ≤ (marketCDF p loss g - marketCDF p loss t) * marketCDF p loss t := by
    have hA : 0 ≤ marketTailMoment p loss t :=
      marketTailMoment_nonneg p loss (fun a => (hloss a).1) t
    have hB : 0 ≤ marketCDF p loss t := hFt.le
    have hD : 0 ≤ marketCDF p loss g - marketCDF p loss t := by
      have := marketCDF_mono p loss ht
      linarith
    nlinarith [hC, hA, hB, hD]
  have hmul : marketCDF p loss g * marketCDF p loss t
      * (marketCVaR p loss g - marketCVaR p loss t)
      ≤ (marketCDF p loss g - marketCDF p loss t) * marketCDF p loss t := by
    linarith [hcleared, hnum]
  have hmul' : marketCDF p loss g * (marketCVaR p loss g - marketCVaR p loss t)
      ≤ marketCDF p loss g - marketCDF p loss t := by
    have h1 := hmul
    field_simp at h1
    nlinarith [h1]
  rw [le_div_iff₀ hFg]
  nlinarith [hmul']

theorem marketCVaR_flat_window_exact {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    {t g : ℝ} (ht : t ≤ g)
    (hFt : 0 < marketCDF p loss t) (hFg : 0 < marketCDF p loss g)
    (hflat : marketCDF p loss g = marketCDF p loss t) :
    marketCVaR p loss g = marketCVaR p loss t := by
  have hC : marketTailMoment p loss g - marketTailMoment p loss t
      ≤ marketCDF p loss g - marketCDF p loss t :=
    marketTailMoment_window_le p loss (fun a => (hloss a).2) ht
  have hzero : marketTailMoment p loss g - marketTailMoment p loss t = 0 := by
    have hnonneg : 0 ≤ marketTailMoment p loss g - marketTailMoment p loss t := by
      have h1 : marketTailMoment p loss t ≤ marketTailMoment p loss g :=
        marketTailMoment_mono p loss (fun a => (hloss a).1) ht
      linarith
    linarith [hC, hflat]
  unfold marketCVaR
  have h1 : marketTailMoment p loss g = marketTailMoment p loss t := by linarith
  rw [h1, hflat]

def marketCDFLipschitz {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (ρ : ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b → marketCDF p loss b - marketCDF p loss a ≤ ρ * (b - a)

theorem marketCVaR_deviation_le {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℝ) (hloss : ∀ a, 0 ≤ loss a ∧ loss a ≤ 1)
    (ρ : ℝ) {t g : ℝ} (ht : t ≤ g) (hρ : 0 ≤ ρ)
    (hFt : 0 < marketCDF p loss t) (hFg : 0 < marketCDF p loss g)
    (hLip : marketCDFLipschitz p loss ρ) :
    marketCVaR p loss g - marketCVaR p loss t
      ≤ ρ * (g - t) / marketCDF p loss g := by
  have hwindow := marketCVaR_window_deviation p loss hloss ht hFt hFg
  have hmass : marketCDF p loss g - marketCDF p loss t ≤ ρ * (g - t) := by
    have h1 := hLip t g ht
    linarith
  rw [le_div_iff₀ hFg]
  have h1 := mul_le_mul_of_nonneg_left hwindow hFg.le
  have h2 : marketCDF p loss g
      * ((marketCDF p loss g - marketCDF p loss t) / marketCDF p loss g)
      = marketCDF p loss g - marketCDF p loss t := by
    field_simp
  have h3 : marketCDF p loss g
      * (ρ * (g - t) / marketCDF p loss g) = ρ * (g - t) := by
    field_simp
  rw [h2] at h1
  nlinarith [hmass]
end Qatlib.Concepts.RiskEstimation.PopulationGap
