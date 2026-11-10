/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.AmplitudeReadoutDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.NativeRiskDefs
import Qatlib.Concepts.NativeNumerics.EmpiricalRisk.EmpiricalRiskConsumers
import Qatlib.Concepts.RiskEstimation.PopulationGap.PopulationRiskCVaRDefs
import Qatlib.Concepts.RiskEstimation.VaRQuantile.BisectFiniteRoutingSubgoalQuan
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.RiskEstimation.PopulationGap.Implementation
import Qatlib.Concepts.RiskEstimation.PopulationGap.ImplementationDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.GatesDefs
import Qatlib.Concepts.RiskEstimation.PopulationGap.OrderShorDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.FairRandomBits.EmpiricalWeight
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.NativeNumerics.EmpiricalRisk
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
noncomputable def exactVaRSet {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) : Finset ℕ :=
  (Finset.range xs.length).filter (fun v => q ≤ populationCDF p loss (xs.getD v 0))

noncomputable def exactVaRIndex {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) : ℕ :=
  if h : (exactVaRSet p loss xs q).Nonempty then (exactVaRSet p loss xs q).min' h
  else xs.length

noncomputable def sampleVaRSet {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) : Finset ℕ :=
  (Finset.range xs.length).filter
    (fun v => q ≤ (empiricalCDF ω loss (xs.getD v 0) : ℝ))

noncomputable def sampleVaRIndex {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) : ℕ :=
  if h : (sampleVaRSet ω loss xs q).Nonempty then (sampleVaRSet ω loss xs q).min' h
  else xs.length

theorem exactVaRIndex_spec {n : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) :
    (exactVaRIndex p loss xs q < xs.length →
      q ≤ populationCDF p loss (xs.getD (exactVaRIndex p loss xs q) 0)) ∧
    (∀ u, u < exactVaRIndex p loss xs q →
      populationCDF p loss (xs.getD u 0) < q) := by
  classical
  unfold exactVaRIndex
  split
  · rename_i h
    have hminmem : (exactVaRSet p loss xs q).min' h ∈ exactVaRSet p loss xs q :=
      Finset.min'_mem (exactVaRSet p loss xs q) h
    have hminfilter := Finset.mem_filter.mp hminmem
    have hminlt : (exactVaRSet p loss xs q).min' h < xs.length := by
      have hx := hminfilter.1
      rw [Finset.mem_range] at hx
      exact hx
    refine ⟨?_, ?_⟩
    · intro _
      exact hminfilter.2
    · intro u hu
      have hnotu : u ∉ exactVaRSet p loss xs q := by
        intro hin
        have hle := Finset.min'_le (exactVaRSet p loss xs q) u hin
        omega
      have hnin : ¬ (u ∈ Finset.range xs.length ∧
          q ≤ populationCDF p loss (xs.getD u 0)) := by
        intro hin
        exact hnotu (Finset.mem_filter.mpr hin)
      exact lt_of_not_ge (fun hq => hnin ⟨Finset.mem_range.mpr (by omega), hq⟩)
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro hv
      exact absurd hv (by simp)
    · intro u hu
      have hnin : ¬ (u ∈ Finset.range xs.length ∧
          q ≤ populationCDF p loss (xs.getD u 0)) := by
        intro hin
        exact h ⟨u, Finset.mem_filter.mpr hin⟩
      exact lt_of_not_ge (fun hq => hnin ⟨Finset.mem_range.mpr (by omega), hq⟩)

theorem sampleVaRIndex_spec {n N : ℕ} (ω : Fin N → Option (Fin n))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q : ℝ) :
    (sampleVaRIndex ω loss xs q < xs.length →
      q ≤ (empiricalCDF ω loss (xs.getD (sampleVaRIndex ω loss xs q) 0) : ℝ)) ∧
    (∀ u, u < sampleVaRIndex ω loss xs q →
      (empiricalCDF ω loss (xs.getD u 0) : ℝ) < q) := by
  classical
  unfold sampleVaRIndex
  split
  · rename_i h
    have hminmem : (sampleVaRSet ω loss xs q).min' h ∈ sampleVaRSet ω loss xs q :=
      Finset.min'_mem (sampleVaRSet ω loss xs q) h
    have hminfilter := Finset.mem_filter.mp hminmem
    have hminlt : (sampleVaRSet ω loss xs q).min' h < xs.length := by
      have hx := hminfilter.1
      rw [Finset.mem_range] at hx
      exact hx
    refine ⟨?_, ?_⟩
    · intro _
      exact hminfilter.2
    · intro u hu
      have hnotu : u ∉ sampleVaRSet ω loss xs q := by
        intro hin
        have hle := Finset.min'_le (sampleVaRSet ω loss xs q) u hin
        omega
      have hnin : ¬ (u ∈ Finset.range xs.length ∧
          q ≤ (empiricalCDF ω loss (xs.getD u 0) : ℝ)) := by
        intro hin
        exact hnotu (Finset.mem_filter.mpr hin)
      exact lt_of_not_ge (fun hq => hnin ⟨Finset.mem_range.mpr (by omega), hq⟩)
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro hv
      exact absurd hv (by simp)
    · intro u hu
      have hnin : ¬ (u ∈ Finset.range xs.length ∧
          q ≤ (empiricalCDF ω loss (xs.getD u 0) : ℝ)) := by
        intro hin
        exact h ⟨u, Finset.mem_filter.mpr hin⟩
      exact lt_of_not_ge (fun hq => hnin ⟨Finset.mem_range.mpr (by omega), hq⟩)

def cdfGood {n N : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
    (xs : List ℚ) (ν : ℝ) (ω : Fin N → Option (Fin n)) : Prop :=
  ∀ t ∈ xs, |(empiricalCDF ω loss t : ℝ) - populationCDF p loss t| ≤ ν

def exactVaRGap {n : ℕ} (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ)
    (xs : List ℚ) (q ν : ℝ) : Prop :=
  let v := exactVaRIndex p loss xs q
  v < xs.length ∧
  (∀ u, u < v → populationCDF p loss (xs.getD u 0) + ν < q) ∧
  (q + ν ≤ populationCDF p loss (xs.getD v 0))

theorem sampleVaRIndex_eq_exact_of_good {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q ν : ℝ)
    (ω : Fin N → Option (Fin n)) (hgood : cdfGood p loss xs ν ω)
    (hgap : exactVaRGap p loss xs q ν) :
    sampleVaRIndex ω loss xs q = exactVaRIndex p loss xs q := by
  classical
  rcases hgap with ⟨hvlt, hg1, hg2⟩
  have hmem_v : xs.getD (exactVaRIndex p loss xs q) 0 ∈ xs := by
    rw [List.getD_eq_getElem xs 0 hvlt]
    exact List.getElem_mem hvlt
  have hclose_v : |(empiricalCDF ω loss (xs.getD (exactVaRIndex p loss xs q) 0) : ℝ)
      - populationCDF p loss (xs.getD (exactVaRIndex p loss xs q) 0)| ≤ ν :=
    hgood (xs.getD (exactVaRIndex p loss xs q) 0) hmem_v
  have hge : (empiricalCDF ω loss (xs.getD (exactVaRIndex p loss xs q) 0) : ℝ) ≥ q := by
    have h := abs_le.mp hclose_v
    linarith
  have hvinset : exactVaRIndex p loss xs q ∈ sampleVaRSet ω loss xs q := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr hvlt, hge⟩
  have hnot : ∀ u, u < exactVaRIndex p loss xs q →
      u ∉ sampleVaRSet ω loss xs q := by
    intro u hu
    have hmem_u : xs.getD u 0 ∈ xs := by
      have hlt : u < xs.length := by
        have := hu
        omega
      rw [List.getD_eq_getElem xs 0 hlt]
      exact List.getElem_mem hlt
    have hclose_u : |(empiricalCDF ω loss (xs.getD u 0) : ℝ)
        - populationCDF p loss (xs.getD u 0)| ≤ ν :=
      hgood (xs.getD u 0) hmem_u
    have habs := abs_le.mp hclose_u
    intro hin
    have hq := (Finset.mem_filter.mp hin).2
    have hq1 := hg1 u hu
    linarith
  unfold sampleVaRIndex
  split
  · rename_i h
    have h1 := Finset.min'_le (sampleVaRSet ω loss xs q) (exactVaRIndex p loss xs q) hvinset
    have h2 := Finset.min'_mem (sampleVaRSet ω loss xs q) h
    have h3 : exactVaRIndex p loss xs q ≤ (sampleVaRSet ω loss xs q).min' h := by
      by_contra hc
      exact hnot _ (lt_of_not_ge hc) h2
    omega
  · rename_i h
    exact absurd ⟨exactVaRIndex p loss xs q, hvinset⟩ h

theorem exactVaR_recovery_bound {n N : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (q ν : ℝ)
    (hN : 0 < N) (hν : 0 < ν) (hgap : exactVaRGap p loss xs q ν) :
    FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
      sampleVaRIndex ω loss xs q ≠ exactVaRIndex p loss xs q)
      ≤ (xs.length : ℝ)/(4*(N : ℝ)*ν^2) := by
  classical
  have hmono : FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        sampleVaRIndex ω loss xs q ≠ exactVaRIndex p loss xs q)
      ≤ FinDist.probEvent (L := N) p (fun ω : Fin N → Option (Fin n) =>
        ∃ t ∈ xs, ν < |(empiricalCDF ω loss t : ℝ)-populationCDF p loss t|) := by
    unfold FinDist.probEvent
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      rw [Finset.mem_filter] at hω
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hnotbad
      have hgood : cdfGood p loss xs ν ω := by
        intro t ht
        by_contra hcon
        exact hnotbad ⟨t, ht, lt_of_not_ge hcon⟩
      exact hω.2 (sampleVaRIndex_eq_exact_of_good p loss xs q ν ω hgood hgap)
    · intro ω _ _
      exact Finset.prod_nonneg fun i _ => p.nonneg (ω i)
  exact hmono.trans (empirical_uniform_cdf_sampling_bound p loss xs ν hN hν)

theorem sampleVaRIndex_population_bounds_of_good {n N : ℕ}
    (p : FinDist (Option (Fin n))) (loss : Option (Fin n) → ℚ) (xs : List ℚ)
    (q ν : ℝ) (ω : Fin N → Option (Fin n)) (hgood : cdfGood p loss xs ν ω)
    (hvlt : sampleVaRIndex ω loss xs q < xs.length) :
    q - ν ≤ populationCDF p loss (xs.getD (sampleVaRIndex ω loss xs q) 0) ∧
    (∀ u, u < sampleVaRIndex ω loss xs q →
      populationCDF p loss (xs.getD u 0) < q + ν) := by
  classical
  have hspec := sampleVaRIndex_spec ω loss xs q
  have hmem_v : xs.getD (sampleVaRIndex ω loss xs q) 0 ∈ xs := by
    rw [List.getD_eq_getElem xs 0 hvlt]
    exact List.getElem_mem hvlt
  have hclose_v : |(empiricalCDF ω loss (xs.getD (sampleVaRIndex ω loss xs q) 0) : ℝ)
      - populationCDF p loss (xs.getD (sampleVaRIndex ω loss xs q) 0)| ≤ ν :=
    hgood (xs.getD (sampleVaRIndex ω loss xs q) 0) hmem_v
  have habs_v := abs_le.mp hclose_v
  have hq := hspec.1 hvlt
  constructor
  · linarith
  · intro u hu
    have hmem_u : xs.getD u 0 ∈ xs := by
      have hlt : u < xs.length := by
        have := hu
        omega
      rw [List.getD_eq_getElem xs 0 hlt]
      exact List.getElem_mem hlt
    have hclose_u : |(empiricalCDF ω loss (xs.getD u 0) : ℝ)
        - populationCDF p loss (xs.getD u 0)| ≤ ν :=
      hgood (xs.getD u 0) hmem_u
    have habs_u := abs_le.mp hclose_u
    have hu' := hspec.2 u hu
    linarith

theorem prepared_cdf_transport {n N bits : ℕ} (p : FinDist (Option (Fin n)))
    (loss : Option (Fin n) → ℚ) (xs : List ℚ) (ν : ℝ)
    (ω : Fin N → Option (Fin n)) (hN : 0 < N) (hgood : cdfGood p loss xs ν ω) :
    ∀ t ∈ xs,
      |riskCDF (empiricalPrepare ω bits) none loss t - populationCDF p loss t|
        ≤ ν + 64*(n : ℝ)/2^bits := by
  intro t ht
  have hprep := (empirical_actual_preparation_cdf_bias n N bits ω loss t hN).2
  have hclose := hgood t ht
  calc
    |riskCDF (empiricalPrepare ω bits) none loss t - populationCDF p loss t|
      ≤ |riskCDF (empiricalPrepare ω bits) none loss t - (empiricalCDF ω loss t : ℝ)|
        + |(empiricalCDF ω loss t : ℝ) - populationCDF p loss t| :=
      abs_sub_le _ _ _
    _ ≤ ν + 64*(n : ℝ)/2^bits := by
      have h1 := abs_le.mp hprep
      have h2 := abs_le.mp hclose
      linarith

def twoAtomLoss (x : Option (Fin 2)) : ℚ := if x = some 1 then 1 else 0

noncomputable def twoAtomProb (a : ℝ) (x : Option (Fin 2)) : ℝ :=
  if x = some 0 then a else if x = some 1 then 1 - a else 0

noncomputable def twoAtomPop (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : FinDist (Option (Fin 2)) where
  prob := twoAtomProb a
  nonneg := by
    intro x
    unfold twoAtomProb
    split_ifs <;> linarith
  sum_one := by
    have h := Fintype.sum_option (f := twoAtomProb a)
    have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 => twoAtomProb a (some y)))
    rw [h, h2]
    simp [twoAtomProb]

noncomputable def noGapPop : FinDist (Option (Fin 2)) :=
  twoAtomPop (1/2) (by norm_num) (by norm_num)

noncomputable def nearPop (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) : FinDist (Option (Fin 2)) :=
  twoAtomPop (1/2 - ε) (by linarith) (by linarith)

theorem twoAtomPop_cdf_zero (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    populationCDF (twoAtomPop a ha0 ha1) twoAtomLoss 0 = a := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold populationCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if twoAtomLoss x ≤ 0 then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if twoAtomLoss (some y) ≤ 0 then 1 else 0)))
  rw [h, h2]
  simp [twoAtomProb, twoAtomLoss]

theorem twoAtomPop_cdf_one (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    populationCDF (twoAtomPop a ha0 ha1) twoAtomLoss 1 = 1 := by
  have hprob : (twoAtomPop a ha0 ha1).prob = twoAtomProb a := rfl
  unfold populationCDF
  rw [hprob]
  have h := Fintype.sum_option (f := fun x : Option (Fin 2) =>
    twoAtomProb a x * (if twoAtomLoss x ≤ 1 then 1 else 0))
  have h2 := Fin.sum_univ_two (f := (fun y : Fin 2 =>
    twoAtomProb a (some y) * (if twoAtomLoss (some y) ≤ 1 then 1 else 0)))
  rw [h, h2]
  simp [twoAtomProb, twoAtomLoss]

theorem twoAtom_exactVaRSet_mem (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v : ℕ) :
    v ∈ exactVaRSet (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2) ↔
      (v = 0 ∧ (1/2:ℝ) ≤ a) ∨ (v = 1) := by
  constructor
  · intro hin
    have h := Finset.mem_filter.mp hin
    rcases h with ⟨hvlt, hq⟩
    rw [Finset.mem_range] at hvlt
    have hlen : ([0, 1] : List ℚ).length = 2 := rfl
    rw [hlen] at hvlt
    have hv : v = 0 ∨ v = 1 := by omega
    rcases hv with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      rw [show (List.getD ([0, 1] : List ℚ) 0 0) = 0 from rfl,
        twoAtomPop_cdf_zero a ha0 ha1] at hq
      exact hq
    · right
      rfl
  · intro hin
    rcases hin with ⟨hv, ha2⟩ | hv
    · subst hv
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (by simp)
      · rw [show (List.getD ([0, 1] : List ℚ) 0 0) = 0 from rfl,
          twoAtomPop_cdf_zero a ha0 ha1]
        exact ha2
    · subst hv
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (by simp)
      · rw [show (List.getD ([0, 1] : List ℚ) 1 0) = 1 from rfl,
          twoAtomPop_cdf_one a ha0 ha1]
        norm_num

theorem twoAtom_exactVaRIndex_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : (1/2:ℝ) ≤ a) :
    exactVaRIndex (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2) = 0 := by
  unfold exactVaRIndex
  have hne : (exactVaRSet (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2)).Nonempty := by
    refine ⟨1, ?_⟩
    rw [twoAtom_exactVaRSet_mem]
    exact Or.inr rfl
  split
  · rename_i h
    have hle := Finset.min'_le (exactVaRSet (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2))
      0 (by rw [twoAtom_exactVaRSet_mem]; exact Or.inl ⟨rfl, ha⟩)
    omega
  · rename_i h
    exact absurd hne h

theorem twoAtom_exactVaRIndex_gt (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ha : a < (1/2:ℝ)) :
    exactVaRIndex (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2) = 1 := by
  unfold exactVaRIndex
  have hne : (exactVaRSet (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2)).Nonempty := by
    refine ⟨1, ?_⟩
    rw [twoAtom_exactVaRSet_mem]
    exact Or.inr rfl
  split
  · rename_i h
    have hminmem := Finset.min'_mem (exactVaRSet (twoAtomPop a ha0 ha1) twoAtomLoss [0, 1] (1/2)) h
    rw [twoAtom_exactVaRSet_mem] at hminmem
    rcases hminmem with ⟨h0, h1⟩ | h1
    · exact absurd h1 (not_le_of_gt ha)
    · omega
  · rename_i h
    exact absurd hne h

theorem twoAtomProbOf_all_some_one (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a < 1) (N : ℕ) :
    0 < (twoAtomPop a ha0 (le_of_lt ha2)).probOf (fun _ : Fin N => some (1 : Fin 2)) := by
  have hprob : (twoAtomPop a ha0 (le_of_lt ha2)).prob = twoAtomProb a := rfl
  unfold FinDist.probOf
  rw [hprob]
  have hprod : (∏ i : Fin N, twoAtomProb a (some 1)) = (twoAtomProb a (some 1))^N := by
    rw [Finset.prod_const]
    simp [Fintype.card_fin]
  rw [hprod]
  have hpos : 0 < twoAtomProb a (some 1) := by
    simp [twoAtomProb]
    linarith
  exact pow_pos hpos N

theorem empiricalCDF_all_some_one (N : ℕ) (hN : 0 < N) (t : ℚ) :
    (empiricalCDF (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss t : ℝ) =
      if (1:ℚ) ≤ t then 1 else 0 := by
  rw [empiricalCDF_avg]
  unfold FinDist.avg
  have hsum : (∑ k : Fin N, riskCDFPayoff twoAtomLoss t (some 1))
      = (if (1:ℚ) ≤ t then 1 else 0) * N := by
    by_cases h : (1:ℚ) ≤ t
    · simp [riskCDFPayoff, twoAtomLoss, h]
    · simp [riskCDFPayoff, twoAtomLoss, h]
  rw [hsum]
  by_cases h : (1:ℚ) ≤ t
  · rw [if_pos h]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    calc
      ((1:ℝ) * (N:ℝ)) / (N:ℝ) = (N:ℝ) / (N:ℝ) := by rw [one_mul]
      _ = 1 := div_self hN0
  · rw [if_neg h]
    calc
      ((0:ℝ) * (N:ℝ)) / (N:ℝ) = 0 := by rw [zero_mul, zero_div]

theorem sampleVaRIndex_all_some_one (N : ℕ) (hN : 0 < N) :
    sampleVaRIndex (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2) = 1 := by
  have h0 := empiricalCDF_all_some_one N hN 0
  have h1 := empiricalCDF_all_some_one N hN 1
  have hnot0 : 0 ∉ sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2) := by
    intro hin
    have hq := (Finset.mem_filter.mp hin).2
    rw [show (List.getD ([0, 1] : List ℚ) 0 0) = 0 from rfl] at hq
    rw [h0] at hq
    norm_num at hq
  have hmem1 : 1 ∈ sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by simp), ?_⟩
    rw [show (List.getD ([0, 1] : List ℚ) 1 0) = 1 from rfl]
    rw [h1]
    norm_num
  unfold sampleVaRIndex
  have hne : (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)).Nonempty :=
    ⟨1, hmem1⟩
  split
  · rename_i h
    have hminmem := Finset.min'_mem
      (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)) h
    have hminle := Finset.min'_le
      (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)) 1 hmem1
    have hlen : ([0, 1] : List ℚ).length = 2 := rfl
    have hrange : (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)).min' h < 2 := by
      have hx := (Finset.mem_filter.mp hminmem).1
      rw [Finset.mem_range] at hx
      rw [hlen] at hx
      exact hx
    have hne0 : (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)).min' h ≠ 0 := by
      intro hc
      apply hnot0
      exact Eq.mp (congrArg (fun k => k ∈ sampleVaRSet
        (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)) hc) hminmem
    have : (sampleVaRSet (fun _ : Fin N => some (1 : Fin 2)) twoAtomLoss [0, 1] (1/2)).min' h = 1 := by
      omega
    omega
  · rename_i h
    exact absurd hne h

theorem probEvent_lt_one_of_not_mem {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E]
    (ω : Fin L → X) (hnot : ¬ E ω) (hω : 0 < p.probOf ω) : p.probEvent E < 1 := by
  have hnotmem : ω ∉ (Finset.univ : Finset (Fin L → X)).filter E := by
    intro hmem
    exact hnot (Finset.mem_filter.mp hmem).2
  have hsub : (Finset.univ : Finset (Fin L → X)).filter E
      ⊆ (Finset.univ : Finset (Fin L → X)).erase ω :=
    Finset.subset_erase.mpr ⟨Finset.subset_univ _, hnotmem⟩
  have hle : (∑ x ∈ (Finset.univ : Finset (Fin L → X)).filter E, p.probOf x)
      ≤ ∑ x ∈ (Finset.univ : Finset (Fin L → X)).erase ω, p.probOf x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => Finset.prod_nonneg fun k _ => p.nonneg (i k))
  have herase : (∑ x ∈ (Finset.univ : Finset (Fin L → X)).erase ω, p.probOf x)
      + p.probOf ω = 1 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin L → X))
      (fun i => p.probOf i) (Finset.mem_univ ω)
    rw [p.sum_probOf L] at h
    exact h
  show (∑ x ∈ (Finset.univ : Finset (Fin L → X)).filter E, p.probOf x) < 1
  calc
    (∑ x ∈ (Finset.univ : Finset (Fin L → X)).filter E, p.probOf x)
        ≤ ∑ x ∈ (Finset.univ : Finset (Fin L → X)).erase ω, p.probOf x := hle
    _ < 1 := by linarith

theorem probEvent_eq_one_imp {X : Type} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (E : (Fin L → X) → Prop) [DecidablePred E]
    (h : p.probEvent E = 1) (ω : Fin L → X) (hω : 0 < p.probOf ω) : E ω := by
  by_contra hnot
  have hlt := probEvent_lt_one_of_not_mem p E ω hnot hω
  linarith

theorem sampleVaRIndex_success_lt_one {N : ℕ} (hN : 0 < N) :
    FinDist.probEvent (L := N) noGapPop (fun ω : Fin N → Option (Fin 2) =>
      sampleVaRIndex ω twoAtomLoss [0, 1] (1/2) = 0) < 1 := by
  classical
  apply probEvent_lt_one_of_not_mem noGapPop (fun ω : Fin N → Option (Fin 2) =>
    sampleVaRIndex ω twoAtomLoss [0, 1] (1/2) = 0) (fun _ : Fin N => some (1 : Fin 2))
  · rw [sampleVaRIndex_all_some_one N hN]
    norm_num
  · exact twoAtomProbOf_all_some_one (1/2) (by norm_num) (by norm_num) N

theorem exactVaR_no_procedure_exact_under_both {N : ℕ} (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1/2) (alg : (Fin N → Option (Fin 2)) → ℕ) :
    ¬ (FinDist.probEvent (L := N) noGapPop (fun ω : Fin N → Option (Fin 2) =>
          alg ω = 0) = 1 ∧
        FinDist.probEvent (L := N) (nearPop ε hε hε1) (fun ω : (Fin N → Option (Fin 2)) =>
          alg ω = 1) = 1) := by
  classical
  rintro ⟨h1, h2⟩
  have hmass := probEvent_eq_one_imp noGapPop (fun ω : (Fin N → Option (Fin 2)) => alg ω = 0)
    h1 (fun _ : Fin N => some (1 : Fin 2))
    (twoAtomProbOf_all_some_one (1/2) (by norm_num) (by norm_num) N)
  have hmass' := probEvent_eq_one_imp (nearPop ε hε hε1)
    (fun ω : (Fin N → Option (Fin 2)) => alg ω = 1) h2 (fun _ : Fin N => some (1 : Fin 2))
    (twoAtomProbOf_all_some_one (1/2 - ε) (by linarith) (by linarith) N)
  omega
end Qatlib.Concepts.RiskEstimation.PopulationGap
