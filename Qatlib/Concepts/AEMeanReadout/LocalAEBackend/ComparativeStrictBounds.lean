/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3QSearchQuan
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutCore
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadout
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem17Stat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Bound
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchLoop
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchBudget

/-!
# Strict amplitude-estimation probability bounds

This module proves strict lower bounds for phase and amplitude readout windows in the
amplitude-estimation analysis of [BrassardEtAl2002]. The bounds pass from
`bhmt11WindowMass_strict` through QPE kernels to prepared amplitude estimation and
Fourier-prepared counting.

The module also bounds both expected query counters of the source and shifted search loops by
`400 / √a` when the marked mass `a` is positive, uniformly over finite horizons.

## Main statements

* `strictSpacedTail`: a strict reciprocal-square tail bound for separated values.
* `preparedAeWindow_strict`: a strict probability bound for the prepared amplitude window.
* `countingWindow_strict`: the corresponding strict counting bound.
* `source_and_shifted_two_ledger_budget`: expected query bounds for both search loops.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib
open Matrix
open scoped ENNReal Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTQSearch
open Qatlib
open Qatlib
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.BHMTTh17
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Filter
open scoped Topology

/-- For positive marked mass `a`, each of the two expected query counters of both search loops
is at most `400 / √a`, uniformly in the finite horizon `T`. -/
theorem source_and_shifted_two_ledger_budget {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (T : ℕ) (ha : 0 < MeasureProb (preparedAAState A j₀) S) :
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (sourceQSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.1 : ℝ≥0∞))
        ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) ∧
    (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (BHMTQSearch.qSearchLoop A hA j₀ S T 0) (fun out => (out.2.2 : ℝ≥0∞))
      ≤ ENNReal.ofReal (400 / Real.sqrt (MeasureProb (preparedAAState A j₀) S))) := by
  refine ⟨sourceLoop_ledger1_expectation_le A hA j₀ S T ha,
    sourceLoop_ledger2_expectation_le A hA j₀ S T ha, ?_, ?_⟩
  · have h := bhmt_theorem3_qsearch (I := I) A hA j₀ S T
    have h' := h.2.2 ha
    exact h'.1
  · have h := bhmt_theorem3_qsearch (I := I) A hA j₀ S T
    have h' := h.2.2 ha
    exact h'.2

/-- The sum of reciprocal squares of finitely many real values greater than `k > 1`, separated
pairwise by at least one, is strictly less than `1 / (k - 1)`. -/
theorem strictSpacedTail {α : Type*} (s : Finset α) (f : α → ℝ) (k : ℝ) (hk : 1 < k)
    (hlo : ∀ a ∈ s, k < f a)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → 1 ≤ |f a - f b|) :
    ∑ a ∈ s, 1 / f a ^ 2 < 1 / (k - 1) := by
  classical
  have hk1 : 0 < k - 1 := by linarith
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty]
    exact (lt_div_iff₀ hk1).mpr (by simp)
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image f hs
  have hka : k < f a := hlo a ha
  have ha1 : 1 < f a := lt_trans hk hka
  have he : ∑ b ∈ s.erase a, 1 / f b ^ 2 ≤ 1 / f a := by
    have hh := bhmt_phase_estimation_theorem11_spaced_tail (s.erase a) f (f a + 1)
      (show 1 < f a + 1 by linarith)
      (fun b hb => by
        have hb' := Finset.mem_erase.mp hb
        have hm := hmin b hb'.2
        have hd := hsep a ha b hb'.2 (Ne.symm hb'.1)
        rw [abs_of_nonpos (sub_nonpos.mpr hm)] at hd
        linarith)
      (fun b hb c hc hbc => hsep b (Finset.mem_of_mem_erase hb)
        c (Finset.mem_of_mem_erase hc) hbc)
    simpa using! hh
  rw [← Finset.add_sum_erase _ _ ha]
  have hfa0 : 0 < f a := by linarith
  have hfa1 : 0 < f a - 1 := by linarith
  have hkey : (1 / f a ^ 2 + 1 / f a) * (f a - 1) = (f a ^ 2 - 1) / f a ^ 2 := by
    field_simp
    ring
  have hlt : 1 / f a ^ 2 + 1 / f a < 1 / (f a - 1) := by
    apply (lt_div_iff₀ hfa1).mpr
    rw [hkey]
    have hsq : 0 < f a ^ 2 := sq_pos_of_pos hfa0
    rw [div_lt_one hsq]
    nlinarith
  have hlast : 1 / (f a - 1) < 1 / (k - 1) :=
    one_div_lt_one_div_of_lt hk1 (by linarith)
  calc
    1 / f a ^ 2 + ∑ b ∈ s.erase a, 1 / f b ^ 2 ≤
        1 / f a ^ 2 + 1 / f a := by linarith
    _ < 1 / (f a - 1) := hlt
    _ < 1 / (k - 1) := hlast

/-- For positive grid size `M` and `k > 1`, the BHMT phase window of radius `k / M` has mass
strictly greater than `1 - 1 / (2 * (k - 1))`. -/
theorem bhmt11WindowMass_strict (M : ℕ) (ω : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k) :
    1 - 1 / (2 * (k - 1)) < bhmt11WindowMass M ω (k / (M : ℝ)) := by
  classical
  have hm : (0 : ℝ) < M := by positivity
  let f := fun x : Fin M => (M : ℝ) * bhmt11CircleDist (x.val / (M : ℝ)) ω
  let g := fun x : Fin M => (bhmt_phase_estimation_theorem11_lift M ω x : ℝ) - (M : ℝ) * ω
  let s := Finset.univ.filter (fun x : Fin M => k < f x)
  have hf (x : Fin M) : f x = |g x| := bhmt_phase_estimation_theorem11_scaled_distance M ω hM x
  have hpoint (x : Fin M) (hx : x ∈ s) :
      bhmt11OutcomeMass M ω x ≤ (1 / 4 : ℝ) * (1 / f x ^ 2) := by
    have hxk : k < f x := (Finset.mem_filter.mp hx).2
    have hd : 0 < bhmt11CircleDist (x.val / (M : ℝ)) ω := by
      dsimp [f] at hxk
      nlinarith
    have h := bhmt_phase_estimation_theorem11_mass_bound M ω hM x
      (by rw [bhmt_phase_estimation_theorem11_distance_symm]; exact hd)
    rw [bhmt_phase_estimation_theorem11_distance_symm ω (x.val / (M : ℝ))] at h
    convert! h using 1
    dsimp [f]
    field_simp
    ring
  have hb (a : Finset (Fin M)) (has : a ⊆ s)
      (hsep : ∀ x ∈ a, ∀ y ∈ a, x ≠ y → 1 ≤ |f x - f y|) :
      ∑ x ∈ a, bhmt11OutcomeMass M ω x < (1 / 4 : ℝ) * (1 / (k - 1)) := by
    calc
      _ ≤ ∑ x ∈ a, (1 / 4 : ℝ) * (1 / f x ^ 2) :=
        Finset.sum_le_sum (fun x hx => hpoint x (has hx))
      _ = (1 / 4 : ℝ) * ∑ x ∈ a, 1 / f x ^ 2 := (Finset.mul_sum ..).symm
      _ < _ := mul_lt_mul_of_pos_left
        (strictSpacedTail a f k hk
          (fun x hx => (Finset.mem_filter.mp (has hx)).2) hsep) (by norm_num)
  have hp : ∑ x ∈ s.filter (fun x => 0 ≤ g x), bhmt11OutcomeMass M ω x <
      (1 / 4 : ℝ) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    rw [hf, hf, abs_of_nonneg hx0, abs_of_nonneg hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M ω x y hxy using 1
    congr 1
    dsimp [g]
    ring
  have hn : ∑ x ∈ s.filter (fun x => ¬ 0 ≤ g x), bhmt11OutcomeMass M ω x <
      (1 / 4 : ℝ) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (not_le.mp (Finset.mem_filter.mp hx).2).le
    have hy0 := (not_le.mp (Finset.mem_filter.mp hy).2).le
    rw [hf, hf, abs_of_nonpos hx0, abs_of_nonpos hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M ω y x (Ne.symm hxy) using 1
    congr 1
    dsimp [g]
    ring
  have ht : ∑ x ∈ s, bhmt11OutcomeMass M ω x < 1 / (2 * (k - 1)) := by
    have he := Finset.sum_filter_add_sum_filter_not s (fun x => 0 ≤ g x)
      (fun x => bhmt11OutcomeMass M ω x)
    have hr : (1 / 4 : ℝ) * (1 / (k - 1)) + (1 / 4 : ℝ) * (1 / (k - 1)) =
        1 / (2 * (k - 1)) := by field_simp; ring
    linarith
  have htotal : bhmt11WindowMass M ω (k / (M : ℝ)) +
      ∑ x ∈ s, bhmt11OutcomeMass M ω x = 1 := by
    rw [← bhmt_phase_estimation_theorem11_normalization M ω hM]
    unfold bhmt11WindowMass
    dsimp [s]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have hc : k < f x ↔ ¬ bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ k / M := by
      rw [not_le, div_lt_iff₀ hm]
      dsimp [f]
      rw [mul_comm]
    simp only [hc]
    by_cases h : bhmt11CircleDist (x.val / (M : ℝ)) ω ≤ k / M
    · simp [h]
    · simp [h]
  linarith

/-- For positive `M` and `k > 1`, the QPE kernel mass within circular phase distance `k / M` of
`φ` is strictly greater than `1 - 1 / (2 * (k - 1))`. -/
theorem qpeReadoutWindow_strict (M : ℕ) (φ : ℝ) (hM : 0 < M) (k : ℝ) (hk : 1 < k) :
    1 - 1 / (2 * (k - 1)) <
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ k / (M : ℝ)),
        ‖qpeKernel M φ z‖ ^ 2 := by
  rw [bhmt_k2_window_mass_bridge M φ (k / (M : ℝ)) hM]
  exact bhmt11WindowMass_strict M φ hM k hk

/-- For positive `M` and `k ≥ 2`, the QPE kernel assigns mass strictly greater than `1 - 1 / (2
* (k - 1))` to the amplitude error window `2πk√(a(1-a))/M + k²π²/M²`, where `a = sin²(πφ)`. -/
theorem aeErrorWindow_strict (M : ℕ) (hM : 0 < M) (φ : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    let a := Real.sin (Real.pi * φ) ^ 2
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) + (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      ‖qpeKernel M φ z‖ ^ 2 > 1 - 1 / (2 * ((k : ℝ) - 1)) := by
  have hk' : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hw := qpeReadoutWindow_strict M φ hM (k : ℝ) hk'
  (try dsimp only)
  refine lt_of_lt_of_le hw ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact bhmt_k2_estimate_error M hM φ z k hz
  · intro z _ _
    exact sq_nonneg _

/-- For a unitary preparation, `M ≥ 2`, and `k ≥ 2`, the prepared amplitude-estimation law
places mass strictly greater than `1 - 1 / (2 * (k - 1))` in the BHMT amplitude error window
[BrassardEtAl2002]. -/
theorem preparedAeWindow_strict (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ) (k : ℕ) (hk : 2 ≤ k) :
    let a := MeasureProb (preparedAAState A j) S
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |aeEstimate M z - a| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt (a*(1-a))/(M : ℝ) + (k : ℝ)^2*Real.pi^2/(M : ℝ)^2),
      (aeLaw M A j S hA hM).prob z > 1 - 1 / (2 * ((k : ℝ) - 1)) := by
  let a := MeasureProb (preparedAAState A j) S
  have hgeo := prepared_aa_good_bad_geometry A j S hA
  have ha0 : 0 ≤ a := hgeo.2.2.2.2.1
  have ha1 : a ≤ 1 := hgeo.2.2.2.2.2
  by_cases hzero : a = 0
  · have hzero' : MeasureProb (preparedAAState A j) S = 0 := hzero
    simp_rw [aeLaw_zero_mass M hM A j S hA hzero]
    have h := aeErrorWindow_strict M (by omega) 0 k hk
    simpa [hzero'] using! h
  by_cases hone : a = 1
  · have hone' : MeasureProb (preparedAAState A j) S = 1 := hone
    simp_rw [aeLaw_one_mass M hM A j S hA hone]
    have h := aeErrorWindow_strict M (by omega) (1/2) k hk
    have hsin : (Real.sin (Real.pi*(1/2)))^2=(1:ℝ) := by
      rw [mul_one_div, Real.sin_pi_div_two]
      norm_num
    simpa only [hone', hsin] using! h
  have ha0' : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
  have ha1' : a < 1 := lt_of_le_of_ne ha1 hone
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0')
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using! Real.sqrt_lt_sqrt ha0 ha1'
  have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hroot1
  have hθa : a=(Real.sin θ)^2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha0).symm
  have hp : (Real.sin (Real.pi*(θ/Real.pi)))^2=a := by
    rw [show Real.pi*(θ/Real.pi)=θ by field_simp]
    exact hθa.symm
  have hn : (Real.sin (Real.pi*(-θ/Real.pi)))^2=a := by
    rw [show Real.pi*(-θ/Real.pi)=-θ by field_simp, Real.sin_neg, neg_sq]
    exact hθa.symm
  have hlo := aeErrorWindow_strict M (by omega) (θ/Real.pi) k hk
  have hhi := aeErrorWindow_strict M (by omega) (-θ/Real.pi) k hk
  (try dsimp only at hlo hhi)
  rw [hp] at hlo
  rw [hn] at hhi
  simp_rw [prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 hθa]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

/-- For `N > 0`, `M ≥ 2`, and `k ≥ 2`, the Fourier-prepared counting estimate lies within
`2πk√(t(N-t))/M + π²k²N/M²` of `t = S.card` with probability strictly greater than `1 - 1 /
(2 * (k - 1))` [BrassardEtAl2002]. -/
theorem countingWindow_strict (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N)
    (hM : 2 ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
            Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
      (aeLaw M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S (qftMatrix_unitary hN) hM).prob z >
        1 - 1 / (2 * ((k : ℝ) - 1)) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsuccess := preparedAeWindow_strict M (QFTMatrix N) (⟨0,hN⟩ : Fin N) S hM
    (qftMatrix_unitary hN) k hk
  rw [prepared_qft_mark_mass N hN S] at hsuccess
  have hsqrt : (N : ℝ)*Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
      Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card)) := by
    have he : (N : ℝ)^2*((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))) =
        (S.card : ℝ)*((N : ℝ)-S.card) := by field_simp [hn.ne']
    have h := Real.sqrt_mul (sq_nonneg (N : ℝ))
      ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))
    rw [he, Real.sqrt_sq_eq_abs, abs_of_pos hn] at h
    exact h.symm
  refine lt_of_lt_of_le hsuccess ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have h := mul_le_mul_of_nonneg_left hz hn.le
    have habs : |(N : ℝ)*aeEstimate M z-(S.card : ℝ)| =
        (N : ℝ)*|aeEstimate M z-(S.card : ℝ)/(N : ℝ)| := by
      have he : (N : ℝ)*(aeEstimate M z-(S.card : ℝ)/(N : ℝ)) =
          (N : ℝ)*aeEstimate M z-(S.card : ℝ) := by field_simp [hn.ne']
      rw [← he, abs_mul, abs_of_pos hn]
    have he : (N : ℝ)*(2*Real.pi*(k : ℝ)*
        Real.sqrt ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ)))/(M : ℝ)+
          (k : ℝ)^2*Real.pi^2/(M : ℝ)^2) =
        2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)+
          Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2 := by
      calc
        _ = 2*Real.pi*(k : ℝ)*((N : ℝ)*Real.sqrt
            ((S.card : ℝ)/(N : ℝ)*(1-(S.card : ℝ)/(N : ℝ))))/(M : ℝ)+
              Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2 := by ring
        _ = _ := by rw [hsqrt]
    rw [← habs, he] at h
    exact h
  · intro z _ _
    exact (aeLaw M (QFTMatrix N) ⟨0,hN⟩ S (qftMatrix_unitary hN) hM).nonneg z
end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
