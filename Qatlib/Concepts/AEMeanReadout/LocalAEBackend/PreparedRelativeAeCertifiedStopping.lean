/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutRefined
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw
open Qatlib
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped BigOperators Classical
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]

theorem relativeAe_qpe_chord (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * t) - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : (2 * Real.pi * Complex.I * t : ℂ) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * t) / 2 = Real.pi * t by ring, Real.norm_eq_abs, abs_mul]
  norm_num

theorem qpeKernel_norm_le (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M)
    (hd : 0 < phaseDistance φ (z.val / (M : ℝ))) :
    ‖qpeKernel M φ z‖ ≤ |Real.sin (Real.pi * ((M : ℝ) * φ))| /
      (2 * (M : ℝ) * phaseDistance φ (z.val / (M : ℝ))) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hg := congrArg norm (qpeKernel_geometric_identity M φ z hM)
  push_cast at hg
  simp only [norm_mul, Complex.norm_natCast] at hg
  have hden : 4 * phaseDistance φ (z.val / (M : ℝ)) ≤
      ‖Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ) / (M : ℝ))) - 1‖ := by
    have h := phase_chord_lower_bound (φ - (z.val : ℝ) / (M : ℝ))
    push_cast at h
    simpa only [phaseDistance, sub_zero] using! h
  have hc := relativeAe_qpe_chord ((M : ℝ) * φ)
  push_cast at hc
  rw [hc] at hg
  have hmain : (M : ℝ) * ‖qpeKernel M φ z‖ *
      (4 * phaseDistance φ (z.val / (M : ℝ))) ≤
      2 * |Real.sin (Real.pi * ((M : ℝ) * φ))| := by
    calc
      _ ≤ (M : ℝ) * ‖qpeKernel M φ z‖ *
          ‖Complex.exp (2 * Real.pi * Complex.I * (φ - (z.val : ℝ) / (M : ℝ))) - 1‖ :=
        mul_le_mul_of_nonneg_left hden
          (mul_nonneg hMr.le (norm_nonneg (qpeKernel M φ z)))
      _ = _ := hg
  apply (le_div_iff₀ (by positivity :
    0 < 2 * (M : ℝ) * phaseDistance φ (z.val / (M : ℝ)))).mpr
  nlinarith [hmain]

theorem qpeKernel_norm_sq_le (M : ℕ) (hM : 0 < M) (φ : ℝ) (z : Fin M)
    (hd : 0 < phaseDistance φ (z.val / (M : ℝ))) :
    ‖qpeKernel M φ z‖ ^ 2 ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 /
      (2 * (M : ℝ) * phaseDistance φ (z.val / (M : ℝ))) ^ 2 := by
  have h := qpeKernel_norm_le M hM φ z hd
  have hs := pow_le_pow_left₀ (norm_nonneg (qpeKernel M φ z)) h 2
  simpa only [div_pow, sq_abs] using! hs

theorem qpeKernel_phase_tail_le (M : ℕ) (hM : 0 < M) (φ k : ℝ) (hk : 1 < k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      k < (M : ℝ) * phaseDistance φ (z.val / (M : ℝ))), ‖qpeKernel M φ z‖ ^ 2
      ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / (2 * (k - 1)) := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let f := fun x : Fin M => (M : ℝ) * phaseDistance φ (x.val / (M : ℝ))
  let g := fun x : Fin M => (bhmt_phase_estimation_theorem11_lift M φ x : ℝ) - (M : ℝ) * φ
  let s := Finset.univ.filter (fun x : Fin M => k < f x)
  have hf (x : Fin M) : f x = |g x| := by
    dsimp [f, g]
    rw [bhmt_k2_distance_bridge]
    exact bhmt_phase_estimation_theorem11_scaled_distance M φ hM x
  have hpoint (x : Fin M) (hx : x ∈ s) :
      ‖qpeKernel M φ x‖ ^ 2 ≤
        (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / f x ^ 2) := by
    have hxk : k < f x := (Finset.mem_filter.mp hx).2
    have hfx : 0 < f x := by linarith
    have hd : 0 < phaseDistance φ (x.val / (M : ℝ)) := by
      dsimp [f] at hfx
      nlinarith
    calc
      _ ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / (2 * f x) ^ 2 := by
        simpa only [f, mul_assoc] using! qpeKernel_norm_sq_le M hM φ x hd
      _ = _ := by field_simp; ring
  have hb (a : Finset (Fin M)) (has : a ⊆ s)
      (hsep : ∀ x ∈ a, ∀ y ∈ a, x ≠ y → 1 ≤ |f x - f y|) :
      ∑ x ∈ a, ‖qpeKernel M φ x‖ ^ 2 ≤
        (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / (k - 1)) := by
    calc
      _ ≤ ∑ x ∈ a, (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / f x ^ 2) :=
        Finset.sum_le_sum (fun x hx => hpoint x (has hx))
      _ = (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * ∑ x ∈ a, 1 / f x ^ 2 :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (bhmt_phase_estimation_theorem11_spaced_tail a f k hk
          (fun x hx => ((Finset.mem_filter.mp (has hx)).2).le) hsep) (by positivity)
  have hp : ∑ x ∈ s.filter (fun x => 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2 ≤
      (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    rw [hf, hf, abs_of_nonneg hx0, abs_of_nonneg hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M φ x y hxy using 1
    congr 1
    dsimp [g]
    ring
  have hn : ∑ x ∈ s.filter (fun x => ¬ 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2 ≤
      (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / (k - 1)) := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (not_le.mp (Finset.mem_filter.mp hx).2).le
    have hy0 := (not_le.mp (Finset.mem_filter.mp hy).2).le
    rw [hf, hf, abs_of_nonpos hx0, abs_of_nonpos hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M φ y x (Ne.symm hxy) using 1
    congr 1
    dsimp [g]
    ring
  have he := Finset.sum_filter_add_sum_filter_not s (fun x => 0 ≤ g x)
    (fun x => ‖qpeKernel M φ x‖ ^ 2)
  change ∑ x ∈ s, ‖qpeKernel M φ x‖ ^ 2 ≤ _
  calc
    _ ≤ (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / (k - 1)) +
        (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / (k - 1)) := by
      linarith
    _ = _ := by
      field_simp [ne_of_gt (sub_pos.mpr hk)]
      ring

theorem qpeKernel_phase_one_tail_le (M : ℕ) (hM : 0 < M) (φ : ℝ) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      1 < (M : ℝ) * phaseDistance φ (z.val / (M : ℝ))), ‖qpeKernel M φ z‖ ^ 2
      ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let f := fun x : Fin M => (M : ℝ) * phaseDistance φ (x.val / (M : ℝ))
  let g := fun x : Fin M => (bhmt_phase_estimation_theorem11_lift M φ x : ℝ) - (M : ℝ) * φ
  let s := Finset.univ.filter (fun x : Fin M => 1 < f x)
  have hf (x : Fin M) : f x = |g x| := by
    dsimp [f, g]
    rw [bhmt_k2_distance_bridge]
    exact bhmt_phase_estimation_theorem11_scaled_distance M φ hM x
  have hpoint (x : Fin M) (hx : x ∈ s) :
      ‖qpeKernel M φ x‖ ^ 2 ≤
        (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / f x ^ 2) := by
    have hxk : 1 < f x := (Finset.mem_filter.mp hx).2
    have hfx : 0 < f x := by linarith
    have hd : 0 < phaseDistance φ (x.val / (M : ℝ)) := by
      dsimp [f] at hfx
      nlinarith
    calc
      _ ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / (2 * f x) ^ 2 := by
        simpa only [f, mul_assoc] using! qpeKernel_norm_sq_le M hM φ x hd
      _ = _ := by field_simp; ring
  have hb (a : Finset (Fin M)) (has : a ⊆ s)
      (hsep : ∀ x ∈ a, ∀ y ∈ a, x ≠ y → 1 ≤ |f x - f y|) :
      ∑ x ∈ a, ‖qpeKernel M φ x‖ ^ 2 ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 2 := by
    rcases a.eq_empty_or_nonempty with rfl | ha
    · simp only [Finset.sum_empty]
      positivity
    obtain ⟨x, hx, hmin⟩ := a.exists_min_image f ha
    have hfx : 1 < f x := (Finset.mem_filter.mp (has hx)).2
    have hfrac : 1 / f x ^ 2 ≤ 1 := by
      apply (div_le_one (by positivity : 0 < f x ^ 2)).mpr
      nlinarith
    have hxbound : ‖qpeKernel M φ x‖ ^ 2 ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4 := by
      calc
        _ ≤ (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * (1 / f x ^ 2) := hpoint x (has hx)
        _ ≤ (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * 1 :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = _ := mul_one _
    have herase : (∑ y ∈ a.erase x, ‖qpeKernel M φ y‖ ^ 2) ≤
        Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4 := by
      calc
        _ ≤ ∑ y ∈ a.erase x, (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) *
            (1 / f y ^ 2) := Finset.sum_le_sum (fun y hy => hpoint y (has (Finset.mem_of_mem_erase hy)))
        _ = (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * ∑ y ∈ a.erase x, 1 / f y ^ 2 :=
          (Finset.mul_sum ..).symm
        _ ≤ (Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have ht := bhmt_phase_estimation_theorem11_spaced_tail (a.erase x) f 2 (by norm_num)
            (fun y hy => by
              have hy' := Finset.mem_erase.mp hy
              have hm := hmin y hy'.2
              have hd := hsep x hx y hy'.2 (Ne.symm hy'.1)
              rw [abs_of_nonpos (sub_nonpos.mpr hm)] at hd
              linarith)
            (fun y hy z hz hyz =>
              hsep y (Finset.mem_of_mem_erase hy) z (Finset.mem_of_mem_erase hz) hyz)
          norm_num at ht
          simpa only [one_div] using! ht
        _ = _ := mul_one _
    calc
      _ = ‖qpeKernel M φ x‖ ^ 2 + ∑ y ∈ a.erase x, ‖qpeKernel M φ y‖ ^ 2 :=
        (Finset.add_sum_erase _ _ hx).symm
      _ ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4 +
          Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 4 := add_le_add hxbound herase
      _ = _ := by ring
  have hp : ∑ x ∈ s.filter (fun x => 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2 ≤
      Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 2 := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (Finset.mem_filter.mp hx).2
    have hy0 := (Finset.mem_filter.mp hy).2
    rw [hf, hf, abs_of_nonneg hx0, abs_of_nonneg hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M φ x y hxy using 1
    congr 1
    dsimp [g]
    ring
  have hn : ∑ x ∈ s.filter (fun x => ¬ 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2 ≤
      Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 2 := by
    apply hb _ (Finset.filter_subset _ _)
    intro x hx y hy hxy
    have hx0 := (not_le.mp (Finset.mem_filter.mp hx).2).le
    have hy0 := (not_le.mp (Finset.mem_filter.mp hy).2).le
    rw [hf, hf, abs_of_nonpos hx0, abs_of_nonpos hy0]
    convert! bhmt_phase_estimation_theorem11_lift_spacing M φ y x (Ne.symm hxy) using 1
    congr 1
    dsimp [g]
    ring
  have he := Finset.sum_filter_add_sum_filter_not s (fun x => 0 ≤ g x)
    (fun x => ‖qpeKernel M φ x‖ ^ 2)
  change ∑ x ∈ s, ‖qpeKernel M φ x‖ ^ 2 ≤ _
  calc
    _ = (∑ x ∈ s.filter (fun x => 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2) +
        (∑ x ∈ s.filter (fun x => ¬ 0 ≤ g x), ‖qpeKernel M φ x‖ ^ 2) := he.symm
    _ ≤ Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 2 +
        Real.sin (Real.pi * ((M : ℝ) * φ)) ^ 2 / 2 := add_le_add hp hn
    _ = _ := by ring

theorem preparedAe_two_phase_phase_tail_le (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2) (k : ℝ) (hk : 1 < k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      k < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      k < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
      (aeLaw M A j S hA hM).prob z
      ≤ Real.sin ((M : ℝ) * θ) ^ 2 / (2 * (k - 1)) := by
  classical
  let s := Finset.univ.filter (fun z : Fin M =>
    k < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
    k < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)))
  have hlo := qpeKernel_phase_tail_le M (by omega) (θ / Real.pi) k hk
  have hhi := qpeKernel_phase_tail_le M (by omega) (-θ / Real.pi) k hk
  have hpsin : Real.sin (Real.pi * ((M : ℝ) * (θ / Real.pi))) = Real.sin ((M : ℝ) * θ) := by
    congr 1
    field_simp
  have hnsin : Real.sin (Real.pi * ((M : ℝ) * (-θ / Real.pi))) ^ 2 =
      Real.sin ((M : ℝ) * θ) ^ 2 := by
    rw [show Real.pi * ((M : ℝ) * (-θ / Real.pi)) = -((M : ℝ) * θ) by
      field_simp, Real.sin_neg, neg_sq]
  rw [hpsin] at hlo
  rw [hnsin] at hhi
  have hplus : (∑ z ∈ s, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        k < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ))),
        ‖qpeKernel M (θ / Real.pi) z‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.1⟩
    · intro z _ _
      positivity
  have hminus : (∑ z ∈ s, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2) ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        k < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
        ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2.2⟩
    · intro z _ _
      positivity
  change ∑ z ∈ s, (aeLaw M A j S hA hM).prob z ≤ _
  calc
    _ = ∑ z ∈ s, (‖qpeKernel M (θ / Real.pi) z‖ ^ 2 +
        ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2) / 2 :=
      Finset.sum_congr rfl fun z _ =>
        prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 ha z
    _ = ((∑ z ∈ s, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2) +
        (∑ z ∈ s, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

theorem preparedAe_two_phase_phase_tail_le_of_sq (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2) (k : ℝ) (hk : 1 < k) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      k < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      k < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
      (aeLaw M A j S hA hM).prob z
      ≤ (Real.pi ^ 2 * (M : ℝ) ^ 2 * Real.sin θ ^ 2) / (8 * (k - 1)) := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hj := Real.mul_abs_le_abs_sin (x := θ) (by
    rw [abs_of_pos hθ0]
    exact hθ1.le)
  rw [abs_of_pos hθ0, abs_of_pos hsin] at hj
  have hj' : θ ≤ (Real.pi / 2) * Real.sin θ := by
    have hdiv := (div_le_iff₀ Real.pi_pos).mp (show 2 * θ / Real.pi ≤ Real.sin θ by
      convert! hj using 1
      ring)
    nlinarith
  have hθsq : θ ^ 2 ≤ ((Real.pi / 2) * Real.sin θ) ^ 2 :=
    pow_le_pow_left₀ hθ0.le hj' 2
  have hnum : Real.sin ((M : ℝ) * θ) ^ 2 ≤
      (Real.pi ^ 2 / 4) * (M : ℝ) ^ 2 * Real.sin θ ^ 2 := by
    calc
      _ ≤ ((M : ℝ) * θ) ^ 2 := Real.sin_sq_le_sq
      _ = (M : ℝ) ^ 2 * θ ^ 2 := by ring
      _ ≤ (M : ℝ) ^ 2 * ((Real.pi / 2) * Real.sin θ) ^ 2 :=
        mul_le_mul_of_nonneg_left hθsq (sq_nonneg (M : ℝ))
      _ = _ := by ring
  have hden : 0 < 2 * (k - 1) := by linarith
  calc
    _ ≤ Real.sin ((M : ℝ) * θ) ^ 2 / (2 * (k - 1)) :=
      preparedAe_two_phase_phase_tail_le M hM A j S hA θ hθ0 hθ1 ha k hk
    _ ≤ ((Real.pi ^ 2 / 4) * (M : ℝ) ^ 2 * Real.sin θ ^ 2) / (2 * (k - 1)) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = _ := by
      field_simp [ne_of_gt (sub_pos.mpr hk)]
      ring

theorem preparedAe_two_phase_event_le_of_subset (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2)
    (E F G : Fin M → Prop) [DecidablePred E] [DecidablePred F] [DecidablePred G]
    (hEF : ∀ z, E z → F z) (hEG : ∀ z, E z → G z) (C : ℝ)
    (hlo : (∑ z ∈ Finset.univ.filter F, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2) ≤ C)
    (hhi : (∑ z ∈ Finset.univ.filter G, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2) ≤ C) :
    ∑ z ∈ Finset.univ.filter E, (aeLaw M A j S hA hM).prob z ≤ C := by
  classical
  have hplus : (∑ z ∈ Finset.univ.filter E, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2) ≤
      ∑ z ∈ Finset.univ.filter F, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEF z (Finset.mem_filter.mp hz).2⟩
    · intro z _ _
      positivity
  have hminus : (∑ z ∈ Finset.univ.filter E, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2) ≤
      ∑ z ∈ Finset.univ.filter G, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEG z (Finset.mem_filter.mp hz).2⟩
    · intro z _ _
      positivity
  calc
    _ = ∑ z ∈ Finset.univ.filter E, (‖qpeKernel M (θ / Real.pi) z‖ ^ 2 +
        ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2) / 2 :=
      Finset.sum_congr rfl fun z _ =>
        prepared_ae_two_phase_distribution M hM A j S hA θ hθ0 hθ1 ha z
    _ = ((∑ z ∈ Finset.univ.filter E, ‖qpeKernel M (θ / Real.pi) z‖ ^ 2) +
        (∑ z ∈ Finset.univ.filter E, ‖qpeKernel M (-θ / Real.pi) z‖ ^ 2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ (C + C) / 2 := by linarith
    _ = C := by ring

theorem preparedAe_two_phase_one_tail_le (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
      (aeLaw M A j S hA hM).prob z ≤ Real.sin ((M : ℝ) * θ) ^ 2 := by
  have hlo := qpeKernel_phase_one_tail_le M (by omega) (θ / Real.pi)
  have hhi := qpeKernel_phase_one_tail_le M (by omega) (-θ / Real.pi)
  have hpsin : Real.sin (Real.pi * ((M : ℝ) * (θ / Real.pi))) = Real.sin ((M : ℝ) * θ) := by
    congr 1
    field_simp
  have hnsin : Real.sin (Real.pi * ((M : ℝ) * (-θ / Real.pi))) ^ 2 =
      Real.sin ((M : ℝ) * θ) ^ 2 := by
    rw [show Real.pi * ((M : ℝ) * (-θ / Real.pi)) = -((M : ℝ) * θ) by
      field_simp, Real.sin_neg, neg_sq]
  rw [hpsin] at hlo
  rw [hnsin] at hhi
  exact preparedAe_two_phase_event_le_of_subset M hM A j S hA θ hθ0 hθ1 ha
    (fun z => 1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)))
    (fun z => 1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)))
    (fun z => 1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)))
    (fun _ h => h.1) (fun _ h => h.2) _ hlo hhi

theorem preparedAe_two_phase_one_tail_le_of_sq (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ha : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
      (aeLaw M A j S hA hM).prob z
      ≤ Real.pi ^ 2 * (M : ℝ) ^ 2 * Real.sin θ ^ 2 / 4 := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hj := Real.mul_abs_le_abs_sin (x := θ) (by
    rw [abs_of_pos hθ0]
    exact hθ1.le)
  rw [abs_of_pos hθ0, abs_of_pos hsin] at hj
  have hj' : θ ≤ (Real.pi / 2) * Real.sin θ := by
    have hdiv := (div_le_iff₀ Real.pi_pos).mp (show 2 * θ / Real.pi ≤ Real.sin θ by
      convert! hj using 1
      ring)
    nlinarith
  have hθsq : θ ^ 2 ≤ ((Real.pi / 2) * Real.sin θ) ^ 2 :=
    pow_le_pow_left₀ hθ0.le hj' 2
  calc
    _ ≤ Real.sin ((M : ℝ) * θ) ^ 2 :=
      preparedAe_two_phase_one_tail_le M hM A j S hA θ hθ0 hθ1 ha
    _ ≤ ((M : ℝ) * θ) ^ 2 := Real.sin_sq_le_sq
    _ = (M : ℝ) ^ 2 * θ ^ 2 := by ring
    _ ≤ (M : ℝ) ^ 2 * ((Real.pi / 2) * Real.sin θ) ^ 2 :=
      mul_le_mul_of_nonneg_left hθsq (sq_nonneg (M : ℝ))
    _ = _ := by ring

theorem preparedAe_one_tail_le (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : MeasureProb (preparedAAState A j) S = a) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
      1 < (M : ℝ) * phaseDistance (Real.arcsin (Real.sqrt a) / Real.pi) (z.val / (M : ℝ)) ∧
      1 < (M : ℝ) * phaseDistance (-Real.arcsin (Real.sqrt a) / Real.pi) (z.val / (M : ℝ))),
      (aeLaw M A j S hA hM).prob z ≤ Real.pi ^ 2 * (M : ℝ) ^ 2 * a / 4 := by
  let θ := Real.arcsin (Real.sqrt a)
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using! Real.sqrt_lt_sqrt ha0.le ha1
  have hθ1 : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hroot1
  have hθa : a = Real.sin θ ^ 2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha0.le).symm
  have hθa' : MeasureProb (preparedAAState A j) S = Real.sin θ ^ 2 := ha.trans hθa
  have hresult := preparedAe_two_phase_one_tail_le_of_sq M hM A j S hA θ hθ0 hθ1 hθa'
  rw [← hθa] at hresult
  simpa only [θ] using! hresult

noncomputable def freshMedianEstimate (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : ℝ :=
  sortedBlockMedian r (fun i => aeEstimate M (ω i))

noncomputable def freshStageLaw (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    FinDist (Fin (2 * r + 1) → Fin (adaptiveGrid k)) :=
  independent (fun _ => adaptiveStageLaw k A j S hA)

@[simp] theorem freshStageLaw_prob (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (ω : Fin (2 * r + 1) → Fin (adaptiveGrid k)) :
    (freshStageLaw k r A j S hA).prob ω = (adaptiveStageLaw k A j S hA).probOf ω := rfl

theorem freshMedianEstimate_mem (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) :
    ∃ i, freshMedianEstimate M r ω = aeEstimate M (ω i) := by
  have hlen : ((insertionSortCounted (List.ofFn (fun i => aeEstimate M (ω i)))).1).length
      = 2 * r + 1 := by
    rw [insertionSortCounted_length, List.length_ofFn]
  have hr : r < ((insertionSortCounted (List.ofFn (fun i => aeEstimate M (ω i)))).1).length := by
    omega
  have hmem : (insertionSortCounted (List.ofFn (fun i => aeEstimate M (ω i)))).1.getD r 0
      ∈ (insertionSortCounted (List.ofFn (fun i => aeEstimate M (ω i)))).1 := by
    rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hmem' : (insertionSortCounted (List.ofFn (fun i => aeEstimate M (ω i)))).1.getD r 0
      ∈ List.ofFn (fun i => aeEstimate M (ω i)) :=
    (List.Perm.mem_iff (insertionSortCounted_perm _)).1 hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem'
  exact ⟨i, hi.symm⟩

noncomputable def freshMedianLabel (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : Fin M :=
  ω (Classical.choose (freshMedianEstimate_mem M r ω))

@[simp] theorem freshMedianLabel_spec (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) :
    freshMedianEstimate M r ω = aeEstimate M (freshMedianLabel M r ω) := by
  exact Classical.choose_spec (freshMedianEstimate_mem M r ω)

noncomputable def freshMedianLower (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : ℝ :=
  certifiedLowerBound M (freshMedianLabel M r ω)

noncomputable def freshMedianUpper (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : ℝ :=
  certifiedUpperBound M (freshMedianLabel M r ω)

def freshMedianReady (eps : ℝ) (M r : ℕ) (ω : Fin (2 * r + 1) → Fin M) : Prop :=
  freshMedianUpper M r ω - freshMedianLower M r ω ≤ eps * freshMedianLower M r ω

theorem freshMedian_relative_band {M r : ℕ} (hM : 0 < M)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ω : Fin (2 * r + 1) → Fin M) (eps : ℝ) (heps : 0 < eps)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |freshMedianEstimate M r ω - MeasureProb (preparedAAState A j) S|
      ≤ nextAeWindow M (MeasureProb (preparedAAState A j) S))
    (hready : freshMedianReady eps M r ω) :
    |freshMedianEstimate M r ω - MeasureProb (preparedAAState A j) S|
      ≤ eps * MeasureProb (preparedAAState A j) S := by
  rw [freshMedianLabel_spec] at hw ⊢
  exact certifiedStop_relative_band hM A j S hA (freshMedianLabel M r ω) eps heps ha1 hw hready

theorem freshMedian_window_failure (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (adaptiveStageLaw k A j S hA).probEvent (fun ω : Fin (2 * r + 1) → Fin (adaptiveGrid k) =>
      nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S) <
        |freshMedianEstimate (adaptiveGrid k) r ω - MeasureProb (preparedAAState A j) S|)
      ≤ (8 / 9 : ℝ) ^ r := by
  let p := adaptiveStageLaw k A j S hA
  let a := MeasureProb (preparedAAState A j) S
  let radius := nextAeWindow (adaptiveGrid k) a
  have hgood := adaptiveStageLaw_failure_le_third k A j S hA
  have hc :=
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
      (fun z => |aeEstimate (adaptiveGrid k) z - a| ≤ radius)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => radius < |aeEstimate (adaptiveGrid k) z - a|)
      ≤ 1 / 3 := by
    change (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
      |aeEstimate (adaptiveGrid k) z - a| ≤ radius), p.prob z) ≥ 2 / 3 at hgood
    change (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
      |aeEstimate (adaptiveGrid k) z - a| ≤ radius), p.prob z) +
        Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => radius < |aeEstimate (adaptiveGrid k) z - a|) = 1 at hc
    linarith
  have hr : 0 ≤ radius := by
    dsimp [radius, nextAeWindow]
    positivity
  exact Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.sorted_median_failure p
      (aeEstimate (adaptiveGrid k)) r a radius hr hb

theorem sorted_median_failure_precise {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (v : X → ℝ) (r : ℕ) (μ ε : ℝ)
    (hε : 0 ≤ ε) (hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass (I := X) p (fun x : X => ε < |v x - μ|) ≤ 1 / 3) :
    p.probEvent (fun ω : Fin (2 * r + 1) → X =>
      ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|)
      ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r := by
  let B := fun x : X => ε < |v x - μ|
  let w := fun x : X => if B x then (2 : ℝ) else 1
  have hw : (∑ x, p.prob x * w x) = 1 + Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p B := by
    have he (x : X) : p.prob x * w x = p.prob x + (if B x then p.prob x else 0) := by
      dsimp [w]
      by_cases hx : B x <;> simp [hx, mul_two]
    simp_rw [he]
    rw [Finset.sum_add_distrib, p.sum_one, ← Finset.sum_filter]
    rfl
  have hmoment : (∑ ω : Fin (2 * r + 1) → X, p.probOf ω * ∏ k, w (ω k))
      ≤ (4 / 3 : ℝ) ^ (2 * r + 1) := by
    rw [p.expect_prod (fun _ x => w x)]
    simp only [hw, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    apply pow_le_pow_left₀
    · exact add_nonneg (by norm_num)
        (Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_nonneg p B)
    · linarith
  have hbound : (2 : ℝ) ^ (r + 1) * p.probEvent (fun ω : Fin (2 * r + 1) → X =>
      ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|) ≤
      ∑ ω : Fin (2 * r + 1) → X, p.probOf ω * ∏ k, w (ω k) := by
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ ω with ε < |sortedBlockMedian r (fun k => v (ω k)) - μ|,
          p.probOf ω * ∏ k, w (ω k) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hh := heterogeneous_sorted_median_majority_witness r (fun k => v (ω k)) μ ε hε
          (Finset.mem_filter.mp hω).2
        have he : (∏ k, w (ω k)) = (2 : ℝ) ^ (Finset.univ.filter (fun k => B (ω k))).card := by
          simp [w, Finset.prod_ite]
        have hp : 0 ≤ p.probOf ω := Finset.prod_nonneg (fun _ _ => p.nonneg _)
        rw [he, mul_comm ((2 : ℝ) ^ (r + 1))]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh) hp
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun ω _ _ => mul_nonneg (Finset.prod_nonneg (fun _ _ => p.nonneg _))
          (Finset.prod_nonneg (fun _ _ => by dsimp [w]; split_ifs <;> norm_num)))
  have he : (4 / 3 : ℝ) ^ (2 * r + 1) / (2 : ℝ) ^ (r + 1)
      = (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r := by
    rw [pow_succ, pow_succ, pow_mul]
    rw [show (4 / 3 : ℝ) ^ 2 = (8 / 9 : ℝ) * 2 from by norm_num, mul_pow]
    field_simp
    ring
  calc
    _ ≤ (4 / 3 : ℝ) ^ (2 * r + 1) / (2 : ℝ) ^ (r + 1) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using! hbound.trans hmoment)
    _ = _ := he

theorem freshMedian_window_failure_precise (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    (adaptiveStageLaw k A j S hA).probEvent (fun ω : Fin (2 * r + 1) → Fin (adaptiveGrid k) =>
      nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S) <
        |freshMedianEstimate (adaptiveGrid k) r ω - MeasureProb (preparedAAState A j) S|)
      ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r := by
  let p := adaptiveStageLaw k A j S hA
  let a := MeasureProb (preparedAAState A j) S
  let radius := nextAeWindow (adaptiveGrid k) a
  have hgood := adaptiveStageLaw_failure_le_third k A j S hA
  have hc :=
      Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass_complement p
      (fun z => |aeEstimate (adaptiveGrid k) z - a| ≤ radius)
  simp only [not_le] at hc
  have hb : Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => radius < |aeEstimate (adaptiveGrid k) z - a|)
      ≤ 1 / 3 := by
    change (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
      |aeEstimate (adaptiveGrid k) z - a| ≤ radius), p.prob z) ≥ 2 / 3 at hgood
    change (∑ z ∈ Finset.univ.filter (fun z : Fin (adaptiveGrid k) =>
      |aeEstimate (adaptiveGrid k) z - a| ≤ radius), p.prob z) +
        Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean.mass p (fun z => radius < |aeEstimate (adaptiveGrid k) z - a|) = 1 at hc
    linarith
  have hr : 0 ≤ radius := by
    dsimp [radius, nextAeWindow]
    positivity
  exact sorted_median_failure_precise p (aeEstimate (adaptiveGrid k)) r a radius hr hb

theorem independent_majority_le {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (B : X → Prop) [DecidablePred B] (r : ℕ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : (∑ x ∈ Finset.univ.filter B, p.prob x) ≤ η) :
    p.probEvent (fun ω : Fin (2 * r + 1) → X =>
      r + 1 ≤ (Finset.univ.filter (fun n => B (ω n))).card)
      ≤ (2 : ℝ) ^ (2 * r + 1) * η ^ (r + 1) := by
  classical
  let fam : Finset (Finset (Fin (2 * r + 1))) := Finset.univ.filter (fun J => r + 1 ≤ J.card)
  have hsub : Finset.univ.filter (fun ω : Fin (2 * r + 1) → X =>
      r + 1 ≤ (Finset.univ.filter (fun n => B (ω n))).card)
      ⊆ Finset.univ.filter (fun ω => ∃ J : Finset (Fin (2 * r + 1)),
        J ∈ fam ∧ ∀ n ∈ J, B (ω n)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨Finset.univ.filter (fun n => B (ω n)),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.2⟩,
      fun n hn => (Finset.mem_filter.mp hn).2⟩
  have hub := fintype_union_bound_mass (p.probOf)
    (fun ω => Finset.prod_nonneg fun n _ => p.nonneg _)
    (A := fun (J : Finset (Fin (2 * r + 1))) ω => J ∈ fam ∧ ∀ n ∈ J, B (ω n))
  have hdrop : (∑ J : Finset (Fin (2 * r + 1)), ∑ ω ∈ Finset.univ.filter
      (fun ω => J ∈ fam ∧ ∀ n ∈ J, B (ω n)), p.probOf ω)
      = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter (fun ω => ∀ n ∈ J, B (ω n)), p.probOf ω := by
    rw [← Finset.sum_subset (Finset.subset_univ fam) (fun J _ hJ =>
      Finset.sum_eq_zero fun ω hω => absurd ((Finset.mem_filter.mp hω).2).1 hJ)]
    exact Finset.sum_congr rfl fun J hJ => Finset.sum_congr
      (Finset.filter_congr fun ω _ => ⟨fun h => h.2, fun h => ⟨hJ, h⟩⟩) fun _ _ => rfl
  have hperJ : ∀ J ∈ fam, (∏ n ∈ J, (∑ x ∈ Finset.univ.filter B, p.prob x)) ≤ η ^ (r + 1) := by
    intro J hJ
    have hJcard := (Finset.mem_filter.mp hJ).2
    refine le_trans (le_trans
      (Finset.prod_le_prod₀ (fun n _ => Finset.sum_nonneg fun _ _ => p.nonneg _)
        (fun n _ => hb)) (le_of_eq (Finset.prod_const η))) ?_
    rw [← Nat.sub_add_cancel hJcard, pow_add]
    exact mul_le_of_le_one_left (pow_nonneg hη0 _) (pow_le_one_of_mem_Icc hη0 hη1 _)
  have hcards : fam.card ≤ 2 ^ (2 * r + 1) := by
    have h1 : (Finset.univ.filter (fun J : Finset (Fin (2 * r + 1)) => r + 1 ≤ J.card)).card
        ≤ (Finset.univ : Finset (Finset (Fin (2 * r + 1)))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h1
    exact h1
  change (∑ ω ∈ Finset.univ.filter (fun ω : Fin (2 * r + 1) → X =>
    r + 1 ≤ (Finset.univ.filter (fun n => B (ω n))).card), p.probOf ω) ≤ _
  calc
    _ ≤ ∑ J : Finset (Fin (2 * r + 1)), ∑ ω ∈ Finset.univ.filter
        (fun ω => J ∈ fam ∧ ∀ n ∈ J, B (ω n)), p.probOf ω :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
        fun ω _ _ => Finset.prod_nonneg fun n _ => p.nonneg _).trans hub
    _ = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter (fun ω => ∀ n ∈ J, B (ω n)), p.probOf ω := hdrop
    _ = ∑ J ∈ fam, ∏ n ∈ J, (∑ x ∈ Finset.univ.filter B, p.prob x) :=
      Finset.sum_congr rfl fun J _ => Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf_subset_product p B J
    _ ≤ ∑ J ∈ fam, η ^ (r + 1) := Finset.sum_le_sum fun J hJ => hperJ J hJ
    _ = (fam.card : ℝ) * η ^ (r + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (2 * r + 1) * η ^ (r + 1) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcards) (pow_nonneg hη0 _)

theorem freshStageLaw_window_failure_small_amplitude (k r : ℕ)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (ha : MeasureProb (preparedAAState A j) S = a)
    (hη : Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4 ≤ 1) :
    eventMass (freshStageLaw k r A j S hA) (fun ω =>
      nextAeWindow (adaptiveGrid k) a <
        |freshMedianEstimate (adaptiveGrid k) r ω - a|)
      ≤ (2 : ℝ) ^ (2 * r + 1) *
        (Real.pi ^ 2 * (adaptiveGrid k : ℝ) ^ 2 * a / 4) ^ (r + 1) := by
  classical
  let M := adaptiveGrid k
  let p := adaptiveStageLaw k A j S hA
  let η := Real.pi ^ 2 * (M : ℝ) ^ 2 * a / 4
  let θ := Real.arcsin (Real.sqrt a)
  let B := fun z : Fin M => nextAeWindow M a < |aeEstimate M z - a|
  have hM0 : 0 < M := by dsimp [M]; exact adaptiveGrid_pos k
  have hM2 : 2 ≤ M := by dsimp [M]; exact adaptiveGrid_two k
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr ha0)
  have hroot1 : Real.sqrt a < 1 := by
    simpa only [Real.sqrt_one] using! Real.sqrt_lt_sqrt ha0.le ha1
  have hθa : a = Real.sin θ ^ 2 := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le]
    exact (Real.sq_sqrt ha0.le).symm
  have hpsin : Real.sin (Real.pi * (θ / Real.pi)) ^ 2 = a := by
    rw [show Real.pi * (θ / Real.pi) = θ by field_simp]
    exact hθa.symm
  have hnsin : Real.sin (Real.pi * (-θ / Real.pi)) ^ 2 = a := by
    rw [show Real.pi * (-θ / Real.pi) = -θ by field_simp, Real.sin_neg, neg_sq]
    exact hθa.symm
  have hbad_phase (z : Fin M) (hz : B z) :
      1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
      1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)) := by
    change nextAeWindow M a < |aeEstimate M z - a| at hz
    constructor
    · by_contra h
      have hd' : (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ≤ 1 :=
        le_of_not_gt h
      have hd : phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ≤ 1 / (M : ℝ) := by
        apply (le_div_iff₀ hMr).mpr
        simpa only [mul_comm] using! hd'
      have hw := bhmt_k2_estimate_error M hM0 (θ / Real.pi) z 1 (by
        simpa only [Nat.cast_one] using! hd)
      (try dsimp only at hw)
      rw [hpsin] at hw
      have hw' : |aeEstimate M z - a| ≤ nextAeWindow M a := by
        simpa only [nextAeWindow, Nat.cast_one, mul_one, one_mul, one_pow] using! hw
      exact (not_le.mpr hz) hw'
    · by_contra h
      have hd' : (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)) ≤ 1 :=
        le_of_not_gt h
      have hd : phaseDistance (-θ / Real.pi) (z.val / (M : ℝ)) ≤ 1 / (M : ℝ) := by
        apply (le_div_iff₀ hMr).mpr
        simpa only [mul_comm] using! hd'
      have hw := bhmt_k2_estimate_error M hM0 (-θ / Real.pi) z 1 (by
        simpa only [Nat.cast_one] using! hd)
      (try dsimp only at hw)
      rw [hnsin] at hw
      have hw' : |aeEstimate M z - a| ≤ nextAeWindow M a := by
        simpa only [nextAeWindow, Nat.cast_one, mul_one, one_mul, one_pow] using! hw
      exact (not_le.mpr hz) hw'
  have hb : (∑ z ∈ Finset.univ.filter B, p.prob z) ≤ η := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
          1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))), p.prob z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro z hz
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad_phase z (Finset.mem_filter.mp hz).2⟩
        · intro z _ _
          exact p.nonneg z
      _ = ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
          1 < (M : ℝ) * phaseDistance (θ / Real.pi) (z.val / (M : ℝ)) ∧
          1 < (M : ℝ) * phaseDistance (-θ / Real.pi) (z.val / (M : ℝ))),
          (aeLaw M A j S hA hM2).prob z := rfl
      _ ≤ _ := preparedAe_one_tail_le M hM2 A j S hA a ha0 ha1 ha
  change p.probEvent (fun ω : Fin (2 * r + 1) → Fin M =>
    nextAeWindow M a < |freshMedianEstimate M r ω - a|) ≤ _
  calc
    _ ≤ p.probEvent (fun ω : Fin (2 * r + 1) → Fin M =>
        r + 1 ≤ (Finset.univ.filter (fun n => B (ω n))).card) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ω hω
        rw [Finset.mem_filter] at hω ⊢
        exact ⟨Finset.mem_univ _, heterogeneous_sorted_median_majority_witness r
          (fun n => aeEstimate M (ω n)) a (nextAeWindow M a)
          (by dsimp [nextAeWindow]; positivity) hω.2⟩
      · intro ω _ _
        exact Finset.prod_nonneg fun n _ => p.nonneg _
    _ ≤ _ := independent_majority_le p B r η (by dsimp [η]; positivity) hη hb

theorem freshStageLaw_window_failure (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    eventMass (freshStageLaw k r A j S hA) (fun ω =>
      nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S) <
        |freshMedianEstimate (adaptiveGrid k) r ω - MeasureProb (preparedAAState A j) S|)
      ≤ (8 / 9 : ℝ) ^ r := by
  exact freshMedian_window_failure k r A j S hA

theorem freshStageLaw_window_failure_precise (k r : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) :
    eventMass (freshStageLaw k r A j S hA) (fun ω =>
      nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S) <
        |freshMedianEstimate (adaptiveGrid k) r ω - MeasureProb (preparedAAState A j) S|)
      ≤ (2 / 3 : ℝ) * (8 / 9 : ℝ) ^ r := by
  exact freshMedian_window_failure_precise k r A j S hA

theorem eventMass_eq_expect {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : X → Prop) [DecidablePred E] :
    eventMass p E = p.expect (fun x => if E x then 1 else 0) := by
  classical
  simp [eventMass, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Finset.sum_filter]

theorem independent_expect_prod {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (g : ∀ i, X i → ℝ) :
    (independent p).expect (fun ω => ∏ i, g i (ω i))
      = ∏ i, (p i).expect (g i) := by
  classical
  have hsplit : (∑ ω : ∀ i, X i,
      (∏ i, (p i).prob (ω i)) * ∏ i, g i (ω i))
      = ∑ ω : ∀ i, X i, ∏ i, ((p i).prob (ω i) * g i (ω i)) := by
    apply Finset.sum_congr rfl
    intro ω _
    rw [← Finset.prod_mul_distrib]
  change (∑ ω : ∀ i, X i, (∏ i, (p i).prob (ω i)) * ∏ i, g i (ω i)) = _
  rw [hsplit]
  simpa only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, Fintype.piFinset_univ] using!
    (Finset.prod_univ_sum
      (t := fun i => (Finset.univ : Finset (X i)))
      (f := fun i x => (p i).prob x * g i x)).symm

theorem independent_event_all {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (E : ∀ i, X i → Prop) [∀ i, DecidablePred (E i)] :
    eventMass (independent p) (fun ω => ∀ i, E i (ω i))
      = ∏ i, eventMass (p i) (E i) := by
  classical
  rw [eventMass_eq_expect]
  have hpoint (ω : ∀ i, X i) :
      (if ∀ i, E i (ω i) then (1 : ℝ) else 0)
        = ∏ i, (if E i (ω i) then 1 else 0) := by
    by_cases h : ∀ i, E i (ω i)
    · simp [h]
    · simp only [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
  have hrewrite : (independent p).expect (fun ω => if ∀ i, E i (ω i) then (1 : ℝ) else 0)
      = (independent p).expect (fun ω => ∏ i, (if E i (ω i) then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro ω _
    change (independent p).prob ω * (if ∀ i, E i (ω i) then (1 : ℝ) else 0) = _
    rw [hpoint ω]
  rw [hrewrite]
  calc
    _ = ∏ i, (p i).expect (fun x => if E i x then (1 : ℝ) else 0) :=
      independent_expect_prod p (fun i x => if E i x then (1 : ℝ) else 0)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (eventMass_eq_expect (p i) (E i)).symm

theorem independent_event_all_finset {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (p : ∀ i, FinDist (X i)) (s : Finset J) (E : ∀ i, X i → Prop)
    [∀ i, DecidablePred (E i)] :
    eventMass (independent p) (fun ω => ∀ i ∈ s, E i (ω i))
      = ∏ i ∈ s, eventMass (p i) (E i) := by
  classical
  rw [eventMass_eq_expect]
  have hpoint (ω : ∀ i, X i) :
      (if ∀ i ∈ s, E i (ω i) then (1 : ℝ) else 0)
        = ∏ i, (if i ∈ s then (if E i (ω i) then 1 else 0) else 1) := by
    by_cases h : ∀ i ∈ s, E i (ω i)
    · rw [if_pos h]
      symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ s
      · simp [hi, h i hi]
      · simp [hi]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi, hE⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hE])).symm
  have hrewrite : (independent p).expect (fun ω => if ∀ i ∈ s, E i (ω i) then (1 : ℝ) else 0)
      = (independent p).expect (fun ω =>
        ∏ i, (if i ∈ s then (if E i (ω i) then 1 else 0) else 1)) := by
    apply Finset.sum_congr rfl
    intro ω _
    change (independent p).prob ω * (if ∀ i ∈ s, E i (ω i) then (1 : ℝ) else 0) = _
    rw [hpoint ω]
  rw [hrewrite]
  calc
    _ = ∏ i, (p i).expect (fun x => if i ∈ s then (if E i x then (1 : ℝ) else 0) else 1) :=
      independent_expect_prod p _
    _ = ∏ i, (if i ∈ s then eventMass (p i) (E i) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp only [if_pos hi]
        exact (eventMass_eq_expect (p i) (E i)).symm
      · simp only [if_neg hi]
        simpa only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect, mul_one] using!
            (p i).sum_one
    _ = _ := by
      clear hpoint hrewrite
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp [ha, Finset.prod_ite]
        convert! Finset.prod_insert (f := fun i : J => eventMass (p i) (E i)) ha using 1
        apply Finset.prod_congr
        · ext x
          simp
        · intro x _
          rfl

theorem eventMass_exists_le_sum {J X : Type*} [Fintype J] [DecidableEq J]
    [Fintype X] [DecidableEq X]
    (p : FinDist X) (E : J → X → Prop) [∀ i, DecidablePred (E i)] :
    eventMass p (fun ω => ∃ i, E i ω) ≤ ∑ i, eventMass p (E i) := by
  classical
  rw [eventMass_eq_expect]
  have hsum : (∑ i, eventMass p (E i))
      = p.expect (fun ω => ∑ i, (if E i ω then (1 : ℝ) else 0)) := by
    simp_rw [eventMass_eq_expect]
    unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
    calc
      (∑ i, ∑ ω, p.prob ω * (if E i ω then (1 : ℝ) else 0))
          = ∑ ω, ∑ i, p.prob ω * (if E i ω then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ ω, p.prob ω * ∑ i, (if E i ω then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.mul_sum]
  rw [hsum]
  unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (p.nonneg ω)
  change (if ∃ i, E i ω then (1 : ℝ) else 0) ≤ ∑ i, (if E i ω then 1 else 0)
  by_cases h : ∃ i, E i ω
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    have hle := Finset.single_le_sum
      (fun j _ => show (0 : ℝ) ≤ (if E j ω then 1 else 0) by positivity)
      (Finset.mem_univ i)
    simpa [hi] using! hle
  · rw [if_neg h]
    positivity

theorem freshMedian_fires_at_fine_stage {k r : ℕ} {ω : Fin (2 * r + 1) → Fin (adaptiveGrid k)}
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (ha0 : 0 < MeasureProb (preparedAAState A j) S)
    (ha1 : MeasureProb (preparedAAState A j) S ≤ 1)
    (hw : |freshMedianEstimate (adaptiveGrid k) r ω - MeasureProb (preparedAAState A j) S|
      ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S))
    (hfine : 32 * Real.pi ≤ eps * (adaptiveGrid k : ℝ)
      * Real.sqrt (MeasureProb (preparedAAState A j) S)) :
    freshMedianReady eps (adaptiveGrid k) r ω := by
  let z := freshMedianLabel (adaptiveGrid k) r ω
  have hz : adaptiveLabel k z.val = z := by
    apply Fin.ext
    simp [adaptiveLabel, Nat.mod_eq_of_lt z.isLt]
  have hw' : |adaptiveEstimate k z.val - MeasureProb (preparedAAState A j) S|
      ≤ nextAeWindow (adaptiveGrid k) (MeasureProb (preparedAAState A j) S) := by
    rw [adaptiveEstimate, recordEstimate, hz]
    simpa only [z, ← freshMedianLabel_spec] using! hw
  have hready := adaptiveFires_at_fine_stage eps heps heps1 A j S hA ha0 ha1 hw' hfine
  unfold freshMedianReady freshMedianUpper freshMedianLower
  simpa only [adaptiveReady, adaptiveUpper, adaptiveLower, hz] using! hready

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
