/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.QuadratureNormalization
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped BigOperators Topology
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.KoopmanFlow.Sampling Qatlib.Papers.KoopmanSim26.SpectralRep

noncomputable section
namespace Qatlib.Papers.KoopmanSim26.SpectralRep

theorem source_rate_sq (κ : ℝ) (hκ : 0 < κ) (h M : ℕ) (hh : 0 < h) (hM : 0 < M) :
    (Real.sqrt (4*κ/Real.pi) * (M:ℝ)^(-(1/2:ℝ)) * (h:ℝ)^(-(1/3:ℝ)))^2 =
      4*cubicCutoff κ h/(Real.pi*(h:ℝ)*(M:ℝ)) := by
  rw [Real.rpow_neg (Nat.cast_nonneg M), ← Real.sqrt_eq_rpow,
    Real.rpow_neg (Nat.cast_nonneg h)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg M), inv_pow]
  unfold cubicCutoff
  have hc := root_cube h
  generalize he : (h:ℝ)^(1/3:ℝ) = r at *
  rw [← hc]
  have hr : r ≠ 0 := by
    rw [← he]
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hm : (M:ℝ) ≠ 0 := by positivity
  field_simp

theorem sampling_bound_from_mass_half {h N M : ℕ} (p : Fin h → FinDist (Fin N))
    (κ : ℝ) (hκ : 0 < κ) (hh : 0 < h) (hM : 0 < M)
    (hz : 1/2 ≤ quadratureMass (cubicCutoff κ h) (uniformRightNodes (cubicCutoff κ h) h)) :
    (recordsLaw p M).expect (l2Error p (normalizedWeight (cubicCutoff κ h)
      (uniformRightNodes (cubicCutoff κ h) h))) ≤
      Real.sqrt (4*κ/Real.pi) * (M:ℝ)^(-(1/2:ℝ)) * (h:ℝ)^(-(1/3:ℝ)) := by
  have hK : 0 < cubicCutoff κ h := mul_pos hκ (Real.rpow_pos_of_pos (by positivity) _)
  have hb := quadrature_expected_l2_bound p (cubicCutoff κ h)
    (uniformRightNodes (cubicCutoff κ h) h) hK hh hM
  apply hb.trans
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, ?_⟩
  rw [source_rate_sq κ hκ h M hh hM]
  calc
    _ = (2*cubicCutoff κ h/(Real.pi*(h:ℝ)*(M:ℝ))) /
        quadratureMass (cubicCutoff κ h) (uniformRightNodes (cubicCutoff κ h) h) := by
      rw [div_div]
    _ ≤ (2*cubicCutoff κ h/(Real.pi*(h:ℝ)*(M:ℝ))) / (1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hz
    _ = _ := by ring

theorem eventually_uniform_sampling_bound (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ h : ℕ in atTop, ∀ (N M : ℕ) (p : Fin h → FinDist (Fin N)), 0 < M →
    (recordsLaw p M).expect (l2Error p (normalizedWeight (cubicCutoff κ h)
      (uniformRightNodes (cubicCutoff κ h) h))) ≤
      Real.sqrt (4*κ/Real.pi) * (M:ℝ)^(-(1/2:ℝ)) * (h:ℝ)^(-(1/3:ℝ)) := by
  filter_upwards [eventually_mass_half κ hκ, eventually_gt_atTop (0:ℕ)] with h hz hh
  intro N M p hM
  exact sampling_bound_from_mass_half p κ hκ hh hM hz

theorem source_sampling_scaling {N : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (p : (h : ℕ) → Fin h → FinDist (Fin N)) : SourceSamplingScaling κ p := by
  unfold SourceSamplingScaling
  apply Asymptotics.IsBigO.of_bound (Real.sqrt (4*κ/Real.pi))
  obtain ⟨H, hH⟩ := eventually_atTop.mp (eventually_uniform_sampling_bound κ hκ)
  apply eventually_atTop.mpr
  refine ⟨(H, 1), ?_⟩
  intro b hb
  have hh := hH b.1 hb.1 N b.2 (p b.1) (lt_of_lt_of_le Nat.zero_lt_one hb.2)
  have hn : 0 ≤ (recordsLaw (p b.1) b.2).expect
      (l2Error (p b.1) (normalizedWeight (cubicCutoff κ b.1)
        (uniformRightNodes (cubicCutoff κ b.1) b.1))) := by
    apply Finset.sum_nonneg
    intro r _
    exact mul_nonneg ((recordsLaw (p b.1) b.2).nonneg r) (norm_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg b.2) _)
      (Real.rpow_nonneg (Nat.cast_nonneg b.1) _)), mul_assoc] using hh

end Qatlib.Papers.KoopmanSim26.SpectralRep
