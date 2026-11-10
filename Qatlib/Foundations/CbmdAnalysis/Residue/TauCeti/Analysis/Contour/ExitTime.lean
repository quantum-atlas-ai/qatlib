/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Order.IntermediateValue
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

section Norm

variable {E : Type*} [Sub E] [Norm E]

def firstExitTimeRight (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sInf {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}

private theorem right_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ + δ) - s‖) :
    (t₀ + δ) ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖} :=
  ⟨⟨by linarith, le_rfl⟩, h_far⟩

private theorem right_set_bddBelow (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t - s‖}, t₀ ≤ t :=
  fun _ ⟨hmem, _⟩ => hmem.1

theorem firstExitTimeRight_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    firstExitTimeRight γ t₀ δ s ε ∈ Icc t₀ (t₀ + δ) :=
  ⟨le_csInf ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩ (right_set_bddBelow γ t₀ δ ε s),
    csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ (right_endpoint_mem hδ hε_le)⟩

theorem firstExitTimeRight_le_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc t₀ (t₀ + δ)) (h_far : ε ≤ ‖γ t₁ - s‖) :
    firstExitTimeRight γ t₀ δ s ε ≤ t₁ :=
  csInf_le ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

def firstExitTimeLeft (γ : ℝ → E) (t₀ δ : ℝ) (s : E) (ε : ℝ) : ℝ :=
  sSup {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}

private theorem left_endpoint_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (t₀ - δ) ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖} :=
  ⟨⟨le_rfl, by linarith⟩, h_far⟩

private theorem left_set_bddAbove (γ : ℝ → E) (t₀ δ ε : ℝ) (s : E) :
    ∀ t ∈ {t ∈ Icc (t₀ - δ) t₀ | ε ≤ ‖γ t - s‖}, t ≤ t₀ :=
  fun _ ⟨hmem, _⟩ => hmem.2

theorem firstExitTimeLeft_mem_Icc {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε ∈ Icc (t₀ - δ) t₀ :=
  ⟨le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ (left_endpoint_mem hδ hε_le),
    csSup_le ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩ (left_set_bddAbove γ t₀ δ ε s)⟩

theorem le_firstExitTimeLeft_of_mem {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (t₀ - δ) t₀) (h_far : ε ≤ ‖γ t₁ - s‖) :
    t₁ ≤ firstExitTimeLeft γ t₀ δ s ε :=
  le_csSup ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩ ⟨ht₁, h_far⟩

end Norm

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

theorem le_norm_at_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csInf_mem
    ⟨t₀ + δ, right_endpoint_mem hδ hε_le⟩
    ⟨t₀, right_set_bddBelow γ t₀ δ ε s⟩).2

theorem lt_firstExitTimeRight {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ < firstExitTimeRight γ t₀ δ s ε := by
  refine lt_of_le_of_ne (firstExitTimeRight_mem_Icc hδ hε_le).1 ?_
  intro h
  have := le_norm_at_firstExitTimeRight hδ hγ_cont hε_le
  simp [← h, h_s] at this
  linarith

theorem norm_at_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (hε_nonneg : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_at_firstExitTimeRight hδ hγ_cont hε_le)
  by_contra! h
  have hτ := firstExitTimeRight_mem_Icc hδ hε_le
  have hcont : ContinuousOn (fun t => ‖γ t - s‖)
      (Icc t₀ (firstExitTimeRight γ t₀ δ s ε)) :=
    ((hγ_cont.mono (Icc_subset_Icc_right hτ.2)).sub continuousOn_const).norm
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Ico hτ.1 hcont
    (by simpa [h_s] using And.intro hε_nonneg h)
  have hle := firstExitTimeRight_le_of_mem ⟨ht.1, ht.2.le.trans hτ.2⟩ hnorm.ge
  exact hle.not_gt ht.2

theorem le_norm_at_firstExitTimeLeft {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ε ≤ ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ :=
  (((hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_Ici).csSup_mem
    ⟨t₀ - δ, left_endpoint_mem hδ hε_le⟩
    ⟨t₀, left_set_bddAbove γ t₀ δ ε s⟩).2

theorem firstExitTimeLeft_lt {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    firstExitTimeLeft γ t₀ δ s ε < t₀ := by
  refine lt_of_le_of_ne (firstExitTimeLeft_mem_Icc hδ hε_le).2 ?_
  intro h
  have := le_norm_at_firstExitTimeLeft hδ hγ_cont hε_le
  simp [h, h_s] at this
  linarith

theorem norm_at_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ ε : ℝ} {s : E}
    (hδ : 0 ≤ δ) (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (hε_nonneg : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  refine le_antisymm ?_ (le_norm_at_firstExitTimeLeft hδ hγ_cont hε_le)
  by_contra! h
  have hτ := firstExitTimeLeft_mem_Icc hδ hε_le
  have hcont : ContinuousOn (fun t => ‖γ t - s‖)
      (Icc (firstExitTimeLeft γ t₀ δ s ε) t₀) :=
    ((hγ_cont.mono (Icc_subset_Icc_left hτ.1)).sub continuousOn_const).norm
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Ioc' hτ.2 hcont
    (by simpa [h_s] using And.intro hε_nonneg h)
  have hle := le_firstExitTimeLeft_of_mem ⟨hτ.1.trans ht.1.le, ht.2⟩ hnorm.ge
  exact hle.not_gt ht.1

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E]

theorem firstExitTimeRight_tendsto {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeRight γ t₀ δ s ε) (𝓝[>] 0) (𝓝[>] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    set t₁ := t₀ + min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Ioc t₀ (t₀ + δ) :=
      ⟨by linarith [lt_min hη_pos hδ], by linarith [min_le_right η δ]⟩
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using h_leave t₁ ht₁_mem, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Icc t₀ (t₀ + δ) := ⟨ht₁_mem.1.le, ht₁_mem.2⟩
    have h_t₀_le : t₀ ≤ firstExitTimeRight γ t₀ δ s ε :=
      le_csInf ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩ (right_set_bddBelow γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ firstExitTimeRight γ t₀ δ s ε - t₀)]
    linarith [firstExitTimeRight_le_of_mem h_t₁_mem_Icc hε_lt.le, min_le_left η δ]
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨by linarith, le_rfl⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo 0 ‖γ (t₀ + δ) - s‖, Ioo_mem_nhdsGT h_far_pos, fun ε hε => ?_⟩
    exact lt_firstExitTimeRight hδ.le hγ_cont h_s hε.1 hε.2.le

theorem firstExitTimeLeft_tendsto {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ - δ) t₀, γ t ≠ s) :
    Tendsto (fun ε => firstExitTimeLeft γ t₀ δ s ε) (𝓝[>] 0) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro η hη_pos
    set t₁ := t₀ - min η δ / 2 with ht₁_def
    have ht₁_mem : t₁ ∈ Ico (t₀ - δ) t₀ :=
      ⟨by linarith [min_le_right η δ], by linarith [lt_min hη_pos hδ]⟩
    refine ⟨‖γ t₁ - s‖, by simpa [norm_pos_iff, sub_ne_zero] using h_leave t₁ ht₁_mem, ?_⟩
    intro ε hε_pos hε_lt
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_lt
    have h_t₁_mem_Icc : t₁ ∈ Icc (t₀ - δ) t₀ := ⟨ht₁_mem.1, ht₁_mem.2.le⟩
    have h_le : firstExitTimeLeft γ t₀ δ s ε ≤ t₀ :=
      csSup_le ⟨t₁, h_t₁_mem_Icc, hε_lt.le⟩ (left_set_bddAbove γ t₀ δ ε s)
    rw [Real.dist_eq, abs_of_nonpos
      (by linarith : firstExitTimeLeft γ t₀ δ s ε - t₀ ≤ 0)]
    linarith [le_firstExitTimeLeft_of_mem h_t₁_mem_Icc hε_lt.le, min_le_left η δ]
  · have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_leave _ ⟨le_rfl, by linarith⟩))
    rw [eventually_iff_exists_mem]
    refine ⟨Ioo 0 ‖γ (t₀ - δ) - s‖, Ioo_mem_nhdsGT h_far_pos, fun ε hε => ?_⟩
    exact firstExitTimeLeft_lt hδ.le hγ_cont h_s hε.1 hε.2.le

theorem eventually_norm_at_firstExitTimeRight_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ)))
    (h_s : γ t₀ = s) (h_leave : γ (t₀ + δ) ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeRight γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ + δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr h_leave)
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeRight_eq hδ hγ_cont h_s hε.1.le hε.2.le

theorem eventually_norm_at_firstExitTimeLeft_eq {γ : ℝ → E} {t₀ δ : ℝ} {s : E} (hδ : 0 ≤ δ)
    (hγ_cont : ContinuousOn γ (Icc (t₀ - δ) t₀))
    (h_s : γ t₀ = s) (h_leave : γ (t₀ - δ) ≠ s) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (firstExitTimeLeft γ t₀ δ s ε) - s‖ = ε := by
  have h_far_pos : (0 : ℝ) < ‖γ (t₀ - δ) - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr h_leave)
  filter_upwards [Ioo_mem_nhdsGT h_far_pos] with ε hε
  exact norm_at_firstExitTimeLeft_eq hδ hγ_cont h_s hε.1.le hε.2.le

end Normed

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
