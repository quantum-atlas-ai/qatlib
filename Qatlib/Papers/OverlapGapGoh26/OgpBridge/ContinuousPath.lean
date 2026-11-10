/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation

namespace Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path

def hilbertCube (N : ℕ) : Set (Fin N → ℝ) := {u | ∀ i, u i ∈ Set.Icc (-1:ℝ) 1}

def cubeOpt {q N : ℕ} (J : Tensor q N) : ℝ := sInf (tensorEnergy J '' hilbertCube N)

theorem cubeOpt_attained {q N : ℕ} (J : Tensor q N) :
    ∃ u ∈ hilbertCube N, tensorEnergy J u=cubeOpt J := by
  have hc : IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N => isCompact_Icc)
  have hn : (hilbertCube N).Nonempty := ⟨fun _ => 0, fun _ => by constructor <;> norm_num⟩
  have hE : Continuous (tensorEnergy J) :=
    continuous_tensorEnergy.comp (continuous_const.prodMk continuous_id)
  obtain ⟨u,hu,hmin⟩ := hc.exists_isMinOn hn hE.continuousOn
  have hb : BddBelow (tensorEnergy J '' hilbertCube N) := by
    refine ⟨tensorEnergy J u, ?_⟩
    rintro _ ⟨v,hv,rfl⟩
    exact hmin hv
  refine ⟨u,hu,le_antisymm ?_ ?_⟩
  · exact le_csInf (Set.image_nonempty.mpr hn) (by rintro _ ⟨v,hv,rfl⟩; exact hmin hv)
  · exact csInf_le hb (Set.mem_image_of_mem _ hu)

def normalizedOverlap {N : ℕ} (u v : EuclideanSpace ℝ (Fin N)) : ℝ :=
  |inner (𝕜:=ℝ) u v|/(‖u‖*‖v‖)

theorem normalizedOverlap_self {N : ℕ} (u : EuclideanSpace ℝ (Fin N)) (hu : u≠0) :
    normalizedOverlap u u=1 := by
  unfold normalizedOverlap
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), pow_two]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr hu) (norm_ne_zero_iff.mpr hu))

def ensembleOGP {q N : ℕ} (A B : Tensor q N) (μ ν₁ ν₂ : ℝ) : Prop :=
  ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ σ ∈ Set.Icc (0:ℝ) 1,
    ∀ (u v : EuclideanSpace ℝ (Fin N)), u.ofLp ∈ hilbertCube N → v.ofLp ∈ hilbertCube N →
      tensorEnergy (interpolate A B τ) u.ofLp ≤ cubeOpt (interpolate A B τ)+μ →
      tensorEnergy (interpolate A B σ) v.ofLp ≤ cubeOpt (interpolate A B σ)+μ →
      normalizedOverlap u v≤ν₁ ∨ ν₂≤normalizedOverlap u v

theorem actual_overlap_gap_crossing {N : ℕ} (V : ℝ → EuclideanSpace ℝ (Fin N))
    (hV : ContinuousOn V (Set.Icc (0:ℝ) 1))
    (hnz : ∀ τ ∈ Set.Icc (0:ℝ) 1, V τ≠0)
    (ν₁ ν₂ : ℝ) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hdec : normalizedOverlap (V 0) (V 1)≤ν₁) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1, ν₁<normalizedOverlap (V 0) (V τ) ∧
      normalizedOverlap (V 0) (V τ)<ν₂ := by
  have hz : V 0≠0 := hnz 0 (by constructor <;> norm_num)
  have hc : ContinuousOn (fun τ => normalizedOverlap (V 0) (V τ)) (Set.Icc (0:ℝ) 1) := by
    apply (continuousOn_const.inner hV).abs.div (continuousOn_const.mul hV.norm)
    intro τ hτ
    exact mul_ne_zero (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr (hnz τ hτ))
  have hs : normalizedOverlap (V 0) (V 0)=1 := normalizedOverlap_self _ hz
  have hm : (ν₁+ν₂)/2 ∈ Set.Icc (normalizedOverlap (V 0) (V 1)) (normalizedOverlap (V 0) (V 0)) := by
    rw [hs]
    constructor <;> linarith
  obtain ⟨τ,hτ,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ)≤1) hc hm
  change normalizedOverlap (V 0) (V τ)=(ν₁+ν₂)/2 at he
  exact ⟨τ,hτ,by rw [he]; constructor <;> linarith⟩

theorem actual_amp_ogp_obstruction {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (μ ν₁ ν₂ : ℝ)
    (hogp : ensembleOGP A B μ ν₁ ν₂) (hgap : ν₁<ν₂) (hhigh : ν₂<1)
    (hnz : ∀ τ ∈ Set.Icc (0:ℝ) 1, outputPath M s T A B seed τ≠0)
    (hdec : normalizedOverlap (outputPath M s T A B seed 0) (outputPath M s T A B seed 1)≤ν₁) :
    ∃ τ ∈ Set.Icc (0:ℝ) 1,
      cubeOpt (interpolate A B τ)+μ <
        tensorEnergy (interpolate A B τ) (outputPath M s T A B seed τ).ofLp := by
  by_contra hn
  push Not at hn
  obtain ⟨τ,hτ,hlo,hhi⟩ := actual_overlap_gap_crossing (outputPath M s T A B seed)
    (continuous_outputPath M s T A B seed).continuousOn hnz ν₁ ν₂ hgap hhigh hdec
  have hz : (0:ℝ)∈Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := hogp 0 hz τ hτ _ _
    (fun i => outputPath_cube M s T A B seed 0 i)
    (fun i => outputPath_cube M s T A B seed τ i) (hn 0 hz) (hn τ hτ)
  rcases hb with hb | hb <;> linarith

theorem decorrelation_to_normalized {N : ℕ} (u v : EuclideanSpace ℝ (Fin N))
    (b δ ν₁ : ℝ) (hb : 0<b) (hν : 0≤ν₁) (hu : b≤‖u‖) (hv : b≤‖v‖)
    (hdec : |inner (𝕜:=ℝ) u v|≤δ*(N:ℝ)) (hscale : δ*(N:ℝ)≤ν₁*b^2) :
    normalizedOverlap u v≤ν₁ := by
  apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le hb hu) (lt_of_lt_of_le hb hv))).2
  exact hdec.trans (hscale.trans (mul_le_mul_of_nonneg_left
    (by nlinarith [mul_le_mul hu hv hb.le (norm_nonneg u)]) hν))

end Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
