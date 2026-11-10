/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped NNReal
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.AffineCenter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_affine_center (H u : E) (hu : ‖u‖=1) :
    ∃ c : ℝ,∀ r : ℝ,‖H+c • u‖≤‖H+r • u‖ := by
  let f : ℝ → ℝ := fun c => ‖H+c • u‖
  have hf : Continuous f := (continuous_const.add (continuous_id.smul continuous_const)).norm
  have hzero : (0:ℝ)∈Set.Icc (-(2*‖H‖)) (2*‖H‖) := by
    constructor <;> nlinarith [norm_nonneg H]
  obtain ⟨c,hc,hm⟩ := isCompact_Icc.exists_isMinOn ⟨0,hzero⟩ hf.continuousOn
  refine ⟨c,fun r => ?_⟩
  by_cases hr : r∈Set.Icc (-(2*‖H‖)) (2*‖H‖)
  · exact hm hr
  · have hlarge : 2*‖H‖ < |r| := lt_of_not_ge (fun h => hr (abs_le.mp h))
    have hm0 : f c≤‖H‖ := by
      have hz : f c ≤ f 0 := hm hzero
      simpa only [f,zero_smul,add_zero] using hz
    have hb : |r|≤f r+‖H‖ := by
      calc
        |r| = ‖r • u‖ := by rw [norm_smul,hu,mul_one,Real.norm_eq_abs]
        _ = ‖(H+r • u)-H‖ := by congr 1;abel
        _ ≤ f r+‖H‖ := norm_sub_le _ _
    exact hm0.trans (by linarith)

theorem affine_inf_nonneg (H u : E) :
    0≤sInf (Set.range (fun c : ℝ => ‖H+c • u‖)) := by
  apply le_csInf (Set.range_nonempty _)
  intro y hy
  obtain ⟨r,rfl⟩ := hy
  exact norm_nonneg _

theorem exists_center_eq_inf (H u : E) (hu : ‖u‖=1) :
    ∃ c : ℝ,‖H+c • u‖=sInf (Set.range (fun r : ℝ => ‖H+r • u‖)) := by
  obtain ⟨c,hc⟩ := exists_affine_center H u hu
  have hb : BddBelow (Set.range (fun r : ℝ => ‖H+r • u‖)) := by
    refine ⟨0,?_⟩
    intro y hy
    obtain ⟨r,rfl⟩ := hy
    exact norm_nonneg _
  refine ⟨c,le_antisymm ?_ (csInf_le hb (Set.mem_range_self c))⟩
  apply le_csInf (Set.range_nonempty _)
  intro y hy
  obtain ⟨r,rfl⟩ := hy
  exact hc r

def optimalRadius (H u : E) : ℝ≥0 :=
  ⟨sInf (Set.range (fun c : ℝ => ‖H+c • u‖)),affine_inf_nonneg H u⟩

def familyRadius {I : Type*} [Fintype I] (H : I → E) (u : E) : ℝ≥0 :=
  Finset.univ.sup (fun i => optimalRadius (H i) u)

theorem exists_uniform_family_centers {I : Type*} [Fintype I]
    (H : I → E) (u : E) (hu : ‖u‖=1) :
    ∃ c : I → ℝ,∀ i,‖H i-c i • u‖≤(familyRadius H u:ℝ) := by
  classical
  let arg (i : I) : ℝ := Classical.choose (exists_center_eq_inf (H i) u hu)
  refine ⟨fun i => -arg i,fun i => ?_⟩
  have he : ‖H i-(-arg i) • u‖=(optimalRadius (H i) u:ℝ) := by
    have hh : H i-(-arg i) • u=H i+arg i • u := by module
    rw [hh]
    exact Classical.choose_spec (exists_center_eq_inf (H i) u hu)
  rw [he]
  have hle : optimalRadius (H i) u≤familyRadius H u := by
    change optimalRadius (H i) u ≤ Finset.univ.sup (fun j => optimalRadius (H j) u)
    exact Finset.le_sup (f := fun j : I => optimalRadius (H j) u) (Finset.mem_univ i)
  exact_mod_cast hle
end Qatlib.Foundations.MatrixGeometry.AffineCenter
