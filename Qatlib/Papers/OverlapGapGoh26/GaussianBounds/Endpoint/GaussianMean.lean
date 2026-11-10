/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint.SeedParity
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical RealInnerProductSpace
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

def flipInput {r N : ℕ} (x : Input r N) : Input r N :=
  WithLp.toLp 2 (fun a=>Sum.elim (fun k=>x (Sum.inl k)) (fun i=>-x (Sum.inr i)) a)

theorem flipInput_involutive (r N : ℕ) : Function.Involutive (flipInput (r:=r) (N:=N)) := by
  intro x
  ext a
  cases a <;> simp [flipInput]

theorem flipInput_norm {r N : ℕ} (x : Input r N) : ‖flipInput x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,flipInput,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,neg_sq]

def seedReflection (r N : ℕ) : Input r N≃ₗᵢ[ℝ]Input r N where
  toFun := flipInput
  invFun := flipInput
  left_inv := flipInput_involutive r N
  right_inv := flipInput_involutive r N
  map_add' x y := by ext a;cases a <;> simp [flipInput,add_comm]
  map_smul' c x := by ext a;cases a <;> simp [flipInput]
  norm_map' := flipInput_norm

theorem seedReflection_preserving (r N : ℕ) :
    MeasurePreserving (seedReflection r N) (stdGaussian (Input r N)) (stdGaussian (Input r N)) :=
  ⟨by fun_prop,stdGaussian_map _⟩

def spin {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (x : Input r N) : EuclideanSpace ℝ (Fin N) :=
  rawSpin s T (tensorCoords x) (seedCoords x)

theorem spin_component_smooth {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (i : Fin N) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun x:Input r N=>spin s T x i) := contDiff_feedback s T i 2

theorem spin_component_memLp {r N : ℕ} (s : ℕ→ℝ) (T : ℕ) (i : Fin N) :
    MemLp (fun x:Input r N=>spin s T x i) 2 (stdGaussian (Input r N)) := by
  apply MemLp.of_bound (spin_component_smooth s T i).continuous.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x=>by
    simpa only [Real.norm_eq_abs] using! rawSpin_cube s T (tensorCoords x) (seedCoords x) i

theorem spin_reflection {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ) (x : Input r N) :
    spin s T (seedReflection r N x)= -spin s T x := by
  change rawSpin s T (tensorCoords (flipInput x)) (seedCoords (flipInput x))=_
  have ht : tensorCoords (flipInput x)=tensorCoords x := by ext k;rfl
  have hs : seedCoords (flipInput x)=fun i=>-seedCoords x i := rfl
  rw [ht,hs,rawSpin_seed_odd hr]
  rfl

theorem spin_component_mean_zero {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ) (i : Fin N) :
    (∫ x:Input r N,spin s T x i ∂stdGaussian (Input r N))=0 := by
  have hm := (spin_component_memLp (r:=r) (N:=N) s T i).aestronglyMeasurable
  have hmp := seedReflection_preserving r N
  have he :=
      hmp.integral_comp (seedReflection r N).toHomeomorph.measurableEmbedding (fun x=>spin s T x i)
  simp_rw [spin_reflection hr] at he
  simp only [PiLp.neg_apply,integral_neg] at he
  linarith
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
