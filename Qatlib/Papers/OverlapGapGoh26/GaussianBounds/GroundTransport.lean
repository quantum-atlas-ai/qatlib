/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LinearTail
import Qatlib.Papers.OverlapGapGoh26.OgpBridge.ContinuousPath
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.OgpBridge.Path
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Linear

namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport

theorem cube_coefficient_sq_bound {q N : ℕ} (u : Fin N → ℝ) (hu : u∈hilbertCube N) :
    (∑ k : Fin q → Fin N, (∏ a, u (k a))^2)≤(N:ℝ)^q := by
  rw [coefficient_sq_sum (fun _ : Fin q => u)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply pow_le_pow_left₀ (by positivity)
  calc
    (∑ i, u i^2) ≤ ∑ _i : Fin N, (1:ℝ) :=
      Finset.sum_le_sum (fun i _ => by have hi := hu i; nlinarith [hi.1,hi.2])
    _ = (N:ℝ) := by simp

theorem energy_transport_sq {q N : ℕ} (A B : Tensor q N) (u : Fin N → ℝ)
    (hu : u∈hilbertCube N) :
    (tensorEnergy A u-tensorEnergy B u)^2≤(∑ k, (A k-B k)^2)*(N:ℝ)^q := by
  have he : tensorEnergy A u-tensorEnergy B u=∑ k, (A k-B k)*∏ a,u (k a) := by
    unfold tensorEnergy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _).trans
    (mul_le_mul_of_nonneg_left (cube_coefficient_sq_bound u hu) (by positivity))

theorem cubeOpt_le_energy {q N : ℕ} (A : Tensor q N) (u : Fin N → ℝ)
    (hu : u∈hilbertCube N) : cubeOpt A≤tensorEnergy A u := by
  have hc : IsCompact (hilbertCube N) := isCompact_pi_infinite (fun _ : Fin N => isCompact_Icc)
  have he : Continuous (tensorEnergy A) :=
      continuous_tensorEnergy.comp (continuous_const.prodMk continuous_id)
  exact csInf_le (hc.bddBelow_image he.continuousOn) (Set.mem_image_of_mem _ hu)

theorem cube_ground_transport_sq {q N : ℕ} (A B : Tensor q N) :
    (cubeOpt A-cubeOpt B)^2≤(∑ k, (A k-B k)^2)*(N:ℝ)^q := by
  let C := (∑ k, (A k-B k)^2)*(N:ℝ)^q
  have hC : 0≤C := by positivity
  obtain ⟨u,hu,heu⟩ := cubeOpt_attained A
  obtain ⟨v,hv,hev⟩ := cubeOpt_attained B
  have hpos : cubeOpt A-cubeOpt B≤Real.sqrt C := by
    have h := Real.le_sqrt_of_sq_le (energy_transport_sq A B v hv)
    have hlo := cubeOpt_le_energy A v hv
    rw [hev] at h
    linarith
  have hneg : -(cubeOpt A-cubeOpt B)≤Real.sqrt C := by
    have he := energy_transport_sq A B u hu
    have h :=
        Real.le_sqrt_of_sq_le
        (show (-(tensorEnergy A u-tensorEnergy B u))^2≤C by simpa only [neg_sq] using he)
    have hlo := cubeOpt_le_energy B u hu
    rw [heu] at h
    linarith
  have hs := Real.sq_sqrt hC
  nlinarith

def sourceTensor {r N : ℕ} (G : Tensor (r+1) N) : Tensor (r+1) N :=
  fun k => Real.sqrt (((N:ℝ)^r)⁻¹)*G k

theorem normalized_ground_transport_sq {r N : ℕ} (hN : 0<N)
    (G D : Tensor (r+1) N) :
    (cubeOpt (sourceTensor G)/(N:ℝ)-cubeOpt (sourceTensor D)/(N:ℝ))^2≤
      (∑ k, (G k-D k)^2)/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h := cube_ground_transport_sq (sourceTensor G) (sourceTensor D)
  have he : (∑ k, (sourceTensor G k-sourceTensor D k)^2)=
      ((N:ℝ)^r)⁻¹*∑ k,(G k-D k)^2 := by
    simp only [sourceTensor, ← mul_sub, mul_pow, Real.sq_sqrt (by positivity : 0≤((N:ℝ)^r)⁻¹)]
    rw [Finset.mul_sum]
  rw [he] at h
  have hm : ((N:ℝ)^r)⁻¹*(∑ k,(G k-D k)^2)*(N:ℝ)^(r+1)=
      (N:ℝ)*(∑ k,(G k-D k)^2) := by
    rw [pow_succ]
    field_simp
  rw [hm] at h
  have hdiv := div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))
  calc
    _ = (cubeOpt (sourceTensor G)-cubeOpt (sourceTensor D))^2/(N:ℝ)^2 := by ring
    _ ≤ (N:ℝ)*(∑ k,(G k-D k)^2)/(N:ℝ)^2 := hdiv
    _ = _ := by field_simp

end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport
