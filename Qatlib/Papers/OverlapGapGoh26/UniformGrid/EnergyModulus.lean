/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.AmpStability
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Stability

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.Modulus

theorem energy_difference {q N : ℕ} (hN : 0<N) (A B : Tensor q N) (u v : Fin N → ℝ)
    (δ η : ℝ) (hδ : 0≤δ)
    (hA : ∀ k,|A k-B k|≤δ) (hB : ∀ k,|B k|≤2)
    (hu : ∀ i,|u i|≤1) (hv : ∀ i,|v i|≤1) (huv : ∀ i,|u i-v i|≤η) :
    |tensorEnergy A u-tensorEnergy B v|≤(N:ℝ)^q*(δ+2*(q:ℝ)*η) :=
  interaction_difference (fun _ => A) (fun _ => B) u v δ η hδ
    (fun _ => hA) (fun _ => hB) hu hv huv ⟨0,hN⟩

theorem actual_energy_density_difference {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (A B : Tensor (r+1) N) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ k,|A k-B k|≤δ) (hB : ∀ k,|B k|≤2) :
    |tensorEnergy A (ampOutput M (rowTensor A) seed s T)/(N:ℝ)-
        tensorEnergy B (ampOutput M (rowTensor B) seed s T)/(N:ℝ)|≤
      (N:ℝ)^r*δ*(1+2*(r+1:ℝ)*(stabilityBase r T N)^T) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hu : ∀ i,|ampOutput M (rowTensor A) seed s T i|≤1 :=
      fun _ => abs_le.mpr (clip_mem 1 (by norm_num) _)
  have hv : ∀ i,|ampOutput M (rowTensor B) seed s T i|≤1 :=
      fun _ => abs_le.mpr (clip_mem 1 (by norm_num) _)
  have huv := actual_output_difference M seed s hs (rowTensor A) (rowTensor B) δ hδ
    (fun i k => hA (Fin.cons i k)) (fun i k => hB (Fin.cons i k))
  have he := energy_difference hN A B _ _ δ (δ*(stabilityBase r T N)^T) hδ
    hA hB hu hv huv
  rw [← sub_div,abs_div,abs_of_pos hn]
  refine (div_le_div_of_nonneg_right he hn.le).trans_eq ?_
  rw [pow_succ]
  field_simp
  push_cast
  ring

theorem sqrt_holder (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    |Real.sqrt x-Real.sqrt y|≤Real.sqrt |x-y| := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have hnx := Real.sqrt_nonneg x
  have hny := Real.sqrt_nonneg y
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hs := Real.sqrt_le_sqrt hxy
    nlinarith [mul_nonneg hnx (sub_nonneg.mpr hs)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hs := Real.sqrt_le_sqrt hyx
    nlinarith [mul_nonneg hny (sub_nonneg.mpr hs)]

theorem interpolated_entry_bound {q N : ℕ} (A B : Tensor q N)
    (hA : ∀ k,|A k|≤1) (hB : ∀ k,|B k|≤1)
    (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (k : Fin q → Fin N) :
    |interpolate A B τ k|≤2 := by
  have h1 : Real.sqrt (1-τ)≤1 := by
    have h := Real.sqrt_le_sqrt (show 1-τ≤1 by linarith [hτ.1]); simpa using h
  have h2 : Real.sqrt τ≤1 := by have h := Real.sqrt_le_sqrt hτ.2; simpa using h
  calc
    _ ≤ |Real.sqrt (1-τ)| *|A k|+|Real.sqrt τ| *|B k| := (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
    _ ≤ 1*1+1*1 := add_le_add
      (mul_le_mul (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using h1) (hA k) (abs_nonneg _) (by norm_num))
      (mul_le_mul (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using h2) (hB k) (abs_nonneg _) (by norm_num))
    _ = _ := by norm_num

theorem interpolated_entry_difference {q N : ℕ} (A B : Tensor q N)
    (hA : ∀ k,|A k|≤1) (hB : ∀ k,|B k|≤1)
    (τ σ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (hσ : σ∈Set.Icc (0:ℝ) 1)
    (k : Fin q → Fin N) :
    |interpolate A B τ k-interpolate A B σ k|≤2*Real.sqrt |τ-σ| := by
  have h1 := sqrt_holder (1-τ) (1-σ) (by linarith [hτ.2]) (by linarith [hσ.2])
  have he : (1-τ)-(1-σ)=-(τ-σ) := by ring
  rw [he,abs_neg] at h1
  have h2 := sqrt_holder τ σ hτ.1 hσ.1
  have he' : interpolate A B τ k-interpolate A B σ k=
      (Real.sqrt (1-τ)-Real.sqrt (1-σ))*A k+(Real.sqrt τ-Real.sqrt σ)*B k := by unfold interpolate; ring
  rw [he']
  calc
    _ ≤ |Real.sqrt (1-τ)-Real.sqrt (1-σ)| *|A k|+|Real.sqrt τ-Real.sqrt σ| *|B k| :=
      (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
    _ ≤ Real.sqrt |τ-σ| *1+Real.sqrt |τ-σ| *1 := add_le_add
      (mul_le_mul h1 (hA k) (abs_nonneg _) (Real.sqrt_nonneg _))
      (mul_le_mul h2 (hB k) (abs_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

def energyHolder (r T N : ℕ) : ℝ :=
  2*(N:ℝ)^r*(1+2*(r+1:ℝ)*(stabilityBase r T N)^T)

theorem energyHolder_nonneg (r T N : ℕ) : 0≤energyHolder r T N := by
  unfold energyHolder
  have h := stabilityBase_ge_one r T N
  positivity

theorem actual_energy_holder {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (w : Sample r N)
    (hA : ∀ k,|w.1.1 k|≤1) (hB : ∀ k,|w.1.2 k|≤1)
    (τ σ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (hσ : σ∈Set.Icc (0:ℝ) 1) :
    |energyPath M s T w τ-energyPath M s T w σ|≤energyHolder r T N*Real.sqrt |τ-σ| := by
  have he := actual_energy_density_difference hN M w.2 s hs
    (interpolate w.1.1 w.1.2 τ) (interpolate w.1.1 w.1.2 σ) (2*Real.sqrt |τ-σ|) (by positivity)
    (interpolated_entry_difference w.1.1 w.1.2 hA hB τ σ hτ hσ)
    (interpolated_entry_bound w.1.1 w.1.2 hA hB σ hσ)
  exact he.trans_eq (by unfold energyHolder; ring)

def holderCoefficient (r T : ℕ) : ℝ :=
  2*(1+2*(r+1:ℝ))*(4*(r:ℝ)*(T:ℝ)+3)^T

theorem holderCoefficient_pos (r T : ℕ) : 0<holderCoefficient r T := by
    unfold holderCoefficient; positivity

theorem energyHolder_polynomial {r N T : ℕ} (hN : 0<N) :
    energyHolder r T N≤holderCoefficient r T*(N:ℝ)^(r*(T+1)) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hp : 1≤(N:ℝ)^r := one_le_pow₀ hn
  have hb : stabilityBase r T N≤(4*(r:ℝ)*(T:ℝ)+3)*(N:ℝ)^r := by unfold stabilityBase; nlinarith
  have hpow := pow_le_pow_left₀ (by have h := stabilityBase_ge_one r T N; linarith) hb T
  have hpT : 1≤(N:ℝ)^(r*T) := one_le_pow₀ hn
  have hc : (1:ℝ)≤4*(r:ℝ)*(T:ℝ)+3 := by
    have h : (0:ℝ)≤4*(r:ℝ)*(T:ℝ) := by positivity
    linarith
  have hcT : 1≤(4*(r:ℝ)*(T:ℝ)+3)^T := one_le_pow₀ hc
  have hbase : 1≤(4*(r:ℝ)*(T:ℝ)+3)^T*(N:ℝ)^(r*T) := by nlinarith
  rw [mul_pow,← pow_mul] at hpow
  unfold energyHolder holderCoefficient
  calc
    _ ≤ 2*(N:ℝ)^r*(1+2*(r+1:ℝ)*((4*(r:ℝ)*(T:ℝ)+3)^T*(N:ℝ)^(r*T))) := by gcongr
    _ ≤ 2*(N:ℝ)^r*((1+2*(r+1:ℝ))*((4*(r:ℝ)*(T:ℝ)+3)^T*(N:ℝ)^(r*T))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = _ := by rw [show r*(T+1)=r+r*T by ring, pow_add]; ring

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.Modulus
