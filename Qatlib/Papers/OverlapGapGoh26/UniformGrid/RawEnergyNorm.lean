/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability
import Qatlib.Papers.OverlapGapGoh26.GaussianBounds.LipschitzMoments
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators RealInnerProductSpace
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.TensorModel.TensorNorm
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.NormStability
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.GaussianBounds.GroundTransport

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm

def rawSpin {r N : ℕ} (s : ℕ→ℝ) (T : ℕ)
    (G : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed : Fin N→ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => feedbackState id (rowTensor (sourceTensor G.ofLp)) seed s T i 2)

def rawEnergyDensity {r N : ℕ} (s : ℕ→ℝ) (T : ℕ)
    (G : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed : Fin N→ℝ) : ℝ :=
  tensorEnergy (sourceTensor G.ofLp) (rawSpin s T G seed).ofLp/(N:ℝ)

theorem rawSpin_cube {r N : ℕ} (s : ℕ→ℝ) (T : ℕ)
    (G : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed : Fin N→ℝ) :
    ∀ i,|rawSpin s T G seed i|≤1 := by
  intro i
  change |feedbackState id (rowTensor (sourceTensor G.ofLp)) seed s T i 2|≤1
  rw [actual_feedback_phi]
  exact Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity.phi_abs_le_one s T _

theorem source_energy_tensor_difference {r N : ℕ} (hN : 0<N)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (z : EuclideanSpace ℝ (Fin N))
    (hz : ∀ i,|z i|≤1) :
    |tensorEnergy (sourceTensor G.ofLp) z.ofLp/(N:ℝ)-tensorEnergy (sourceTensor D.ofLp) z.ofLp/(N:ℝ)|≤
      ‖G-D‖/Real.sqrt (N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have h :=
      energy_transport_sq (sourceTensor G.ofLp) (sourceTensor D.ofLp) z.ofLp
      (fun i => abs_le.mp (hz i))
  have he : (∑ k,(sourceTensor G.ofLp k-sourceTensor D.ofLp k)^2)=
      ((N:ℝ)^r)⁻¹*‖G-D‖^2 := by
    simp only [sourceTensor,← mul_sub,mul_pow,Real.sq_sqrt (by positivity : 0≤((N:ℝ)^r)⁻¹)]
    rw [← Finset.mul_sum,EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [he] at h
  have hm : ((N:ℝ)^r)⁻¹*‖G-D‖^2*(N:ℝ)^(r+1)=(N:ℝ)*‖G-D‖^2 := by
    rw [pow_succ (N:ℝ) r]
    field_simp
  rw [hm] at h
  have hs : (tensorEnergy (sourceTensor G.ofLp) z.ofLp/(N:ℝ)-
      tensorEnergy (sourceTensor D.ofLp) z.ofLp/(N:ℝ))^2≤‖G-D‖^2/(N:ℝ) := by
    have hd := div_le_div_of_nonneg_right h (sq_nonneg (N:ℝ))
    calc
      _ = (tensorEnergy (sourceTensor G.ofLp) z.ofLp-tensorEnergy (sourceTensor D.ofLp) z.ofLp)^2/(N:ℝ)^2 := by ring
      _ ≤ _ := hd
      _ = _ := by field_simp
  have hh := Real.abs_le_sqrt hs
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] at hh
  exact hh

theorem source_energy_spin_difference {r N : ℕ} (hr : 0<r) (hN : 0<N)
    (D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (z w : EuclideanSpace ℝ (Fin N))
    (hz : ∀ i,|z i|≤1) (hw : ∀ i,|w i|≤1) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    |tensorEnergy (sourceTensor D.ofLp) z.ofLp/(N:ℝ)-tensorEnergy (sourceTensor D.ofLp) w.ofLp/(N:ℝ)|≤
      (K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ))*‖z-w‖ := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hsq : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hrad : max ‖z‖ ‖w‖≤Real.sqrt (N:ℝ) := max_le (cube_spin_norm z hz) (cube_spin_norm w hw)
  have hpow : (Real.sqrt (N:ℝ))^r=(Real.sqrt (N:ℝ))^(r-1)*Real.sqrt (N:ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfactor : Real.sqrt (N:ℝ)/(N:ℝ)=1/Real.sqrt (N:ℝ) := by
    apply (div_eq_div_iff hn.ne' hsq.ne').mpr
    nlinarith [Real.sq_sqrt hn.le]
  refine (actual_energy_density_difference hN (sourceTensor D.ofLp) z w).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ ‖tensorForm (sourceTensor D.ofLp)‖*((r+1:ℕ):ℝ)*(Real.sqrt (N:ℝ))^r/(N:ℝ) := by gcongr
    _ = (‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1))*((r+1:ℕ):ℝ)*(Real.sqrt (N:ℝ)/(N:ℝ)) := by rw [hpow]; ring
    _ = (‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1))*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ) := by rw [hfactor]; ring
    _ ≤ _ := by gcongr

theorem actual_raw_energy_difference {r N T : ℕ} (hr : 0<r) (hN : 0<N)
    (s : ℕ→ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1)
    (G D : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed seed' : Fin N→ℝ) (K : ℝ)
    (hK : ‖tensorForm (sourceTensor D.ofLp)‖*(Real.sqrt (N:ℝ))^(r-1)≤K) :
    |rawEnergyDensity s T G seed-rawEnergyDensity s T D seed'|≤
      ((1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T))/Real.sqrt (N:ℝ))*
      (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖) := by
  have hK0 : 0≤K := le_trans (by positivity) hK
  have h1 := source_energy_tensor_difference hN G D (rawSpin s T G seed) (rawSpin_cube s T G seed)
  have h2 := source_energy_spin_difference hr hN D (rawSpin s T G seed) (rawSpin s T D seed')
    (rawSpin_cube s T G seed) (rawSpin_cube s T D seed') K hK
  have h3 := actual_raw_spin_norm hr hN s hs G D seed seed' K hK
  have hn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hc : 0≤K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ) := by positivity
  have hh := h2.trans (mul_le_mul_of_nonneg_left h3 hc)
  have he := (abs_sub_le (tensorEnergy (sourceTensor G.ofLp) (rawSpin s T G seed).ofLp/(N:ℝ))
    (tensorEnergy (sourceTensor D.ofLp) (rawSpin s T G seed).ofLp/(N:ℝ))
    (tensorEnergy (sourceTensor D.ofLp) (rawSpin s T D seed').ofLp/(N:ℝ))).trans (add_le_add h1 hh)
  change |rawEnergyDensity s T G seed-rawEnergyDensity s T D seed'|≤_ at he
  refine he.trans ?_
  have heq : ((1+K*((r+1:ℕ):ℝ)*(2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T))/Real.sqrt (N:ℝ))*
      (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖)=
      (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖)/Real.sqrt (N:ℝ)+
      (K*((r+1:ℕ):ℝ)/Real.sqrt (N:ℝ))*((2*Real.sqrt (T:ℝ)*(2+2*K*(r:ℝ)*Real.sqrt (T:ℝ))^T)*
      (‖G-D‖+‖(WithLp.toLp 2 seed : EuclideanSpace ℝ (Fin N))-WithLp.toLp 2 seed'‖)) := by ring
  rw [heq]
  gcongr
  exact le_add_of_nonneg_right (norm_nonneg _)

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
