/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.FixedInstance
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Stability
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Modulus
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Grid
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.FixedInstance

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinEnergy

theorem actual_spin_difference {r N T : ℕ} (M : ℝ) (seed : Fin N → ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤ T,s j∈Set.Icc (0:ℝ) 1)
    (A B : Tensor (r+1) N) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ k,|A k-B k|≤δ) (hB : ∀ k,|B k|≤2) (i : Fin N) :
    |spinOutput M (rowTensor A) seed s T i-spinOutput M (rowTensor B) seed s T i|≤
      2*(T:ℝ)*(δ*(stabilityBase r T N)^T) := by
  have hb := stabilityBase_ge_one r T N
  exact readout_difference s le_rfl hs _ _ _ (by positivity)
    (actual_history_difference M seed s hs (rowTensor A) (rowTensor B) δ hδ
      (fun i k => hA (Fin.cons i k)) (fun i k => hB (Fin.cons i k)) T le_rfl) i

theorem actual_spin_density_difference {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (seed : Fin N → ℝ) (s : ℕ → ℝ) (hs : ∀ j≤ T,s j∈Set.Icc (0:ℝ) 1)
    (A B : Tensor (r+1) N) (δ : ℝ) (hδ : 0≤δ)
    (hA : ∀ k,|A k-B k|≤δ) (hB : ∀ k,|B k|≤2) :
    |tensorEnergy A (spinOutput M (rowTensor A) seed s T)/(N:ℝ)-
        tensorEnergy B (spinOutput M (rowTensor B) seed s T)/(N:ℝ)|≤
      (N:ℝ)^r*δ*(1+2*(r+1:ℝ)*(2*(T:ℝ)*(stabilityBase r T N)^T)) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hu : ∀ i,|spinOutput M (rowTensor A) seed s T i|≤1 := fun _ => phi_abs_le_one s T _
  have hv : ∀ i,|spinOutput M (rowTensor B) seed s T i|≤1 := fun _ => phi_abs_le_one s T _
  have he := energy_difference hN A B _ _ δ (2*(T:ℝ)*(δ*(stabilityBase r T N)^T)) hδ
    hA hB hu hv (actual_spin_difference M seed s hs A B δ hδ hA hB)
  rw [← sub_div,abs_div,abs_of_pos hn]
  refine (div_le_div_of_nonneg_right he hn.le).trans_eq ?_
  rw [pow_succ]
  field_simp
  push_cast
  ring

def spinHolder (r T N : ℕ) : ℝ := (1+2*(T:ℝ))*energyHolder r T N

theorem actual_spin_energy_holder {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤ T,s j∈Set.Icc (0:ℝ) 1) (w : Sample r N)
    (hA : ∀ k,|w.1.1 k|≤1) (hB : ∀ k,|w.1.2 k|≤1)
    (τ σ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (hσ : σ∈Set.Icc (0:ℝ) 1) :
    |spinEnergyPath M s T w τ-spinEnergyPath M s T w σ|≤ spinHolder r T N*Real.sqrt |τ-σ| := by
  have he := actual_spin_density_difference hN M w.2 s hs
    (interpolate w.1.1 w.1.2 τ) (interpolate w.1.1 w.1.2 σ) (2*Real.sqrt |τ-σ|) (by positivity)
    (interpolated_entry_difference w.1.1 w.1.2 hA hB τ σ hτ hσ)
    (interpolated_entry_bound w.1.1 w.1.2 hA hB σ hσ)
  have hb := stabilityBase_ge_one r T N
  have hp : 0≤2*(N:ℝ)^r*(2*(T:ℝ)+2*(r+1:ℝ)*(stabilityBase r T N)^T) := by positivity
  have hc : 2*(N:ℝ)^r*(1+2*(r+1:ℝ)*(2*(T:ℝ)*(stabilityBase r T N)^T))≤ spinHolder r T N := by
    unfold spinHolder energyHolder
    nlinarith
  calc
    _ ≤ (N:ℝ)^r*(2*Real.sqrt |τ-σ|)*(1+2*(r+1:ℝ)*(2*(T:ℝ)*(stabilityBase r T N)^T)) := he
    _ = (2*(N:ℝ)^r*(1+2*(r+1:ℝ)*(2*(T:ℝ)*(stabilityBase r T N)^T)))*Real.sqrt |τ-σ| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

def spinPolynomialHolder (r T N : ℕ) : ℝ := (1+2*(T:ℝ))*polynomialHolder r T N

theorem spinHolder_polynomial {r N T : ℕ} (hN : 0<N) :
    spinHolder r T N≤ spinPolynomialHolder r T N :=
  mul_le_mul_of_nonneg_left (energyHolder_polynomial hN) (by positivity)

def spinActualGrid (r T N : ℕ) (ε : ℝ) : Finset ℝ :=
  uniformGrid (gridResolution (spinPolynomialHolder r T N) ε)

theorem actual_spin_grid_approximation {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤ T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    ∀ w∈dataBox r N 1 M,∀ τ∈Set.Icc (0:ℝ) 1,
      ∃ σ∈spinActualGrid r T N ε,|spinEnergyPath M s T w τ-spinEnergyPath M s T w σ|<ε := by
  apply uniform_holder_grid (spinEnergyPath M s T) (dataBox r N 1 M)
    (spinPolynomialHolder r T N) ε (by unfold spinPolynomialHolder polynomialHolder; have h := holderCoefficient_pos r T; positivity) hε
  intro w hw τ hτ σ hσ
  exact (actual_spin_energy_holder hN M s hs w
    (fun k => abs_le.mpr (hw.1.1 k)) (fun k => abs_le.mpr (hw.1.2 k)) τ σ hτ hσ).trans
      (mul_le_mul_of_nonneg_right (spinHolder_polynomial hN) (Real.sqrt_nonneg _))

theorem spinActualGrid_card (r T N : ℕ) (ε : ℝ) :
    (spinActualGrid r T N ε).card≤
      Nat.ceil ((2*(1+2*(T:ℝ))*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))))+2 := by
  have he : (2*spinPolynomialHolder r T N/ε)^2=
      (2*(1+2*(T:ℝ))*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))) := by
    unfold spinPolynomialHolder polynomialHolder
    rw [show 2*(r*(T+1))=(r*(T+1))*2 by omega,pow_mul]
    ring
  have h := uniformGrid_card (gridResolution (spinPolynomialHolder r T N) ε)
  simpa only [spinActualGrid,gridResolution,he,Nat.add_assoc] using h

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.SpinEnergy
