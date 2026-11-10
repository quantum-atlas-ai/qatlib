/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.UniformGrid.EnergyModulus
import Qatlib.Papers.OverlapGapGoh26.UniformGrid.ExplicitGrid
import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Program
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.AdaptiveEnergy
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Localization
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Modulus
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.Grid

namespace Qatlib.Papers.OverlapGapGoh26.UniformGrid.FixedInstance

def polynomialHolder (r T N : ℕ) : ℝ :=
  holderCoefficient r T*(N:ℝ)^(r*(T+1))

def actualGrid (r T N : ℕ) (ε : ℝ) : Finset ℝ :=
  uniformGrid (gridResolution (polynomialHolder r T N) ε)

theorem actualGrid_mem (r T N : ℕ) (ε σ : ℝ) (hσ : σ∈actualGrid r T N ε) :
    σ∈Set.Icc (0:ℝ) 1 := uniformGrid_mem (gridResolution_pos _ _) σ hσ

theorem actual_grid_approximation {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) :
    ∀ w∈dataBox r N 1 M,∀ τ∈Set.Icc (0:ℝ) 1,
      ∃ σ∈actualGrid r T N ε,|energyPath M s T w τ-energyPath M s T w σ|<ε := by
  apply uniform_holder_grid (energyPath M s T) (dataBox r N 1 M)
    (polynomialHolder r T N) ε (by unfold polynomialHolder; have h := holderCoefficient_pos r T; positivity) hε
  intro w hw τ hτ σ hσ
  have hA : ∀ k,|w.1.1 k|≤1 := fun k => abs_le.mpr (hw.1.1 k)
  have hB : ∀ k,|w.1.2 k|≤1 := fun k => abs_le.mpr (hw.1.2 k)
  exact (actual_energy_holder hN M s hs w hA hB τ σ hτ hσ).trans
    (mul_le_mul_of_nonneg_right (energyHolder_polynomial hN) (Real.sqrt_nonneg _))

theorem resolution_polynomial (r T N : ℕ) (ε : ℝ) :
    (2*polynomialHolder r T N/ε)^2=
      (2*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))) := by
  unfold polynomialHolder
  rw [show 2*(r*(T+1))=(r*(T+1))*2 by omega,pow_mul]
  ring

theorem actualGrid_card (r T N : ℕ) (ε : ℝ) :
    (actualGrid r T N ε).card≤
      Nat.ceil ((2*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))))+2 := by
  have h := uniformGrid_card (gridResolution (polynomialHolder r T N) ε)
  simpa only [actualGrid,gridResolution,resolution_polynomial,Nat.add_assoc] using! h

theorem actualGrid_card_real (r T N : ℕ) (ε : ℝ) :
    ((actualGrid r T N ε).card:ℝ)≤
      (2*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1)))+3 := by
  have h := uniform_holder_grid_card (polynomialHolder r T N) ε
  rw [resolution_polynomial] at h
  exact h

theorem actual_grid_energy_inclusion {r N T : ℕ} (hN : 0<N) (M : ℝ)
    (s : ℕ → ℝ) (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) (c : ℝ) :
    {w : Sample r N | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤energyPath M s T w τ} ⊆
      (dataBox r N 1 M)ᶜ ∪ ⋃ σ∈actualGrid r T N ε,{w | c≤energyPath M s T w σ} := by
  intro w hw
  by_cases hb : w∈dataBox r N 1 M
  · obtain ⟨τ,hτ,hbig⟩ := hw
    obtain ⟨σ,hσ,hd⟩ := actual_grid_approximation hN M s hs ε hε w hb τ hτ
    right
    apply Set.mem_iUnion.mpr ⟨σ,?_⟩
    apply Set.mem_iUnion.mpr ⟨hσ,?_⟩
    have hdist := abs_lt.mp hd
    change c≤energyPath M s T w σ
    linarith [hdist.2]
  · exact Or.inl hb

theorem actual_quantitative_fixed_instance_reduction {r N T : ℕ} (hN : 0<N)
    (M : ℝ) (hM : 0≤M) (v : NNReal) (s : ℕ → ℝ)
    (hs : ∀ j≤T,s j∈Set.Icc (0:ℝ) 1) (ε : ℝ) (hε : 0<ε) (c : ℝ) :
    jointLaw M v r N {w | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤energyPath M s T w τ}≤
      ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^r/2))+
        ((Nat.ceil ((2*holderCoefficient r T/ε)^2*(N:ℝ)^(2*(r*(T+1))))+2:ℕ):ENNReal)*
          ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
            {p | c≤tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
  let P := jointLaw M v r N
  let Q := ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
    {p | c≤tensorEnergy p.1 (ampOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)}
  have hinc := actual_grid_energy_inclusion (r:=r) hN M s hs ε hε c
  have hP := (measure_mono (μ:=P) hinc).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (measure_biUnion_finset_le (actualGrid r T N ε) _)))
  have hloc : P (dataBox r N 1 M)ᶜ≤
      ENNReal.ofReal (4*(N:ℝ)^(r+1)*Real.exp (-(N:ℝ)^r/2)) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    have hv : -1/(2*(((N:NNReal)^r)⁻¹:ℝ))=-(N:ℝ)^r/2 := by
      simp only [NNReal.coe_natCast]
      have hn : (N:ℝ)≠0 := by positivity
      field_simp
    simpa only [one_pow,hv] using! actual_dataBox_tail (r:=r) (N:=N) M hM v 1 (by norm_num)
  have hsum : (∑ σ∈actualGrid r T N ε,P {w | c≤energyPath M s T w σ})=
      (actualGrid r T N ε).card * Q := by
    calc
      _ = ∑ _σ∈actualGrid r T N ε,Q := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact actual_adaptive_energy_stationary M v s T σ (actualGrid_mem r T N ε σ hσ) c
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  change P {w | ∃ τ∈Set.Icc (0:ℝ) 1,c+ε≤energyPath M s T w τ}≤_
  refine hP.trans ?_
  change P (dataBox r N 1 M)ᶜ+(∑ σ∈actualGrid r T N ε,P {w | c≤energyPath M s T w σ})≤_
  rw [hsum]
  exact add_le_add hloc
      (mul_le_mul_of_nonneg_right (by exact_mod_cast actualGrid_card r T N ε) (zero_le : 0≤Q))

end Qatlib.Papers.OverlapGapGoh26.UniformGrid.FixedInstance
