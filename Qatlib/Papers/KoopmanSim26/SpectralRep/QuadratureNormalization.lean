/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.SpectralSampling
import Qatlib.Concepts.KoopmanFlow.Sampling
import Qatlib.Papers.KoopmanSim26.SpectralRep.UniversalApproximation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder Topology
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Concepts.KoopmanFlow.Sampling

noncomputable section
namespace Qatlib.Papers.KoopmanSim26.SpectralRep
variable {I : Type} [Fintype I] [DecidableEq I]

theorem quadrature_eq_fin_right (L H : Matrix I I ℂ) (t K : ℝ) (N : ℕ) :
    cauchyQuadrature L H t K N =
      ∑ j : Fin N, rawWeight K (uniformRightNodes K N) j •
        spectralUnitary L H t (uniformRightNodes K N j) := by
  unfold cauchyQuadrature
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hn : gridPoint K N (j+1) = uniformRightNodes K N j := by
    simp only [gridPoint, mesh, uniformRightNodes, Nat.cast_add, Nat.cast_one]
    ring
  rw [hn]
  congr 1
  simp only [mesh, cauchyDensity, rawWeight]
  ring

theorem source_right_error (L H : Matrix I I ℂ) (t K : ℝ) (N : ℕ)
    (hL : (-L).PosSemidef) (hH : H.IsHermitian) (ht : 0 ≤ t)
    (hK : 0 < K) (hN : 0 < N) :
    ‖propagator L H t - ∑ j : Fin N,
      rawWeight K (uniformRightNodes K N) j •
        spectralUnitary L H t (uniformRightNodes K N j)‖ ≤
      2/(Real.pi*K) + (2*K^2/(N:ℝ))*(cauchyLipschitzConst+t*‖L‖/Real.pi) := by
  rw [← quadrature_eq_fin_right]
  exact spectral_sampling_quadrature_error L H t K N hL hH ht hK hN

theorem zero_quadrature_right (K : ℝ) (N : ℕ) :
    cauchyQuadrature (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 K N =
      quadratureMass K (uniformRightNodes K N) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [quadrature_eq_fin_right]
  simp only [spectralUnitary, Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]
  exact Finset.sum_smul.symm

theorem right_mass_error (K : ℝ) (N : ℕ) (hK : 0 < K) (hN : 0 < N) :
    |quadratureMass K (uniformRightNodes K N)-1| ≤
      2/(Real.pi*K)+(2*K^2/(N:ℝ))*cauchyLipschitzConst := by
  have hs := spectral_sampling_quadrature_error
    (0 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 K N
    (by simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef))
    Matrix.isHermitian_zero (le_refl 0) hK hN
  rw [zero_quadrature_right] at hs
  simp only [propagator, zero_smul, NormedSpace.exp_zero, zero_mul, zero_div, add_zero] at hs
  have heq : (1 : Matrix (Fin 1) (Fin 1) ℂ) -
      quadratureMass K (uniformRightNodes K N) • (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      (1 - quadratureMass K (uniformRightNodes K N)) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [sub_smul, one_smul]
  rw [heq, norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_sub_comm] at hs
  exact hs

theorem right_grid_rz_minima {n : ℕ} (K : ℝ) (N : ℕ) (α : ℝ → Cube n → ℝ) :
    ∀ j : Fin N, ∃ (φ : ℝ) (θ : Fin n → ℝ),
      rzProductError φ θ (walshPhase (α (uniformRightNodes K N j))) =
        bestProductError (walshPhase (α (uniformRightNodes K N j))) ∧
      (∀ (a : ℝ) (b : Fin n → ℝ),
        rzProductError φ θ (walshPhase (α (uniformRightNodes K N j))) ≤
        rzProductError a b (walshPhase (α (uniformRightNodes K N j)))) ∧
      |rzProductError φ θ (walshPhase (α (uniformRightNodes K N j))) -
        (∑ s, (highPart (α (uniformRightNodes K N j)) s)^2)| ≤
        (phaseConstant n)^4/12*(∑ s, |highPart (α (uniformRightNodes K N j)) s|)^4 := by
  intro j
  exact universal_rz_minimum (α (uniformRightNodes K N j))

theorem root_cube (h : ℕ) : ((h : ℝ) ^ (1/3 : ℝ)) ^ 3 = (h : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg h)]
  norm_num

theorem cubic_right_mass_error (κ : ℝ) (hκ : 0 < κ) (h : ℕ) (hh : 0 < h) :
    |quadratureMass (cubicCutoff κ h) (uniformRightNodes (cubicCutoff κ h) h) - 1| ≤
      (2/(Real.pi*κ)+2*κ^2*cauchyLipschitzConst) * (h:ℝ)^(-(1/3:ℝ)) := by
  have hr : 0 < (h:ℝ)^(1/3:ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hs := right_mass_error (cubicCutoff κ h) h (mul_pos hκ hr) hh
  refine hs.trans_eq ?_
  unfold cubicCutoff
  rw [Real.rpow_neg (Nat.cast_nonneg h)]
  have heq := root_cube h
  have hn : (h:ℝ) ≠ 0 := by positivity
  field_simp
  rw [heq]
  ring

theorem uniform_mass_convergence (κ : ℝ) (hκ : 0 < κ) : UniformMassConvergence κ := by
  unfold UniformMassConvergence
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun h : ℕ => (h:ℝ)^(-(1/3:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/3)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (by simpa using hr.const_mul (2/(Real.pi*κ)+2*κ^2*cauchyLipschitzConst))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with h hh
  simpa only [Real.norm_eq_abs, one_div] using cubic_right_mass_error κ hκ h hh

theorem eventually_mass_half (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ h : ℕ in atTop,
      1/2 ≤ quadratureMass (cubicCutoff κ h) (uniformRightNodes (cubicCutoff κ h) h) := by
  have ht := (uniform_mass_convergence κ hκ).eventually
    (eventually_gt_nhds (by norm_num : (1/2:ℝ)<1))
  exact ht.mono (fun _ hh => le_of_lt hh)

end Qatlib.Papers.KoopmanSim26.SpectralRep
