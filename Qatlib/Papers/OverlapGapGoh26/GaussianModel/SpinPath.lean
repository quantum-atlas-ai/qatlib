/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
import Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace NNReal
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Papers.OverlapGapGoh26.AmpDynamics.Regularity
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Interpolation
open Qatlib.Papers.OverlapGapGoh26.GaussianModel.Stationarity
open Qatlib.Papers.OverlapGapGoh26.OgpBridge.Gaussian

namespace Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath

def spinPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (spinOutput M (rowTensor (interpolate A B τ)) seed s T)

theorem continuous_tensor_spin (r N : ℕ) (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : Tensor (r+1) N × (Fin N → ℝ) => spinOutput M (rowTensor p.1) p.2 s T) := by
  have hj : Continuous (fun p : Tensor (r+1) N × (Fin N → ℝ) => rowTensor p.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    exact (continuous_apply (@Fin.cons r (fun _ => Fin N) i k)).comp continuous_fst
  exact (continuous_spinOutput M s T).comp (hj.prodMk continuous_snd)

theorem continuous_spinPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) : Continuous (spinPath M s T A B seed) := by
  have hi : Continuous (fun τ : ℝ => interpolate A B τ) := by unfold interpolate; fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
    ((continuous_tensor_spin r N M s T).comp (hi.prodMk continuous_const))

theorem spinPath_cube {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) (i : Fin N) :
    (spinPath M s T A B seed τ).ofLp i ∈ Set.Icc (-1:ℝ) 1 :=
  abs_le.mp (phi_abs_le_one s T _)

theorem spinPath_feedback {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ)
    (A B : Tensor (r+1) N) (seed : Fin N → ℝ) (τ : ℝ) (i : Fin N) :
    (spinPath M s T A B seed τ).ofLp i=
      SpinDynamics.Feedback.feedbackState (AmpDynamics.Program.clip M)
        (rowTensor (interpolate A B τ)) seed s T i 2 := by
  exact (SpinDynamics.Feedback.bounded_feedback_eq_spinOutput M _ seed s T i).symm

def spinEnergyPath {r N : ℕ} (M : ℝ) (s : ℕ → ℝ) (T : ℕ) (w : Sample r N) (τ : ℝ) : ℝ :=
  tensorEnergy (interpolate w.1.1 w.1.2 τ) (spinPath M s T w.1.1 w.1.2 w.2 τ).ofLp/(N:ℝ)

theorem continuous_spinEnergy (r N : ℕ) (M : ℝ) (s : ℕ → ℝ) (T : ℕ) :
    Continuous (fun p : Tensor (r+1) N × (Fin N → ℝ) =>
      tensorEnergy p.1 (spinOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)) :=
  (continuous_tensorEnergy.comp (continuous_fst.prodMk (continuous_tensor_spin r N M s T))).div_const _

theorem actual_spin_energy_stationary {r N : ℕ} (M : ℝ) (v : NNReal)
    (s : ℕ → ℝ) (T : ℕ) (τ : ℝ) (hτ : τ∈Set.Icc (0:ℝ) 1) (c : ℝ) :
    jointLaw M v r N {w | c≤ spinEnergyPath M s T w τ}=
      ((gaussianTensorLaw r N).prod (boundedSeedLaw M N v))
        {p | c≤ tensorEnergy p.1 (spinOutput M (rowTensor p.1) p.2 s T)/(N:ℝ)} := by
  exact (interpolate_seed_preserving M v r N τ hτ).measure_preimage
    (measurableSet_le measurable_const (continuous_spinEnergy r N M s T).measurable).nullMeasurableSet

end Qatlib.Papers.OverlapGapGoh26.GaussianModel.SpinPath
