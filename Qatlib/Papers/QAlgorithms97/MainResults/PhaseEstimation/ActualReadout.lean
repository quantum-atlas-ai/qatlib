/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PoweredProgram
import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.PhaseEstimationSuccess
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit

theorem actual_kernel_bhmt (M : ℕ) (hM : 0 < M) (φ : ℝ) (x : Fin M) :
    ‖qpeKernel M φ x‖ ^ 2 = bhmt11OutcomeMass M φ x := by
  unfold bhmt11OutcomeMass
  rw [bhmt_phase_estimation_theorem11_amplitude M φ hM x,
    (offgrid_phase_kernel_formula M φ x hM).2.1]
  congr 2
  congr 1
  unfold bhmt_phase_estimation_theorem11_expSum
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  push_cast
  ring

theorem actual_nearest_readout {I : Type} [Fintype I] [DecidableEq I]
    (m : ℕ) (hM : 2 < 2 ^ m) (U : Matrix I I ℂ) (φ : ℝ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (ψ : QState I) (hn : Normalized ψ)
    (hψ : U.mulVec ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    ∃ z : Reg m,
      bhmt11CircleDist (((bitVecEquiv m z).val : ℝ) / (2 ^ m : ℝ)) φ ≤
        1 / (2 * (2 ^ m : ℝ)) ∧
      4 / Real.pi ^ 2 ≤
        MeasureProb (PoweredProgram.execute U (PoweredProgram.word m)
          (TensorState (Ket (ZeroStr m)) ψ)) ({z} ×ˢ (Finset.univ : Finset I)) := by
  obtain ⟨x,hx,hp⟩ := phase_estimation_best_approx_success (2 ^ m) φ hM hφ0 hφ1
  refine ⟨(bitVecEquiv m).symm x, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply, Nat.cast_pow, Nat.cast_ofNat] using hx
  · rw [PoweredProgram.word_readout m U φ ψ hn hψ,
      actual_kernel_bhmt (2 ^ m) (Nat.two_pow_pos m), Equiv.apply_symm_apply]
    exact hp

end Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
