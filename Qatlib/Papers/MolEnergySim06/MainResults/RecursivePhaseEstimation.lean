/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

def recursiveReadoutQubits : ℕ := 4

def standardReadoutQubits (k : ℕ) : ℕ := recursiveReadoutQubits + k

def residualWidth (k : ℕ) : ℚ := (1 / 2 : ℚ) ^ (4 + k)

theorem residualWidth_succ (k : ℕ) : residualWidth (k + 1) = residualWidth k / 2 := by
  unfold residualWidth
  rw [show 4 + (k + 1) = (4 + k) + 1 by ring, pow_succ]
  ring

theorem residualWidth_one_bit (k : ℕ) :
    residualWidth (k + 1) * 2 = residualWidth k := by
  rw [residualWidth_succ]
  ring

theorem residualWidth_sixteen : residualWidth 16 = (1 / 2 : ℚ) ^ 20 := by
  unfold residualWidth
  norm_num

theorem residualWidth_sixteen_bound : residualWidth 16 ≤ 1 / 1000000 := by
  rw [residualWidth_sixteen]
  norm_num

theorem recursive_readout_reduction :
    recursiveReadoutQubits = 4 ∧
    standardReadoutQubits 16 = 20 ∧
    residualWidth 16 ≤ 1 / 1000000 := by
  refine ⟨rfl, ?_, residualWidth_sixteen_bound⟩
  unfold standardReadoutQubits recursiveReadoutQubits
  norm_num

theorem recursive_fewer_qubits {k : ℕ} (hk : 0 < k) :
    recursiveReadoutQubits < standardReadoutQubits k := by
  unfold recursiveReadoutQubits standardReadoutQubits
  exact Nat.lt_add_of_pos_right hk

theorem base_four_qubit_window_probability (φ : ℝ) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin 16 =>
        phaseDistance φ ((z.val : ℝ) / (16 : ℝ)) ≤ 1 / (16 : ℝ)),
      ‖qpeKernel 16 φ z‖ ^ 2 ≥ 8 / Real.pi ^ 2 := by
  simpa using offgrid_phase_window_probability 16 φ (by norm_num)

theorem base_four_qubit_window_positive (φ : ℝ) :
    0 < ∑ z ∈ Finset.univ.filter (fun z : Fin 16 =>
        phaseDistance φ ((z.val : ℝ) / (16 : ℝ)) ≤ 1 / (16 : ℝ)),
      ‖qpeKernel 16 φ z‖ ^ 2 := by
  have h := base_four_qubit_window_probability φ
  have hp : (0 : ℝ) < 8 / Real.pi ^ 2 := by positivity
  linarith

theorem shifted_residual_mem (φ φhat : ℝ) (h : |φ - φhat| ≤ 1 / 4) :
    0 ≤ φ - (φhat - 1 / 4) ∧ φ - (φhat - 1 / 4) ≤ 1 / 2 := by
  have h' := abs_le.mp h
  constructor <;> linarith

theorem base_resolution_le_shift_window : (1 / 16 : ℚ) ≤ 1 / 4 := by norm_num

end Qatlib.Papers.MolEnergySim06.MainResults
