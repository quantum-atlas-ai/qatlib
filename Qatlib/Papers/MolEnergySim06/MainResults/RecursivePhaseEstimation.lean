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

/-!
# Recursive phase readout widths and a base window bound

This module records a four-qubit readout size and a residual-width model that halves at each
refinement, following the recursive phase-estimation discussion of [AspuruGuzikEtAl2005].
Sixteen refinements give width `2^(-20)` while the stored readout size remains four.

For the actual sixteen-point phase-estimation kernel, the module proves a probability lower
bound for a nearby phase window. It also records the interval arithmetic used to shift a
residual phase.

## Main statements

* `recursive_readout_reduction`: Compare the stored four-qubit readout with the twenty-qubit
  standard count and residual-width bound.
* `base_four_qubit_window_probability`: A sixteen-point phase window has kernel weight at least
  `8 / π^2`.
* `shifted_residual_mem`: A quarter-width phase estimate gives a shifted residual in `[0, 1 /
  2]`.

## References

* [Aspuru-Guzik et al., 2005][AspuruGuzikEtAl2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MolEnergySim06.MainResults

open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

/-- The fixed recursive phase-readout register size of four qubits. -/
def recursiveReadoutQubits : ℕ := 4

/-- The standard readout size `4 + k` corresponding to `k` additional precision bits. -/
def standardReadoutQubits (k : ℕ) : ℕ := recursiveReadoutQubits + k

/-- The rational residual-width model `(1 / 2)^(4 + k)` after `k` refinements. -/
def residualWidth (k : ℕ) : ℚ := (1 / 2 : ℚ) ^ (4 + k)

/-- Each refinement halves the modeled residual width; see [AspuruGuzikEtAl2005]. -/
theorem residualWidth_succ (k : ℕ) : residualWidth (k + 1) = residualWidth k / 2 := by
  unfold residualWidth
  rw [show 4 + (k + 1) = (4 + k) + 1 by ring, pow_succ]
  ring

/-- Twice the residual width after one further refinement equals the current residual width; see
[AspuruGuzikEtAl2005]. -/
theorem residualWidth_one_bit (k : ℕ) :
    residualWidth (k + 1) * 2 = residualWidth k := by
  rw [residualWidth_succ]
  ring

/-- After sixteen refinements, the modeled residual width is exactly `(1 / 2)^20`. -/
theorem residualWidth_sixteen : residualWidth 16 = (1 / 2 : ℚ) ^ 20 := by
  unfold residualWidth
  norm_num

/-- After sixteen refinements, the modeled residual width is at most one millionth. -/
theorem residualWidth_sixteen_bound : residualWidth 16 ≤ 1 / 1000000 := by
  rw [residualWidth_sixteen]
  norm_num

/-- The recursive register size is four, the standard count at sixteen extra bits is twenty, and
the modeled residual width is at most one millionth; see [AspuruGuzikEtAl2005]. -/
theorem recursive_readout_reduction :
    recursiveReadoutQubits = 4 ∧
    standardReadoutQubits 16 = 20 ∧
    residualWidth 16 ≤ 1 / 1000000 := by
  refine ⟨rfl, ?_, residualWidth_sixteen_bound⟩
  unfold standardReadoutQubits recursiveReadoutQubits
  norm_num

/-- For any positive number of additional precision bits, the stored recursive readout size is
smaller than the standard count; see [AspuruGuzikEtAl2005]. -/
theorem recursive_fewer_qubits {k : ℕ} (hk : 0 < k) :
    recursiveReadoutQubits < standardReadoutQubits k := by
  unfold recursiveReadoutQubits standardReadoutQubits
  exact Nat.lt_add_of_pos_right hk

/-- For any phase, the sixteen-point phase-estimation kernel assigns total weight at least `8 /
Real.pi^2` to indices within circular phase distance `1 / 16`; see [AspuruGuzikEtAl2005]. -/
theorem base_four_qubit_window_probability (φ : ℝ) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin 16 =>
        phaseDistance φ ((z.val : ℝ) / (16 : ℝ)) ≤ 1 / (16 : ℝ)),
      ‖qpeKernel 16 φ z‖ ^ 2 ≥ 8 / Real.pi ^ 2 := by
  simpa using offgrid_phase_window_probability 16 φ (by norm_num)

/-- The sixteen-point phase-estimation kernel has strictly positive total weight in the circular
phase window of radius `1 / 16`. -/
theorem base_four_qubit_window_positive (φ : ℝ) :
    0 < ∑ z ∈ Finset.univ.filter (fun z : Fin 16 =>
        phaseDistance φ ((z.val : ℝ) / (16 : ℝ)) ≤ 1 / (16 : ℝ)),
      ‖qpeKernel 16 φ z‖ ^ 2 := by
  have h := base_four_qubit_window_probability φ
  have hp : (0 : ℝ) < 8 / Real.pi ^ 2 := by positivity
  linarith

/-- If `|φ - φhat| ≤ 1 / 4`, the shifted residual `φ - (φhat - 1 / 4)` lies between zero and one
half; see [AspuruGuzikEtAl2005]. -/
theorem shifted_residual_mem (φ φhat : ℝ) (h : |φ - φhat| ≤ 1 / 4) :
    0 ≤ φ - (φhat - 1 / 4) ∧ φ - (φhat - 1 / 4) ≤ 1 / 2 := by
  have h' := abs_le.mp h
  constructor <;> linarith

/-- The base rational resolution `1 / 16` is at most the shift-window radius `1 / 4`. -/
theorem base_resolution_le_shift_window : (1 / 16 : ℚ) ≤ 1 / 4 := by norm_num

end Qatlib.Papers.MolEnergySim06.MainResults
