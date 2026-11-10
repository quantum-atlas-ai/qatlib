/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Qatlib.Papers.LatGaugeSim05.MainResults.U1RegisterHamiltonian
import Qatlib.Papers.LatGaugeSim05.MainResults.SU2Hamiltonian
import Qatlib.Papers.LatGaugeSim05.MainResults.SU3Hamiltonian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.LatGaugeSim05.MainResults

def mainQubitCount (c M d D : ℕ) : ℕ := c * M * d * D

theorem main_qubit_count_linear (c d D M : ℕ) :
    mainQubitCount c (M + 1) d D = mainQubitCount c M d D + c * (d * D) := by
  simp only [mainQubitCount]; ring

theorem main_three_models (M d D : ℕ) :
    mainQubitCount 1 M d D = M * d * D ∧
      mainQubitCount 3 M d D = 3 * (M * d * D) ∧
      mainQubitCount 8 M d D = 8 * (M * d * D) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [mainQubitCount] <;> ring

theorem main_models_match_registers (M d D : ℕ) :
    mainQubitCount 1 M d D = u1QubitCount M d D ∧
      mainQubitCount 3 M d D = u2QubitCount M d D ∧
      mainQubitCount 8 M d D = u3QubitCount M d D := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [mainQubitCount, u1QubitCount]; ring
  · simp only [mainQubitCount, u2QubitCount]
  · simp only [mainQubitCount, u3QubitCount]

def mainBestGates (c M d : ℕ) : ℕ := c * (M * d)

def mainWorstGates (c M d D : ℕ) : ℕ := c * (M * d) * (M * d * D)

theorem main_best_gates_linear (c d M : ℕ) :
    mainBestGates c (M + 1) d = mainBestGates c M d + c * d := by
  simp only [mainBestGates]; ring

theorem main_worst_gates_quadratic (c M d D : ℕ) :
    mainWorstGates c M d D = c * M ^ 2 * d ^ 2 * D := by
  simp only [mainWorstGates]; ring

theorem main_between_linear_and_quadratic (c M d D : ℕ) (h : 1 ≤ M * d * D) :
    mainBestGates c M d ≤ mainWorstGates c M d D := by
  simp only [mainBestGates, mainWorstGates]

  have h0 : 0 ≤ c * (M * d) := Nat.zero_le _
  calc c * (M * d) = c * (M * d) * 1 := by ring
    _ ≤ c * (M * d) * (M * d * D) := by
        exact Nat.mul_le_mul_left _ h

theorem main_result (c M d D : ℕ) (h : 1 ≤ M * d * D) :
    (∀ M', mainQubitCount c (M' + 1) d D
        = mainQubitCount c M' d D + c * (d * D)) ∧
      (mainBestGates c (M + 1) d = mainBestGates c M d + c * d) ∧
      mainWorstGates c M d D = c * M ^ 2 * d ^ 2 * D ∧
      mainBestGates c M d ≤ mainWorstGates c M d D :=
  ⟨fun M' => main_qubit_count_linear c d D M',
    main_best_gates_linear c d M,
    main_worst_gates_quadratic c M d D,
    main_between_linear_and_quadratic c M d D h⟩

end Qatlib.Papers.LatGaugeSim05.MainResults
