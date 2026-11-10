/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSystemSim96.MainResults.ShortTimeStepFactorization
import Qatlib.Concepts.QftPreparation.LocalQft
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Matrix
open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Papers.QSystemSim96.MainResults

theorem manyParticle_state_space_card (d l : ℕ) :
    Fintype.card (Fin d → ZMod (2 ^ l)) = 2 ^ (l * d) := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_mul]

theorem diagonal_unitary_of_unit_modulus {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → ℂ} (hd : ∀ i, d i * star (d i) = 1) :
    Matrix.diagonal d ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with hij
  · subst hij
    exact hd i
  · rfl

def multiRegisterPhase {ι : Type*} [DecidableEq ι] (F : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun x => Complex.exp (Complex.I * (F x : ℂ)))

theorem multiRegisterPhase_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → ℝ) :
    multiRegisterPhase F ∈ Matrix.unitaryGroup ι ℂ := by
  apply diagonal_unitary_of_unit_modulus
  intro x
  exact exp_phase_mul_star (F x)

theorem localQFT_implements_fourier_and_cost (l : ℕ) :
    localProgramMatrix (localQFT l) =
        Qatlib.Foundations.PureStateMath.BornBridge.relabelGate
          (Qatlib.Foundations.PureStateMath.bitVecEquiv l).symm
          (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix (2 ^ l)) ∧
      GateCount (localProgramCircuit (localQFT l)) =
        l + l * (l - 1) / 2 + l / 2 ∧
      QueryCount (localProgramCircuit (localQFT l)) = 0 :=
  Qatlib.Concepts.QftPreparation.LocalQft.aqLocalQFT_actual_matrix_and_cost l

theorem localQFT_gate_count_le_square (l : ℕ) :
    l + l * (l - 1) / 2 + l / 2 ≤ (l + 1) ^ 2 := by
  have h1 : l * (l - 1) / 2 ≤ l * l / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul_left l (Nat.sub_le l 1))
  have h2 : l * l / 2 ≤ l * l := Nat.div_le_self _ _
  have h3 : l / 2 ≤ l := Nat.div_le_self _ _
  have hexp : (l + 1) ^ 2 = l * l + 2 * l + 1 := by ring
  omega

theorem finite_grid_simulation_components (d l : ℕ) :
    Fintype.card (Fin d → ZMod (2 ^ l)) = 2 ^ (l * d) ∧
      (∀ (m Δx Δt : ℝ) (V : ZMod (2 ^ l) → ℝ) (A : ℕ),
        IsUnit (A : ZMod (2 ^ l)) →
          m * Δx ^ 2 / Δt = (A : ℝ) * (2 * Real.pi / ((2 ^ l : ℕ) : ℝ)) →
          stepMatrix (2 ^ l) m Δx Δt V =
              stepNormalisation (2 ^ l) •
                (diagonalRight (2 ^ l) m Δx Δt * fourierMatrix (2 ^ l) m Δx Δt *
                  diagonalLeft (2 ^ l) m Δx Δt V) ∧
            stepMatrix (2 ^ l) m Δx Δt V ∈ Matrix.unitaryGroup (ZMod (2 ^ l)) ℂ) ∧
      localProgramMatrix (localQFT l) =
          Qatlib.Foundations.PureStateMath.BornBridge.relabelGate
            (Qatlib.Foundations.PureStateMath.bitVecEquiv l).symm
            (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix (2 ^ l)) ∧
      GateCount (localProgramCircuit (localQFT l)) = l + l * (l - 1) / 2 + l / 2 ∧
      QueryCount (localProgramCircuit (localQFT l)) = 0 ∧
      l + l * (l - 1) / 2 + l / 2 ≤ (l + 1) ^ 2 ∧
      (∀ F : (Fin d → ZMod (2 ^ l)) → ℝ,
        multiRegisterPhase F ∈ Matrix.unitaryGroup (Fin d → ZMod (2 ^ l)) ℂ) := by
  obtain ⟨hmatrix, hcount, hquery⟩ := localQFT_implements_fourier_and_cost l
  refine ⟨manyParticle_state_space_card d l, ?_, hmatrix, hcount, hquery,
    localQFT_gate_count_le_square l, ?_⟩
  · intro m Δx Δt V A hu hcond
    exact ⟨(shortTimeStep_two_diagonal_and_fourier (2 ^ l) m Δx Δt V A hu hcond).1,
      (shortTimeStep_two_diagonal_and_fourier (2 ^ l) m Δx Δt V A hu hcond).2.2.2⟩
  · intro F
    exact multiRegisterPhase_mem_unitaryGroup F

end Qatlib.Papers.QSystemSim96.MainResults
