module

public import Qatlib.Papers.LowEnergyProd24.CenteredGroups.EnergyShift

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QatlibTests.LowEnergyProd24EnergyShiftConsumer

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.LowEnergyProd24.CenteredGroups
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

/-- A concrete non PSD Hermitian group on a two-dimensional Euclidean space. -/
def concreteGroup : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 0; 0, 0]

/-- The total Hamiltonian consists of the one concrete group. -/
def concreteHamiltonian : Matrix (Fin 2) (Fin 2) ℂ := concreteGroup

/-- The concrete group is Hermitian. -/
theorem concreteGroup_hermitian : concreteGroup.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [concreteGroup, Matrix.conjTranspose_apply]

/-- The concrete total Hamiltonian is the sum of the concrete groups. -/
theorem concrete_sum : ∑ _m : Fin 1, concreteGroup = concreteHamiltonian := by
  simp [concreteHamiltonian]

/-- The concrete group has positive L2-operator norm. -/
theorem concrete_norm_pos : 0 < ∑ _m : Fin 1, ‖concreteGroup‖ := by
  rw [Fin.sum_univ_one, norm_pos_iff]
  intro hzero
  have entry := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hzero
  simp [concreteGroup] at entry

/-- Applying the PSD-shift theorem to the concrete nondegenerate group gives a positive
absolute-cutoff penalty and translates the concrete spectral projector exactly. -/
theorem concrete_psd_shift_cutoff_penalty :
    ∃ C : ℝ, 0 < C ∧
      ∀ Δ : ℝ, low (scalarShift concreteHamiltonian C)
          (scalarShift_hermitian concreteHamiltonian concreteGroup_hermitian C)
          (Δ+C) =
        low concreteHamiltonian concreteGroup_hermitian Δ := by
  obtain ⟨C, hC, c, _, _, _, hlow⟩ :=
    exists_psd_shifts_with_cutoff_penalty
      (fun _ : Fin 1 => concreteGroup) (fun _ => concreteGroup_hermitian)
      concreteHamiltonian concreteGroup_hermitian concrete_sum concrete_norm_pos
  exact ⟨C, hC, hlow⟩

end QatlibTests.LowEnergyProd24EnergyShiftConsumer
