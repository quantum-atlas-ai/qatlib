module

public import Qatlib.Papers.LowEnergyProd24.CenteredGroups.ProjectedShift

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QatlibTests.LowEnergyProd24CenteredGroupsConsumer

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.LowEnergyProd24.CenteredGroups
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff

/-- A concrete Hermitian group family on a nonempty two-dimensional qubit space. -/
def concreteGroups : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![-1, 1; 1, 1], !![1, -1; -1, 0]]

/-- A concrete non-degenerate Hermitian total Hamiltonian. -/
def concreteHamiltonian : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![0, 1]

/-- The concrete total Hamiltonian is Hermitian. -/
theorem concreteHamiltonian_hermitian : concreteHamiltonian.IsHermitian := by
  simp [concreteHamiltonian, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]

/-- Both concrete groups are Hermitian. -/
theorem concreteGroups_hermitian : ∀ m, (concreteGroups m).IsHermitian := by
  intro m
  fin_cases m <;> change _ᴴ = _ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [concreteGroups, Matrix.conjTranspose_apply]

/-- The two groups decompose the concrete total Hamiltonian. -/
theorem concreteGroups_sum : ∑ m, concreteGroups m = concreteHamiltonian := by
  rw [Fin.sum_univ_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [concreteGroups, concreteHamiltonian, Matrix.diagonal_apply]

/-- Retain both eigenspaces so that this cutoff preserves the noncommuting groups. -/
noncomputable def concreteCutoff : ℝ :=
  max (concreteHamiltonian_hermitian.eigenvalues 0)
    (concreteHamiltonian_hermitian.eigenvalues 1)

/-- The cutoff retains the entire concrete space. -/
theorem concreteLow_eq_one : low concreteHamiltonian concreteHamiltonian_hermitian
    concreteCutoff = 1 := by
  have hle (i : Fin 2) : concreteHamiltonian_hermitian.eigenvalues i ≤ concreteCutoff := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  simp [low, mask, hle, Matrix.diagonal_one]

/-- At this cutoff the shifted compressed factors have a nonzero first commutator. -/
theorem concrete_shifted_commutator_ne_zero (c : Fin 2 → ℝ) :
    nestedCommutator (fun m => shiftedCompression concreteHamiltonian
      concreteHamiltonian_hermitian concreteCutoff (concreteGroups m) (c m)) 0 [1] ≠ 0 := by
  simp only [shiftedCompression, concreteLow_eq_one, one_mul, mul_one]
  rw [nestedCommutator_shift concreteGroups c 0 [1] (by simp)]
  intro h
  have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
  norm_num [nestedCommutator, nestedFrom, bracket, concreteGroups, Matrix.mul_apply,
    Fin.sum_univ_two] at he

/-- An ordinary module can apply the bound at positive order to the concrete groups. -/
example :
    ∃ c : Fin 2 → ℝ,
      (∀ m, ‖shiftedCompression concreteHamiltonian concreteHamiltonian_hermitian
        concreteCutoff (concreteGroups m) (c m)‖ =
        shiftedRadius concreteHamiltonian concreteHamiltonian_hermitian
          concreteCutoff (concreteGroups m)) ∧
      ∀ s : ℝ, 0 ≤ s →
        ‖∫ σ in (0 : ℝ)..s, (σ ^ 1 : ℝ) •
            nestedCommutator (fun m => shiftedCompression concreteHamiltonian
              concreteHamiltonian_hermitian concreteCutoff (concreteGroups m) (c m)) 0 [1]‖ ≤
          (shiftedScale concreteHamiltonian concreteHamiltonian_hermitian
            concreteCutoff concreteGroups) ^ 2 * s ^ 2 := by
  obtain ⟨c, hc, C, hC, _, hbound⟩ := exists_centers_uniform_projected_shifted_leading_bound
    concreteHamiltonian concreteHamiltonian_hermitian
    concreteGroups concreteGroups_hermitian concreteCutoff 1 (by decide)
  refine ⟨c, hc, fun s hs => ?_⟩
  have h := hbound s hs 0 [1] rfl
  rw [hC] at h
  norm_num at h ⊢
  exact h

end QatlibTests.LowEnergyProd24CenteredGroupsConsumer
