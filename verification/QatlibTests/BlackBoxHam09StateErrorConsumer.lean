module

public import Qatlib.Papers.BlackBoxHam09.MainResults.StateError
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

@[expose] public section

/-!
# Concrete Euclidean consumer for the BlackBoxHam09 state-error increment

The two-level Hamiltonian is Pauli-X, the rounding profile is nonzero but below the state
preparation tolerance, and the input is the first Euclidean basis vector. The consumer applies
the uniform Lemma 7 theorem at a genuinely two-dimensional, nonempty instance.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace QatlibTests.BlackBoxHam09StateErrorConsumer

open Matrix
open Qatlib.Papers.BlackBoxHam09.MainResults.Defs
open Qatlib.Papers.BlackBoxHam09.MainResults
open scoped Matrix.Norms.L2Operator

private def flip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli-X is unitary. -/
private theorem flip_unitary : flip ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flip, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Matrix.one_apply]

/-- Pauli-X supplies a nonzero two-level Hamiltonian. -/
private def flipHamiltonian : Ham (Fin 2) where
  mat := flip
  herm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [flip, Matrix.conjTranspose_apply]

/-- The Euclidean operator norm of the Pauli-X Hamiltonian is one. -/
private theorem flipHamiltonian_norm :
    spectralNorm flipHamiltonian = 1 := by
  unfold spectralNorm flipHamiltonian
  exact Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_unitary_eq_one flip_unitary

private def rounding : Fin 2 → ℝ := fun _ => 1 / 20

/-- The concrete rounding profile is within the tolerance `1/10`. -/
private theorem maxAbs_rounding_le :
    maxAbs rounding ≤ 1 / 10 := by
  unfold maxAbs rounding
  simp [Pi.norm_def]
  rw [Finset.sup_const (by simp)]
  norm_num

private def inputState : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(1 : ℂ), 0]

/-- The concrete consumer input has Euclidean norm one. -/
private theorem inputState_norm : ‖inputState‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [inputState, Fin.sum_univ_two]

/-- Apply the uniform Lemma 7 estimate to Pauli-X, a nonzero rounding profile, positive norm
bound, positive time, and a normalized two-dimensional Euclidean state. -/
example :
    ∃ C : ℝ, 0 < C ∧
      (1 * 2 / (1 / 10) : ℝ) *
        ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm
          (((1 / 10 / 2 : ℝ) • sandwich flipHamiltonian rounding) *ᵥ inputState)‖ ≤
        C * (1 / 10) := by
  obtain ⟨C, hC, hbound⟩ := lemma7_uniform_state_error
  refine ⟨C, hC, ?_⟩
  simpa only [flipHamiltonian_norm, inputState_norm, mul_one] using
    hbound flipHamiltonian rounding (1 / 10) 2 1
    (by norm_num) (by norm_num) maxAbs_rounding_le (by norm_num) (by norm_num) inputState

end QatlibTests.BlackBoxHam09StateErrorConsumer
