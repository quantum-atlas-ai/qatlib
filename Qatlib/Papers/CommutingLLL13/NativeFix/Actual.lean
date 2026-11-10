/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.ProjectiveFix.ShortRun
import Qatlib.Papers.CommutingLLL13.NativeFix.Bits
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators Matrix Kronecker ComplexOrder
namespace Qatlib.Papers.CommutingLLL13.NativeFix
open Qatlib.Foundations.MatrixAlgebra.ProjectiveFix
noncomputable section

abbrev Qubit := Fin 2 × Fin 1

def qubitProjector : Projector Qubit where
  val := Matrix.diagonal (fun x => if x.1 = 1 then 1 else 0)
  hermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro x
    split_ifs <;> simp
  idem := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext x
    split_ifs <;> norm_num

def qubitInput : Matrix Qubit Qubit ℂ := qubitProjector.val

def qubitGround : Matrix Qubit Qubit ℂ :=
  Matrix.diagonal (fun x => if x.1 = 0 then 1 else 0)

theorem qubitInput_density : qubitInput.PosSemidef ∧ qubitInput.trace = 1 := by
  refine ⟨projector_pos qubitProjector, ?_⟩
  norm_num [qubitInput, qubitProjector, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]
  decide

theorem qubit_violated : branch qubitProjector true qubitInput = qubitInput := by
  simp only [branch, outcome, ↓reduceIte, qubitInput, qubitProjector.hermitian.eq,
    qubitProjector.idem]

theorem qubit_reset : violatedReset qubitProjector qubitInput =
    (1 / 2 : ℝ) • (1 : Matrix Qubit Qubit ℂ) := by
  unfold violatedReset
  rw [qubit_violated]
  ext x y
  rw [localReset_entry]
  rcases x with ⟨x, x'⟩
  rcases y with ⟨y, y'⟩
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y'
  all_goals norm_num [qubitInput, qubitProjector, Fin.sum_univ_two, Matrix.one_apply]

theorem qubit_output :
    zeroRun (fun _ : Fin 1 => qubitProjector) [0]
      (violatedReset qubitProjector qubitInput) = (1 / 2 : ℝ) • qubitGround := by
  rw [qubit_reset]
  simp only [zeroRun, List.foldl_cons, List.foldl_nil]
  ext x y
  rcases x with ⟨x, x'⟩
  rcases y with ⟨y, y'⟩
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y'
  all_goals norm_num [branch, outcome, qubitProjector, qubitGround,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fin.sum_univ_one, Matrix.one_apply, Matrix.diagonal_apply]

theorem qubit_execution :
    let W := zeroRun (fun _ : Fin 1 => qubitProjector) [0]
      (violatedReset qubitProjector qubitInput)
    W.trace = (1 / 2 : ℂ) ∧ (normalize W).PosSemidef ∧
      (normalize W).trace = 1 ∧ qubitProjector.val * normalize W = 0 := by
  (try dsimp only)
  have ht : (zeroRun (fun _ : Fin 1 => qubitProjector) [0]
      (violatedReset qubitProjector qubitInput)).trace = (1 / 2 : ℂ) := by
    rw [qubit_output]
    norm_num [Matrix.trace_smul, qubitGround, Matrix.trace, Matrix.diag,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]
  have hs := short_execution (fun _ : Fin 1 => qubitProjector)
    (fun _ _ => rfl) 0 [0] (fun j => by fin_cases j; simp)
    qubitInput qubitInput_density.1 (by rw [ht]; norm_num)
  exact ⟨ht, hs.1, hs.2.1, hs.2.2 0⟩

end
end Qatlib.Papers.CommutingLLL13.NativeFix
