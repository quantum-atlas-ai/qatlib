module

import Qatlib.Papers.QLSStatePrep24.WalkQSVT.CyclicQubitizationBlock

/-!
# Consumer checks for the interior cyclic qubitization block

This ordinary module instantiates the new block theorem on a non-degenerate two-level
example: the swap unitary, the embedding of the first coordinate, and the interior
eigenvalue zero.
-/

set_option autoImplicit false
set_option warningAsError true

namespace QatlibTests.QLSStatePrep24CyclicBlockConsumer

open Matrix
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.QLSStatePrep24.WalkQSVT
open scoped Matrix.Norms.L2Operator

/-- The concrete qubitization unitary swaps the two ambient basis vectors. -/
def swapU : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The isometry embeds the one-dimensional input space as the first ambient
coordinate. -/
def firstG : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]

/-- The normalized input state. -/
def zeroPhi : QState (Fin 1) := ![1]

/-- The concrete swap is unitary. -/
theorem swapU_unitary : swapU ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The concrete embedding is an isometry. -/
theorem firstG_isometry : IsIsometry firstG := by
  change firstGᴴ * firstG = 1
  ext i j
  fin_cases i
  fin_cases j
  norm_num [firstG, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The compressed square is the identity and the Hermitian compression has the
normalized input as an eigenvector with eigenvalue zero. -/
theorem cyclic_consumer :
    (firstGᴴ * swapU * firstG).IsHermitian ∧
    firstGᴴ * (swapU ^ 2) * firstG = 1 ∧
    Normalized zeroPhi ∧
    (firstGᴴ * swapU * firstG) *ᵥ zeroPhi = (0 : ℂ) • zeroPhi := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (firstGᴴ * swapU * firstG)ᴴ = firstGᴴ * swapU * firstG
    ext i j
    fin_cases i
    fin_cases j
    norm_num [firstG, swapU, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [firstG, swapU, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  · norm_num [Normalized, zeroPhi]
  · funext i
    fin_cases i
    norm_num [firstG, swapU, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, zeroPhi]

/-- The ordinary consumer sees that the boundary-inclusive two-level block has L2
operator norm one. -/
example : ‖cyclicBlock 0‖ = 1 :=
  cyclicBlock_l2Operator_norm (by norm_num)

/-- The ordinary consumer sees the concrete swap action on the embedded vector and its
residual. -/
example :
    swapU *ᵥ (firstG *ᵥ zeroPhi) =
      (0 : ℂ) • (firstG *ᵥ zeroPhi) +
      (Real.sqrt (1 - (0 : ℝ) ^ 2) : ℂ) • residual swapU (firstG *ᵥ zeroPhi) 0 ∧
    swapU *ᵥ residual swapU (firstG *ᵥ zeroPhi) 0 =
      (Real.sqrt (1 - (0 : ℝ) ^ 2) : ℂ) • (firstG *ᵥ zeroPhi) -
      (0 : ℂ) • residual swapU (firstG *ᵥ zeroPhi) 0 :=
  cyclic_qubitization_interior_block_action
    (Fin 2) (Fin 1) swapU firstG zeroPhi 0
    swapU_unitary firstG_isometry cyclic_consumer.1 cyclic_consumer.2.1
    cyclic_consumer.2.2.1 cyclic_consumer.2.2.2 (by norm_num)

/-- The same concrete inputs give a matrix intertwining identity and the operator norm
of its two-level block. -/
example :
    let B := cyclicBlockColumns swapU (firstG *ᵥ zeroPhi) 0
    swapU * B = B * cyclicBlock 0 ∧ ‖cyclicBlock 0‖ = 1 :=
  cyclic_qubitization_interior_block
    (Fin 2) (Fin 1) swapU firstG zeroPhi 0
    swapU_unitary firstG_isometry cyclic_consumer.1 cyclic_consumer.2.1
    cyclic_consumer.2.2.1 cyclic_consumer.2.2.2 (by norm_num)

end QatlibTests.QLSStatePrep24CyclicBlockConsumer
