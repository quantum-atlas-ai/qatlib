module

import Qatlib.Papers.CollisionLB26.DeleteNorm.CollisionDeletionOperator
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Consumers of the collision deletion norm bound

The examples below instantiate the actual collision deletion matrix at tuple length `3`
(`n = 2`) over four labels and check the row and column counts together with the Euclidean
operator-norm bound.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.CollisionLB26.DeleteNorm

namespace QatlibTests.CollisionLB26DeletionConsumer

/-- A concrete column whose first two coordinates collide. -/
def sampleColumn : NonInjectiveTuple 2 4 := by
  let f : Fin 3 → Fin 4 := ![0, 0, 1]
  refine ⟨f, ?_⟩
  intro hinj
  have heq : f 0 = f 1 := rfl
  exact (by decide : (0 : Fin 3) ≠ 1) (hinj heq)

/-- A concrete row: the zero coordinate together with an injective pair. -/
def sampleRow : CollisionDeletionRow 2 4 :=
  ⟨0, ⟨Fin.castLE (by decide), Fin.castLE_injective (by decide)⟩⟩

/-- The sample column contributes to the sample row after deleting its first coordinate. -/
example : collisionDeletion 2 4 sampleRow sampleColumn ≠ 0 := by
  apply (collisionDeletion_ne_zero_iff sampleRow sampleColumn).2
  funext j
  fin_cases j <;> rfl

/-- Every column of the concrete deletion matrix has at most two nonzero entries. -/
example :
    (Finset.univ.filter
      (fun row : CollisionDeletionRow 2 4 => collisionDeletion 2 4 row sampleColumn ≠ 0)).card
        ≤ 2 :=
  collisionDeletion_col_card_le (by norm_num) sampleColumn

/-- Every row of the concrete deletion matrix has at most two nonzero entries (the tuple length
is three, so the source row bound `s - 1` is two). -/
example :
    (Finset.univ.filter
      (fun col : NonInjectiveTuple 2 4 => collisionDeletion 2 4 sampleRow col ≠ 0)).card ≤ 2 :=
  collisionDeletion_row_card_le (by norm_num) sampleRow

/-- The concrete deletion matrix obeys the source squared action bound with `2 (s - 1) = 4`. -/
example (x : EuclideanSpace ℂ (NonInjectiveTuple 2 4)) :
    ‖(EuclideanSpace.equiv (CollisionDeletionRow 2 4) ℂ).symm
        (collisionDeletion 2 4 *ᵥ WithLp.ofLp x)‖ ^ 2 ≤ (4 : ℝ) * ‖x‖ ^ 2 := by
  have h := collisionDeletion_action_sq_le (n := 2) (N := 4) (by norm_num) (by norm_num) x
  norm_num at h ⊢
  exact h

/-- The concrete deletion matrix has Euclidean operator norm at most `√4 = 2`. -/
example : ‖collisionDeletion 2 4‖ ≤ Real.sqrt ((2 * 2 : ℕ) : ℝ) :=
  collisionDeletion_l2_opNorm_le (n := 2) (N := 4) (by norm_num) (by norm_num)

end QatlibTests.CollisionLB26DeletionConsumer
