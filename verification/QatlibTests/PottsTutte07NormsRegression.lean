module

public import Qatlib.Papers.PottsTutte07.MainResults.CupOperatorNorm

@[expose] public section

/-!
# Concrete consumers for the Potts–Tutte norm increments

The cup-operator consumer uses a two-dimensional nonzero Hilbert space, while the
commutator consumer instantiates the uniform L²-operator bound on `Fin 2`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace QatlibTests.PottsTutte07NormsRegression

open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.PottsTutte07.MainResults

/-- The cup operator used in the concrete consumer. -/
def scaledIdentity : Matrix (Fin 2) (Fin 2) ℂ := (2 : ℂ) • 1

/-- Its adjoint-square relation on the nonempty two-point index type. -/
theorem scaledIdentity_adjoint_square :
    Matrix.conjTranspose scaledIdentity * scaledIdentity =
      ((4 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  rw [scaledIdentity, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  simp
  norm_num

/-- A normalized computational basis vector. -/
noncomputable def cupState : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single (0 : Fin 2) 1

/-- The Euclidean theorem gives squared norm four on the concrete cup instance. -/
theorem cup_operator_euclidean_concrete :
    ‖(EuclideanSpace.equiv (Fin 2) ℂ).symm (Matrix.mulVec scaledIdentity cupState)‖ ^ 2 = 4 := by
  exact lemma10_1_cup_operator_norm_euclidean 4 (by norm_num) scaledIdentity
    scaledIdentity_adjoint_square cupState (by simp [cupState])

/-- The exact norm theorem also has a concrete nondegenerate `Fin 2` consumer. -/
theorem cup_operator_l2_opNorm_concrete : ‖scaledIdentity‖ = 2 := by
  have hResult : ‖scaledIdentity‖ = Real.sqrt 4 :=
    lemma10_1_cup_operator_l2_opNorm (by norm_num) scaledIdentity
      scaledIdentity_adjoint_square
  rw [hResult, Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
  norm_num

/-- The uniform commutator estimate has a concrete `Fin 2` consumer with positive radii. -/
theorem commutator_lipschitz_concrete :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V W Vt Wt : Matrix (Fin 2) (Fin 2) ℂ) (ε δ : ℝ),
        0 < ε → 0 < δ → ε ≤ δ → δ ≤ 1 →
        ‖V - Vt‖ ≤ ε → ‖W - Wt‖ ≤ ε →
        ‖V - 1‖ ≤ δ → ‖W - 1‖ ≤ δ →
        ‖(V * W - W * V) - (Vt * Wt - Wt * Vt)‖ ≤ C * ε * δ :=
  lemmaB_2_commutator_lipschitz_l2_operator

end QatlibTests.PottsTutte07NormsRegression
