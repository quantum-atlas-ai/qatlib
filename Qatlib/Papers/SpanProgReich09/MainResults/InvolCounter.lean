/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # A nonunitary involution refutes the literal legacy Lemma9.6 contract

The paper uses an actual self-adjoint unitary coordinate swap. The old Lean
contract instead required only S*S=1. The 4-by-4 matrix below satisfies every
old hypothesis, with a genuine 4-by-2 isometry, but gives ratio1/5 rather than1/2.
This refutes the weakened legacy model, not the source paper's swap theorem.
-/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators Classical
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.SpanProgReich09.MainResults.InvolCounter

/-- Embed the two coordinates into the first row of the two-by-two product index. -/
def embed : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun p j => if p.1 = 0 ∧ p.2 = j then 1 else 0

/-- An actual involution with reciprocal off-diagonal weights2 and1/2. -/
def invol : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => if p.2 = 0 ∧ q.2 = 0 then
    (if p.1 = 0 ∧ q.1 = 1 then 1 / 2 else if p.1 = 1 ∧ q.1 = 0 then 2 else 0)
  else if p = q ∧ p.2 = 1 then 1 else 0

/-- The first genuine unit vector serves as both the eigenvector and the test state. -/
def alpha : Fin 2 → ℂ := fun i => if i = 0 then 1 else 0

/-- The positive-sign vector in the old target at real eigenvalue zero. -/
def plus : Fin 2 × Fin 2 → ℂ := fun p =>
  (1 - Complex.I) * (embed *ᵥ alpha) p +
    (1 + Complex.I) * (invol *ᵥ (embed *ᵥ alpha)) p

/-- The finite embedding is an actual isometry. -/
theorem embedIsometry : embedᴴ * embed = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [embed, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The weighted matrix is genuinely an involution. -/
theorem involSquared : invol * invol = 1 := by
  apply Matrix.ext
  rintro ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [invol, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The chosen vector is normalized without an empty-domain or zero-state trick. -/
theorem alphaUnit : (∑ i, ‖alpha i‖ ^ 2) = 1 := by
  norm_num [alpha, Fin.sum_univ_two]

/-- The compressed operator has the required zero eigenvalue. -/
theorem compressedZero :
    embedᴴ *ᵥ (invol *ᵥ (embed *ᵥ alpha)) = fun i => (0 : ℂ) * alpha i := by
  ext i
  fin_cases i <;>
    norm_num [embed, invol, alpha, Matrix.mulVec, dotProduct,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The extra pairing hypothesis of the old model also holds exactly. -/
theorem pairingZero : Inner (embed *ᵥ alpha) (invol *ᵥ (embed *ᵥ alpha)) = 0 := by
  norm_num [Qatlib.Foundations.PureStateMath.Inner, embed, invol, alpha, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Fin.sum_univ_two]

/-- The actual numerator and denominator give one fifth. -/
theorem ratioFifth :
    ‖Inner alpha (embedᴴ *ᵥ plus)‖ ^ 2 / (∑ p, ‖plus p‖ ^ 2) = 1 / 5 := by
  norm_num [plus, Qatlib.Foundations.PureStateMath.Inner, embed, invol, alpha, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.sq_norm, Complex.normSq_apply]

/-- The required half-mass identity is false despite all the old hypotheses. -/
theorem ratioNotHalf :
    ‖Inner alpha (embedᴴ *ᵥ plus)‖ ^ 2 / (∑ p, ‖plus p‖ ^ 2) ≠
      (1 / 2) * ‖Inner alpha alpha‖ ^ 2 := by
  rw [ratioFifth]
  norm_num [Qatlib.Foundations.PureStateMath.Inner, alpha, Fin.sum_univ_two]

/-- Every literal legacy premise holds, and its first required equality fails. -/
theorem counterexample :
    |(0 : ℝ)| < 1 ∧ (∑ i, ‖alpha i‖ ^ 2) = 1 ∧
      embedᴴ * embed = 1 ∧ invol * invol = 1 ∧
      (embedᴴ *ᵥ (invol *ᵥ (embed *ᵥ alpha)) = fun i => (0 : ℂ) * alpha i) ∧
      Inner (embed *ᵥ alpha) (invol *ᵥ (embed *ᵥ alpha)) = 0 ∧
      (‖Inner alpha (embedᴴ *ᵥ plus)‖ ^ 2 / (∑ p, ‖plus p‖ ^ 2) ≠
        (1 / 2) * ‖Inner alpha alpha‖ ^ 2) := by
  exact ⟨by norm_num, alphaUnit, embedIsometry, involSquared,
    compressedZero, pairingZero, ratioNotHalf⟩

end Qatlib.Papers.SpanProgReich09.MainResults.InvolCounter
