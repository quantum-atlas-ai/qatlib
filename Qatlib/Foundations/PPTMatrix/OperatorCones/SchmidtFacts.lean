/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtNumber
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.RankFactorization

@[expose] public section




/-!
# Consequences of the definition of the Schmidt number

* a positive operator on `ℂ^κ ⊗ ℂ^n` has Schmidt number at most `min {|κ|, |n|}`;
* the Schmidt number of a sum of positive operators is at most the largest Schmidt number;
* Schmidt number at most one implies separability.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*} [Fintype κ] [Fintype n]

/-- Every positive operator is a sum of pure operators, whose Schmidt ranks are at most the
smaller local dimension. -/
theorem hasSchmidtNumberLE_min_card {X : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef) :
    HasSchmidtNumberLE (min (Fintype.card κ) (Fintype.card n)) X := by
  obtain ⟨N, v, rfl⟩ := exists_sum_vecMulVec_of_posSemidef hX
  exact ⟨N, v, fun α => le_min (Matrix.rank_le_card_height (coeffMatrix (v α)))
    (Matrix.rank_le_card_width (coeffMatrix (v α))), rfl⟩

/-- Establishes `schmidtNumber_le_min_card`: `schmidtNumber X ≤ min (Fintype.card κ) (Fintype.card n)`, for the stated parameters. -/
theorem schmidtNumber_le_min_card {X : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef) :
    schmidtNumber X ≤ min (Fintype.card κ) (Fintype.card n) :=
  schmidtNumber_le (hasSchmidtNumberLE_min_card hX)

/-- The Schmidt number of a sum of positive operators is at most the largest of their Schmidt
numbers. -/
theorem schmidtNumber_add_le {X Y : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) : schmidtNumber (X + Y) ≤ max (schmidtNumber X) (schmidtNumber Y) := by
  have hX' := hasSchmidtNumberLE_schmidtNumber (hasSchmidtNumberLE_min_card hX)
  have hY' := hasSchmidtNumberLE_schmidtNumber (hasSchmidtNumberLE_min_card hY)
  exact schmidtNumber_le ((hX'.mono (le_max_left _ _)).add (hY'.mono (le_max_right _ _)))

omit [Fintype κ] [Fintype n] in
/-- A vector whose coefficient matrix is `a bᵀ` is the product vector `a ⊗ b`. -/
theorem pureState_eq_kronecker_of_coeffMatrix {v : κ × n → ℂ} {a : κ → ℂ} {b : n → ℂ}
    (h : coeffMatrix v = Matrix.vecMulVec a b) : pureState v = pureState a ⊗ₖ pureState b := by
  have hv : ∀ i j, v (i, j) = a i * b j := fun i j => by
    have h' := congrFun (congrFun h i) j
    simpa [Matrix.vecMulVec_apply] using h'
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [pureState, Matrix.vecMulVec_apply, Pi.star_apply, kroneckerMap_apply, hv, star_mul']
  ring

/-- Schmidt number at most one implies separability. -/
theorem IsSeparable.of_hasSchmidtNumberLE_one {X : Matrix (κ × n) (κ × n) ℂ}
    (h : HasSchmidtNumberLE 1 X) : IsSeparable X := by
  obtain ⟨N, v, hv, rfl⟩ := h
  refine IsSeparable.sum _ fun α _ => ?_
  obtain ⟨a, b, hab⟩ := exists_eq_vecMulVec_of_rank_le_one (V := coeffMatrix (v α)) (hv α)
  rw [pureState_eq_kronecker_of_coeffMatrix hab]
  exact IsSeparable.kronecker (Matrix.posSemidef_vecMulVec_self_star a)
    (Matrix.posSemidef_vecMulVec_self_star b)

/-- `SN(X) = 1` implies that `X` is separable. -/
theorem IsSeparable.of_schmidtNumber_eq_one {X : Matrix (κ × n) (κ × n) ℂ}
    (h : schmidtNumber X = 1) : IsSeparable X := by
  unfold schmidtNumber at h
  have hne : {k | HasSchmidtNumberLE k X}.Nonempty := Nat.nonempty_of_pos_sInf (by omega)
  have hmem := Nat.sInf_mem hne
  rw [h] at hmem
  exact IsSeparable.of_hasSchmidtNumberLE_one hmem

end Qatlib.Foundations.PPTMatrix.OperatorCones
