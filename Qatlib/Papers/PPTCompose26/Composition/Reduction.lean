/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtDecomposition
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Lift
public import Qatlib.Foundations.PPTMatrix.OperatorCones.SeparablePure
public import Qatlib.Foundations.PPTMatrix.OperatorCones.PairLemma

@[expose] public section




/-!
# Reduction of the Schmidt number by a map with separable qubit-reference outputs

* `sum_single_kronecker_block`: an operator on `ℂ^κ ⊗ ℂ^n` is the sum of its blocks
  `E_{ij} ⊗ X_{ij}`.
* `refMap_refConj`: naturality of `id ⊗ Φ` under conjugation by operators on the reference.
* `HasSchmidtNumberLE.refConj`: conjugation on the reference does not increase the Schmidt number.
* `IsSeparable.hasSchmidtNumberLE_one`: separable operators have Schmidt number at most one.
* `hasSchmidtNumberLE_refMap_of_pair`: the core of Lemma 5. If `Θ` is completely positive and
  `id_2 ⊗ Θ` maps positive operators to separable operators, then `id ⊗ Θ` maps operators of
  Schmidt number at most `s` to operators of Schmidt number at most `max (s - 1) 1`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ κ' n p : Type*}

/-! ### Block decomposition and naturality of `id ⊗ Φ` -/

/-- Tensoring with the identity preserves matrix congruence on the first factor. `(L ⊗ 1)(E ⊗ Y)(L ⊗ 1)ᴴ = (L E Lᴴ) ⊗ Y`. -/
theorem kronecker_one_mul_kronecker_mul_conjTranspose [Fintype κ] [Fintype n] [DecidableEq n]
    (L : Matrix κ' κ ℂ) (E : Matrix κ κ ℂ) (Y : Matrix n n ℂ) :
    (L ⊗ₖ (1 : Matrix n n ℂ)) * (E ⊗ₖ Y) * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ = (L * E * Lᴴ) ⊗ₖ Y := by
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- Naturality of `id ⊗ Φ` under conjugation by an operator acting on the reference factor:
`(id ⊗ Φ)((L ⊗ 1) X (L ⊗ 1)ᴴ) = (L ⊗ 1) (id ⊗ Φ)(X) (L ⊗ 1)ᴴ`. -/
theorem refMap_refConj [Fintype κ] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) (L : Matrix κ' κ ℂ) (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ' Φ ((L ⊗ₖ (1 : Matrix n n ℂ)) * X * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ) =
      (L ⊗ₖ (1 : Matrix p p ℂ)) * refMap κ Φ X * (L ⊗ₖ (1 : Matrix p p ℂ))ᴴ := by
  classical
  have key : ∀ (E : Matrix κ κ ℂ) (Y : Matrix n n ℂ),
      refMap κ' Φ ((L ⊗ₖ (1 : Matrix n n ℂ)) * (E ⊗ₖ Y) * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ) =
        (L ⊗ₖ (1 : Matrix p p ℂ)) * refMap κ Φ (E ⊗ₖ Y) * (L ⊗ₖ (1 : Matrix p p ℂ))ᴴ := by
    intro E Y
    rw [kronecker_one_mul_kronecker_mul_conjTranspose, refMap_kronecker, refMap_kronecker,
      kronecker_one_mul_kronecker_mul_conjTranspose]
  rw [sum_single_kronecker_block X]
  simp only [Matrix.mul_sum, Matrix.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key _ _

/-! ### Schmidt number under reference conjugation; separable operators -/

/-- Conjugation by an operator acting on the reference factor does not increase the Schmidt
number. -/
theorem HasSchmidtNumberLE.refConj [Fintype κ] [Fintype n] [DecidableEq n] (L : Matrix κ' κ ℂ)
    {k : ℕ} {X : Matrix (κ × n) (κ × n) ℂ} (h : HasSchmidtNumberLE k X) :
    HasSchmidtNumberLE k ((L ⊗ₖ (1 : Matrix n n ℂ)) * X * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ) := by
  obtain ⟨N, v, hv, rfl⟩ := h
  refine ⟨N, fun α => (L ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v α, fun α => ?_, ?_⟩
  · exact (schmidtRank_kronecker_mulVec_le L (1 : Matrix n n ℂ) (v α)).trans (hv α)
  · exact (sum_pureState_mulVec (L ⊗ₖ (1 : Matrix n n ℂ)) v).symm

/-- Separable operators have Schmidt number at most one. -/
theorem IsSeparable.hasSchmidtNumberLE_one [Fintype κ] [Fintype n]
    {X : Matrix (κ × n) (κ × n) ℂ} (h : IsSeparable X) : HasSchmidtNumberLE 1 X := by
  obtain ⟨N, a, b, hX⟩ := h.isPureProductSum
  have h1 : ∀ i, schmidtRank (prodVec (a i) (b i)) ≤ 1 := fun i => by
    unfold schmidtRank
    rw [coeffMatrix_prodVec]
    exact Qatlib.Foundations.PPTMatrix.OperatorCones.rank_vecMulVec_le_one (a i) (b i)
  have h2 := hasSchmidtNumberLE_sum (fun i => prodVec (a i) (b i)) h1
  have e : X = ∑ i, pureState (prodVec (a i) (b i)) := by
    rw [hX]
    exact Finset.sum_congr rfl fun i _ => (pureState_prodVec (a i) (b i)).symm
  rw [e]
  exact h2

/-! ### The core of Lemma 5 -/

/-- A bipartite vector is determined by its coefficient matrix. -/
theorem eq_of_coeffMatrix_eq {v w : κ × n → ℂ} (h : coeffMatrix v = coeffMatrix w) : v = w := by
  funext x
  obtain ⟨i, a⟩ := x
  have h' := congrFun (congrFun h i) a
  simpa only [coeffMatrix_apply] using h'

/-- The coordinate isometry `ℂ² → ℂ^s` for `2 ≤ s`. -/
theorem exists_coordinate_isometry {s : ℕ} (hs : 2 ≤ s) :
    ∃ V : Matrix (Fin s) (Fin 2) ℂ, Vᴴ * V = 1 := by
  refine ⟨(1 : Matrix (Fin s) (Fin s) ℂ).submatrix id (Fin.castLE hs), ?_⟩
  have h := Matrix.submatrix_mul (1 : Matrix (Fin s) (Fin s) ℂ) (1 : Matrix (Fin s) (Fin s) ℂ)
    (Fin.castLE hs) id (Fin.castLE hs) Function.bijective_id
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, ← h, Matrix.one_mul,
    Matrix.submatrix_one _ (Fin.castLE_injective hs)]

/-- Rank-one case: a completely positive map sends a pure product operator to a separable
operator. -/
theorem hasSchmidtNumberLE_one_refMap_pureState [Fintype κ] [Fintype n] [Fintype p]
    {Θ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hCP : IsCompletelyPositive Θ)
    {v : κ × n → ℂ} (hv : (coeffMatrix v).rank ≤ 1) :
    HasSchmidtNumberLE 1 (refMap κ Θ (pureState v)) := by
  obtain ⟨a, b, hab⟩ := exists_eq_vecMulVec_of_rank_le_one hv
  have ha : (pureState a).PosSemidef := Matrix.posSemidef_vecMulVec_self_star a
  have hb : (pureState b).PosSemidef := Matrix.posSemidef_vecMulVec_self_star b
  rw [pureState_eq_kronecker_of_coeffMatrix hab, refMap_kronecker]
  exact IsSeparable.hasSchmidtNumberLE_one (IsSeparable.kronecker ha (hCP.posSemidef_apply hb))

/-- Full-reference case: on the reference `ℂ^s`, `2 ≤ s`, the lifting lemma applied to the
coordinate isometry `ℂ² → ℂ^s` lowers the Schmidt number to `s - 1`. -/
theorem hasSchmidtNumberLE_refMap_pureState_fin [Fintype n] [DecidableEq n] [Fintype p]
    [DecidableEq p] {Θ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hCP : IsCompletelyPositive Θ)
    (hpair : ∀ X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ, X.PosSemidef →
      IsSeparable (refMap (Fin 2) Θ X))
    {s : ℕ} (hs : 2 ≤ s) (v' : Fin s × n → ℂ) :
    HasSchmidtNumberLE (s - 1) (refMap (Fin s) Θ (pureState v')) := by
  have hP : (pureState v').PosSemidef := Matrix.posSemidef_vecMulVec_self_star v'
  have hSg : (refMap (Fin s) Θ (pureState v')).PosSemidef := hCP s _ hP
  obtain ⟨V₂, hV₂⟩ := exists_coordinate_isometry hs
  have hJc : (V₂ ⊗ₖ (1 : Matrix p p ℂ))ᴴ = V₂ᴴ ⊗ₖ (1 : Matrix p p ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one]
  have hJcc : (V₂ᴴ ⊗ₖ (1 : Matrix p p ℂ))ᴴ = V₂ ⊗ₖ (1 : Matrix p p ℂ) := by
    rw [conjTranspose_kronecker, conjTranspose_one, conjTranspose_conjTranspose]
  have hcomp : (V₂ ⊗ₖ (1 : Matrix p p ℂ))ᴴ * refMap (Fin s) Θ (pureState v') *
      (V₂ ⊗ₖ (1 : Matrix p p ℂ)) =
        refMap (Fin 2) Θ (pureState ((V₂ᴴ ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v')) := by
    have h := refMap_refConj Θ V₂ᴴ (pureState v')
    rw [hJcc] at h
    rw [hJc, pureState_mulVec]
    exact h.symm
  have hQ : (pureState ((V₂ᴴ ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ v')).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  obtain ⟨N, a, b, hab⟩ := (hpair _ hQ).isPureProductSum
  have h := hasSchmidtNumberLE_of_compression hSg hV₂ ⟨N, a, b, hcomp.trans hab⟩
  rwa [Fintype.card_fin] at h

/-- Case `2 ≤ s` of the core of Lemma 5, for one pure operator. -/
theorem hasSchmidtNumberLE_refMap_pureState_of_two_le [Fintype κ] [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {Θ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hCP : IsCompletelyPositive Θ)
    (hpair : ∀ X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ, X.PosSemidef →
      IsSeparable (refMap (Fin 2) Θ X))
    {s : ℕ} (hs : 2 ≤ s) {v : κ × n → ℂ} (hv : (coeffMatrix v).rank ≤ s) :
    HasSchmidtNumberLE (s - 1) (refMap κ Θ (pureState v)) := by
  classical
  by_cases hv1 : (coeffMatrix v).rank ≤ 1
  · exact (hasSchmidtNumberLE_one_refMap_pureState hCP hv1).mono (by omega)
  · have hr : 2 ≤ schmidtRank v := by
      change 2 ≤ (coeffMatrix v).rank
      omega
    obtain ⟨W, v', _hW, hvv⟩ :=
      ManuscriptSchmidt.exists_reference_isometry_of_schmidt v
    rw [hvv, pureState_mulVec, refMap_refConj Θ W (pureState v')]
    exact (HasSchmidtNumberLE.refConj W
      (hasSchmidtNumberLE_refMap_pureState_fin hCP hpair hr v')).mono (by
        change schmidtRank v ≤ s at hv
        omega)

/-- The core of Lemma 5 for one pure operator of Schmidt rank at most `s`. -/
theorem hasSchmidtNumberLE_refMap_pureState_of_pair [Fintype κ] [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] {Θ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hCP : IsCompletelyPositive Θ)
    (hpair : ∀ X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ, X.PosSemidef →
      IsSeparable (refMap (Fin 2) Θ X))
    {s : ℕ} {v : κ × n → ℂ} (hv : schmidtRank v ≤ s) :
    HasSchmidtNumberLE (max (s - 1) 1) (refMap κ Θ (pureState v)) := by
  have hv' : (coeffMatrix v).rank ≤ s := hv
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have hv1 : (coeffMatrix v).rank ≤ 1 := hv'.trans (by omega)
    exact (hasSchmidtNumberLE_one_refMap_pureState hCP hv1).mono (le_max_right _ _)
  · exact (hasSchmidtNumberLE_refMap_pureState_of_two_le hCP hpair hs hv').mono
      (le_max_left _ _)

/-- **Core of Lemma 5.** If `Θ` is completely positive and `id_2 ⊗ Θ` maps positive operators
to separable operators, then `id ⊗ Θ` maps operators of Schmidt number at most `s` to operators
of Schmidt number at most `max (s - 1) 1`. -/
theorem hasSchmidtNumberLE_refMap_of_pair [Fintype κ] [Fintype n] [DecidableEq n] [Fintype p]
    [DecidableEq p] {Θ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hCP : IsCompletelyPositive Θ)
    (hpair : ∀ X : Matrix (Fin 2 × n) (Fin 2 × n) ℂ, X.PosSemidef →
      IsSeparable (refMap (Fin 2) Θ X))
    {s : ℕ} {X : Matrix (κ × n) (κ × n) ℂ} (hX : HasSchmidtNumberLE s X) :
    HasSchmidtNumberLE (max (s - 1) 1) (refMap κ Θ X) := by
  obtain ⟨N, v, hv, rfl⟩ := hX
  rw [map_sum]
  exact HasSchmidtNumberLE.sum _ fun α _ =>
    hasSchmidtNumberLE_refMap_pureState_of_pair hCP hpair (hv α)

end Qatlib.Papers.PPTCompose26.Composition
