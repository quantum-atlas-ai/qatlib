/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.PairLemma

@[expose] public section




/-!
# Tensor products and congruences of completely positive maps

The tensor product here is a map on actual product-indexed matrices. It applies
the second map blockwise, swaps the factors, applies the first map blockwise,
and swaps back. Its action on Kronecker products is proved explicitly.

Complete positivity is transported through genuine coordinate changes and
finite reference extensions. Congruence maps provide actual matrix embeddings
and compressions that can be consumed independently of a particular channel family.
No trace-preservation, unitality, or invertibility is assumed.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ κ' n m p q r : Type*}

/-- Pull a matrix back along the same coordinate function on its two indices. -/
def submatrixMap (f : p → n) : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ where
  toFun X := X.submatrix f f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Establishes `submatrixMap_apply`: `submatrixMap f X = X.submatrix f f`, for the stated parameters. -/
@[simp]
theorem submatrixMap_apply (f : p → n) (X : Matrix n n ℂ) :
    submatrixMap f X = X.submatrix f f := rfl

/-- Establishes `refMap_submatrixMap`: `refMap κ (submatrixMap f) X = X.submatrix (Prod.map id f) (Prod.map id f)`, for the stated parameters. -/
theorem refMap_submatrixMap (f : p → n) (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (submatrixMap f) X =
      X.submatrix (Prod.map id f) (Prod.map id f) := rfl

/-- Coordinate restrictions and permutations are completely positive. -/
theorem isCompletelyPositive_submatrixMap (f : p → n) :
    IsCompletelyPositive (submatrixMap f) := by
  intro k X hX
  rw [refMap_submatrixMap]
  exact hX.submatrix _

/-- Establishes `refMap_refSubmatrix`: `refMap κ' Φ (X.submatrix (Prod.map f id) (Prod.map f id)) = (refMap κ Φ X).submatrix (Prod.map f id) (Prod.map f id)`, for the stated parameters. -/
theorem refMap_refSubmatrix (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) (f : κ' → κ) :
    refMap κ' Φ (X.submatrix (Prod.map f id) (Prod.map f id)) =
      (refMap κ Φ X).submatrix (Prod.map f id) (Prod.map f id) := rfl

/-- The definition using `Fin k` references extends to every finite reference type. -/
theorem IsCompletelyPositive.posSemidef_refMap [Fintype κ]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsCompletelyPositive Φ)
    {X : Matrix (κ × n) (κ × n) ℂ} (hX : X.PosSemidef) :
    (refMap κ Φ X).PosSemidef := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have h := hΦ (Fintype.card κ) _
    (hX.submatrix (Prod.map e.symm id))
  rw [refMap_refSubmatrix] at h
  have h' := h.submatrix (Prod.map e id)
  have heq : ((refMap κ Φ X).submatrix (Prod.map e.symm id) (Prod.map e.symm id)).submatrix
      (Prod.map e id) (Prod.map e id) = refMap κ Φ X := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp
  exact heq ▸ h'

/-- Adding a finite untouched factor preserves complete positivity. -/
theorem IsCompletelyPositive.refMap [Fintype κ]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsCompletelyPositive Φ) :
    IsCompletelyPositive (refMap κ Φ) := by
  intro k X hX
  have h := hΦ.posSemidef_refMap
    (hX.submatrix (Equiv.prodAssoc (Fin k) κ n))
  exact h.submatrix (Equiv.prodAssoc (Fin k) κ p).symm

/-- Swapping the two actual matrix factors swaps a Kronecker product. -/
theorem submatrixMap_swap_kronecker (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    submatrixMap Prod.swap (A ⊗ₖ B) = B ⊗ₖ A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply, mul_comm]

/-- The tensor product of rectangular matrix maps, defined by two reference
extensions and the two coordinate permutations exchanging the factors. -/
def tensorMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ) :
    Matrix (n × m) (n × m) ℂ →ₗ[ℂ] Matrix (p × q) (p × q) ℂ :=
  submatrixMap Prod.swap ∘ₗ
    (refMap q Φ ∘ₗ (submatrixMap Prod.swap ∘ₗ refMap n Ψ))

/-- The entry formula makes both factor actions explicit on arbitrary inputs. -/
theorem tensorMap_apply (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ)
    (X : Matrix (n × m) (n × m) ℂ) (i j : p) (a b : q) :
    tensorMap Φ Ψ X (i, a) (j, b) =
      Φ (fun u v => Ψ (block X u v) a b) i j := rfl

/-- This is the usual tensor action on elementary tensor matrices. -/
theorem tensorMap_kronecker (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ)
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    tensorMap Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by
  simp only [tensorMap, LinearMap.comp_apply, refMap_kronecker,
    submatrixMap_swap_kronecker]

/-- Tensor products of completely positive maps are completely positive. -/
theorem IsCompletelyPositive.tensorMap [Fintype n] [Fintype q]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    {Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ}
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (tensorMap Φ Ψ) :=
  (isCompletelyPositive_submatrixMap Prod.swap).comp
    (hΦ.refMap.comp ((isCompletelyPositive_submatrixMap Prod.swap).comp hΨ.refMap))

/-- Global output transpose is the tensor of the two output-transposed maps. -/
theorem transposeMap_comp_tensorMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ) :
    transposeMap (p × q) ∘ₗ tensorMap Φ Ψ =
      tensorMap (transposeMap p ∘ₗ Φ) (transposeMap q ∘ₗ Ψ) := by
  apply LinearMap.ext
  intro X
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

/-- Tensor products preserve the conjunction of complete positivity and complete
copositivity, with no trace or normalization requirements. -/
theorem IsPPTMap.tensorMap [Fintype n] [Fintype q]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    {Ψ : Matrix m m ℂ →ₗ[ℂ] Matrix q q ℂ}
    (hΦ : IsPPTMap Φ) (hΨ : IsPPTMap Ψ) : IsPPTMap (tensorMap Φ Ψ) := by
  refine ⟨hΦ.1.tensorMap hΨ.1, ?_⟩
  unfold IsCompletelyCopositive
  rw [transposeMap_comp_tensorMap]
  exact IsCompletelyPositive.tensorMap hΦ.2 hΨ.2

/-- Congruence by an actual rectangular complex matrix. -/
def congruenceMap [Fintype n] (K : Matrix p n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ where
  toFun X := K * X * Kᴴ
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

/-- Establishes `congruenceMap_apply`: `congruenceMap K X = K * X * Kᴴ`, for the stated parameters. -/
@[simp]
theorem congruenceMap_apply [Fintype n] (K : Matrix p n ℂ) (X : Matrix n n ℂ) :
    congruenceMap K X = K * X * Kᴴ := rfl

/-- Coordinate pullback is genuine congruence by the corresponding rows of the
identity matrix. For an equivalence this is permutation conjugacy. -/
theorem submatrixMap_eq_congruenceMap [Fintype n] [DecidableEq n] (f : p → n) :
    submatrixMap f = congruenceMap ((1 : Matrix n n ℂ).submatrix f id) := by
  apply LinearMap.ext
  intro X
  change X.submatrix f f =
    (1 : Matrix n n ℂ).submatrix f id * X *
      ((1 : Matrix n n ℂ).submatrix f id)ᴴ
  rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
  change X.submatrix f f =
    (1 : Matrix n n ℂ).submatrix f (Equiv.refl n) * X *
      (1 : Matrix n n ℂ).submatrix (Equiv.refl n) f
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
  rfl

/-- Extending a congruence map gives the actual congruence by `I ⊗ K`. -/
theorem refMap_congruenceMap [Fintype κ] [DecidableEq κ] [Fintype n]
    (K : Matrix p n ℂ) (X : Matrix (κ × n) (κ × n) ℂ) :
    refMap κ (congruenceMap K) X =
      ((1 : Matrix κ κ ℂ) ⊗ₖ K) * X * ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ := by
  have key : ∀ (E : Matrix κ κ ℂ) (Y : Matrix n n ℂ),
      refMap κ (congruenceMap K) (E ⊗ₖ Y) =
        ((1 : Matrix κ κ ℂ) ⊗ₖ K) * (E ⊗ₖ Y) *
          ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ := by
    intro E Y
    rw [refMap_kronecker, congruenceMap_apply]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
  rw [sum_single_kronecker_block X]
  simp only [map_sum, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key _ _

/-- Establishes `isCompletelyPositive_congruenceMap`: `IsCompletelyPositive (congruenceMap K)`, for the stated parameters. -/
theorem isCompletelyPositive_congruenceMap [Fintype n] [Finite p] (K : Matrix p n ℂ) :
    IsCompletelyPositive (congruenceMap K) := by
  intro k X hX
  rw [refMap_congruenceMap]
  exact hX.mul_mul_conjTranspose_same _

/-- Transposing an output congruence conjugates the entries of its matrix. -/
theorem transposeMap_comp_congruenceMap [Fintype n] (K : Matrix p n ℂ) :
    transposeMap p ∘ₗ congruenceMap K =
      congruenceMap (K.map star) ∘ₗ transposeMap n := by
  have hK : (K.map star)ᴴ = Kᵀ := by
    ext i j
    simp
  apply LinearMap.ext
  intro X
  change (K * X * Kᴴ)ᵀ = K.map star * Xᵀ * (K.map star)ᴴ
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.conjTranspose_transpose,
    hK, Matrix.mul_assoc]

/-- Congruence on the output preserves PPT. -/
theorem IsPPTMap.congruence_comp [Fintype p] [Finite q]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsPPTMap Φ)
    (K : Matrix q p ℂ) : IsPPTMap (congruenceMap K ∘ₗ Φ) := by
  refine ⟨(isCompletelyPositive_congruenceMap K).comp hΦ.1, ?_⟩
  unfold IsCompletelyCopositive
  rw [← LinearMap.comp_assoc, transposeMap_comp_congruenceMap, LinearMap.comp_assoc]
  exact (isCompletelyPositive_congruenceMap (K.map star)).comp hΦ.2

/-- Congruence on the input preserves PPT. -/
theorem IsPPTMap.comp_congruence [Fintype m] [Finite n]
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΦ : IsPPTMap Φ)
    (K : Matrix n m ℂ) : IsPPTMap (Φ ∘ₗ congruenceMap K) :=
  ⟨hΦ.1.comp (isCompletelyPositive_congruenceMap K),
    hΦ.2.comp_isCompletelyPositive (isCompletelyPositive_congruenceMap K)⟩

end Qatlib.Foundations.PPTMatrix.OperatorCones
