/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Defs

@[expose] public section




/-!
# Basic properties of `id ⊗ Φ`, complete positivity and separability

Closure properties used throughout the development: functoriality of `refMap`, closure of
completely positive / completely copositive / PPT maps under composition, and closure of
separable operators under sums and local conjugations.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ κ' n n' p q : Type*}

/-! ### `refMap` -/

/-- An operator is the finite sum of the elementary reference matrices tensored with its blocks. -/
theorem sum_single_kronecker_block [Fintype κ] [DecidableEq κ] (X : Matrix (κ × n) (κ × n) ℂ) :
    X = ∑ i, ∑ j, Matrix.single i j (1 : ℂ) ⊗ₖ block X i j := by
  ext ⟨a, x⟩ ⟨b, y⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply, block_apply]
  rw [Fintype.sum_eq_single a, Fintype.sum_eq_single b]
  · simp
  · intro j hj
    simp [hj]
  · intro i hi
    simp [hi]

/-- Establishes `block_kronecker`: `block (A ⊗ₖ B) i j = A i j • B`, for the stated parameters. -/
theorem block_kronecker (A : Matrix κ κ ℂ) (B : Matrix n n ℂ) (i j : κ) :
    block (A ⊗ₖ B) i j = A i j • B := by
  ext a b
  simp

/-- Establishes `block_refMap`: `block (refMap κ Φ X) i j = Φ (block X i j)`, for the stated parameters. -/
theorem block_refMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) (X : Matrix (κ × n) (κ × n) ℂ)
    (i j : κ) : block (refMap κ Φ X) i j = Φ (block X i j) := by
  ext a b
  simp

/-- `(id ⊗ Φ)(A ⊗ B) = A ⊗ Φ(B)`. -/
theorem refMap_kronecker (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) (A : Matrix κ κ ℂ)
    (B : Matrix n n ℂ) : refMap κ Φ (A ⊗ₖ B) = A ⊗ₖ Φ B := by
  ext x y
  simp [block_kronecker]

/-- Establishes `refMap_id`: `refMap κ (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) = LinearMap.id`, for the stated parameters. -/
theorem refMap_id :
    refMap κ (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  ext x y
  simp

/-- Establishes `refMap_comp`: `refMap κ (Ψ ∘ₗ Φ) = refMap κ Ψ ∘ₗ refMap κ Φ`, for the stated parameters. -/
theorem refMap_comp (Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) :
    refMap κ (Ψ ∘ₗ Φ) = refMap κ Ψ ∘ₗ refMap κ Φ := by
  refine LinearMap.ext fun X => ?_
  ext x y
  simp [block_refMap]

/-! ### Complete positivity -/

/-- Establishes `isCompletelyPositive_id`: `IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)`, for the stated parameters. -/
theorem isCompletelyPositive_id :
    IsCompletelyPositive (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := by
  intro k X hX
  simpa [refMap_id] using hX

/-- Establishes `IsCompletelyPositive.comp`: `IsCompletelyPositive (Ψ ∘ₗ Φ)`, for the stated parameters. -/
theorem IsCompletelyPositive.comp {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ}
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsCompletelyPositive Ψ)
    (hΦ : IsCompletelyPositive Φ) : IsCompletelyPositive (Ψ ∘ₗ Φ) := by
  intro k X hX
  rw [refMap_comp, LinearMap.comp_apply]
  exact hΨ k _ (hΦ k X hX)

/-- A completely copositive map after a completely positive map is completely copositive. -/
theorem IsCompletelyCopositive.comp_isCompletelyPositive {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ}
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsCompletelyCopositive Ψ)
    (hΦ : IsCompletelyPositive Φ) : IsCompletelyCopositive (Ψ ∘ₗ Φ) := by
  unfold IsCompletelyCopositive at hΨ ⊢
  rw [← LinearMap.comp_assoc]
  exact hΨ.comp hΦ

/-- PPT maps are closed under composition. -/
theorem IsPPTMap.comp {Ψ : Matrix p p ℂ →ₗ[ℂ] Matrix q q ℂ}
    {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ} (hΨ : IsPPTMap Ψ) (hΦ : IsPPTMap Φ) :
    IsPPTMap (Ψ ∘ₗ Φ) :=
  ⟨hΨ.1.comp hΦ.1, hΨ.2.comp_isCompletelyPositive hΦ.1⟩

/-! ### Separable operators -/

/-- A sum of products of positive operators over any finite index type is separable. -/
theorem isSeparable_sum_kronecker {ι : Type*} [Fintype ι] (A : ι → Matrix κ κ ℂ)
    (B : ι → Matrix n n ℂ) (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) :
    IsSeparable (∑ i, A i ⊗ₖ B i) := by
  classical
  refine ⟨Fintype.card ι, fun j => A ((Fintype.equivFin ι).symm j),
    fun j => B ((Fintype.equivFin ι).symm j), fun j => hA _, fun j => hB _, ?_⟩
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => A i ⊗ₖ B i)).symm

/-- Establishes `IsSeparable.zero`: `IsSeparable (0 : Matrix (κ × n) (κ × n) ℂ)`, for the stated parameters. -/
theorem IsSeparable.zero : IsSeparable (0 : Matrix (κ × n) (κ × n) ℂ) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- Establishes `IsSeparable.kronecker`: `IsSeparable (A ⊗ₖ B)`, for the stated parameters. -/
theorem IsSeparable.kronecker {A : Matrix κ κ ℂ} {B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : IsSeparable (A ⊗ₖ B) :=
  ⟨1, fun _ => A, fun _ => B, fun _ => hA, fun _ => hB, by simp⟩

/-- Establishes `IsSeparable.add`: `IsSeparable (X + Y)`, for the stated parameters. -/
theorem IsSeparable.add {X Y : Matrix (κ × n) (κ × n) ℂ} (hX : IsSeparable X)
    (hY : IsSeparable Y) : IsSeparable (X + Y) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := hX
  obtain ⟨N', A', B', hA', hB', rfl⟩ := hY
  have h := isSeparable_sum_kronecker (ι := Fin N ⊕ Fin N') (Sum.elim A A') (Sum.elim B B')
    (by rintro (i | i) <;> simp [hA, hA']) (by rintro (i | i) <;> simp [hB, hB'])
  simpa [Fintype.sum_sum_type] using h

/-- Establishes `IsSeparable.sum`: `IsSeparable (∑ i ∈ s, X i)`, for the stated parameters. -/
theorem IsSeparable.sum {ι : Type*} (s : Finset ι) {X : ι → Matrix (κ × n) (κ × n) ℂ}
    (h : ∀ i ∈ s, IsSeparable (X i)) : IsSeparable (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsSeparable.zero : IsSeparable (0 : Matrix (κ × n) (κ × n) ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Separable operators are positive. -/
theorem IsSeparable.posSemidef [Finite κ] [Finite n] {X : Matrix (κ × n) (κ × n) ℂ}
    (h : IsSeparable X) : X.PosSemidef := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := h
  exact Matrix.posSemidef_sum _ fun i _ => (hA i).kronecker (hB i)

/-- Conjugation by an operator acting on the reference factor preserves separability. -/
theorem IsSeparable.refConj [Fintype κ] [Finite κ'] [Fintype n] [DecidableEq n]
    (L : Matrix κ' κ ℂ) {X : Matrix (κ × n) (κ × n) ℂ} (h : IsSeparable X) :
    IsSeparable ((L ⊗ₖ (1 : Matrix n n ℂ)) * X * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := h
  have key : (L ⊗ₖ (1 : Matrix n n ℂ)) * (∑ i, A i ⊗ₖ B i) * (L ⊗ₖ (1 : Matrix n n ℂ))ᴴ =
      ∑ i, (L * A i * Lᴴ) ⊗ₖ B i := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
  rw [key]
  exact isSeparable_sum_kronecker _ _ (fun i => (hA i).mul_mul_conjTranspose_same L) hB

/-- Conjugation by an operator acting on the system factor preserves separability. -/
theorem IsSeparable.sysConj [Fintype κ] [DecidableEq κ] [Fintype n] [Finite n']
    (K : Matrix n' n ℂ) {X : Matrix (κ × n) (κ × n) ℂ} (h : IsSeparable X) :
    IsSeparable (((1 : Matrix κ κ ℂ) ⊗ₖ K) * X * ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ) := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := h
  have key : ((1 : Matrix κ κ ℂ) ⊗ₖ K) * (∑ i, A i ⊗ₖ B i) * ((1 : Matrix κ κ ℂ) ⊗ₖ K)ᴴ =
      ∑ i, A i ⊗ₖ (K * B i * Kᴴ) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one]
  rw [key]
  exact isSeparable_sum_kronecker _ _ hA (fun i => (hB i).mul_mul_conjTranspose_same K)

end Qatlib.Foundations.PPTMatrix.OperatorCones
