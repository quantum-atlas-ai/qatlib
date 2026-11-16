/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.SchmidtFacts

@[expose] public section




/-!
# Separable operators are finite sums of pure product operators

"A separable operator can be written as a finite sum of operators `P_a ⊗ P_b`" (manuscript,
paragraph before the proof of Theorem 1), and conversely.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*}

/-- `X` is a finite sum of pure product operators `P_a ⊗ P_b`. -/
def IsPureProductSum (X : Matrix (κ × n) (κ × n) ℂ) : Prop :=
  ∃ (N : ℕ) (a : Fin N → κ → ℂ) (b : Fin N → n → ℂ),
    X = ∑ i, pureState (a i) ⊗ₖ pureState (b i)

/-- Establishes `isPureProductSum_of_fintype`: `IsPureProductSum (∑ i, pureState (a i) ⊗ₖ pureState (b i))`, for the stated parameters. -/
theorem isPureProductSum_of_fintype {ι : Type*} [Fintype ι] (a : ι → κ → ℂ) (b : ι → n → ℂ) :
    IsPureProductSum (∑ i, pureState (a i) ⊗ₖ pureState (b i)) := by
  classical
  exact ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j),
    fun j => b ((Fintype.equivFin ι).symm j),
    (Equiv.sum_comp (Fintype.equivFin ι).symm
      (fun i => pureState (a i) ⊗ₖ pureState (b i))).symm⟩

/-- Establishes `IsPureProductSum.zero`: `IsPureProductSum (0 : Matrix (κ × n) (κ × n) ℂ)`, for the stated parameters. -/
theorem IsPureProductSum.zero : IsPureProductSum (0 : Matrix (κ × n) (κ × n) ℂ) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- Establishes `IsPureProductSum.add`: `IsPureProductSum (X + Y)`, for the stated parameters. -/
theorem IsPureProductSum.add {X Y : Matrix (κ × n) (κ × n) ℂ} (hX : IsPureProductSum X)
    (hY : IsPureProductSum Y) : IsPureProductSum (X + Y) := by
  obtain ⟨N, a, b, rfl⟩ := hX
  obtain ⟨N', a', b', rfl⟩ := hY
  have h := isPureProductSum_of_fintype (ι := Fin N ⊕ Fin N') (Sum.elim a a') (Sum.elim b b')
  simpa [Fintype.sum_sum_type] using h

/-- Establishes `kronecker_sum_sum`: `(∑ k, A k) ⊗ₖ (∑ l, B l) = ∑ x : Fin K × Fin L, A x.1 ⊗ₖ B x.2`, for the stated parameters. -/
theorem kronecker_sum_sum {K L : ℕ} (A : Fin K → Matrix κ κ ℂ) (B : Fin L → Matrix n n ℂ) :
    (∑ k, A k) ⊗ₖ (∑ l, B l) = ∑ x : Fin K × Fin L, A x.1 ⊗ₖ B x.2 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.sum_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]

/-- Establishes `isPureProductSum_kronecker`: `IsPureProductSum (A ⊗ₖ B)`, for the stated parameters. -/
theorem isPureProductSum_kronecker [Fintype κ] [Fintype n] {A : Matrix κ κ ℂ}
    {B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) : IsPureProductSum (A ⊗ₖ B) := by
  obtain ⟨K, a, rfl⟩ := exists_sum_vecMulVec_of_posSemidef hA
  obtain ⟨L, b, rfl⟩ := exists_sum_vecMulVec_of_posSemidef hB
  rw [kronecker_sum_sum]
  exact isPureProductSum_of_fintype (fun x : Fin K × Fin L => a x.1) (fun x => b x.2)

/-- A separable operator is a finite sum of pure product operators. -/
theorem IsSeparable.isPureProductSum [Fintype κ] [Fintype n] {X : Matrix (κ × n) (κ × n) ℂ}
    (h : IsSeparable X) : IsPureProductSum X := by
  obtain ⟨M, A, B, hA, hB, rfl⟩ := h
  exact Finset.sum_induction _ IsPureProductSum (fun _ _ => IsPureProductSum.add)
    IsPureProductSum.zero (fun i _ => isPureProductSum_kronecker (hA i) (hB i))

/-- Establishes `IsPureProductSum.isSeparable`: `IsSeparable X`, for the stated parameters. -/
theorem IsPureProductSum.isSeparable [Finite κ] [Finite n] {X : Matrix (κ × n) (κ × n) ℂ}
    (h : IsPureProductSum X) : IsSeparable X := by
  obtain ⟨N, a, b, rfl⟩ := h
  exact ⟨N, fun i => pureState (a i), fun i => pureState (b i),
    fun i => Matrix.posSemidef_vecMulVec_self_star _,
    fun i => Matrix.posSemidef_vecMulVec_self_star _, rfl⟩

/-- Establishes `isSeparable_iff_isPureProductSum`: `IsSeparable X ↔ IsPureProductSum X`, for the stated parameters. -/
theorem isSeparable_iff_isPureProductSum [Fintype κ] [Fintype n]
    {X : Matrix (κ × n) (κ × n) ℂ} : IsSeparable X ↔ IsPureProductSum X :=
  ⟨IsSeparable.isPureProductSum, IsPureProductSum.isSeparable⟩

end Qatlib.Foundations.PPTMatrix.OperatorCones
