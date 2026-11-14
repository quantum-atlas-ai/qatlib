/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Nonnegative adversary values and product inputs

This module defines query-difference matrices, nonzero symmetric nonnegative adversary matrices,
and their operator-norm ratios and supremum. Concatenated bit access and componentwise product
outputs provide the setup for the direct-sum constructions discussed in [AmbainisEtAl2009].

## Main statements

* `diffMatrix_symm`: query-difference matrices are symmetric.
* `hadamard_symm`: entrywise products preserve symmetry.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

/-- The real zero-one matrix indicating whether two inputs differ at query position `i`. -/
def diffMatrix {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (i : Fin n) : Matrix ι ι ℝ :=
  fun x y => if bit x i = bit y i then 0 else 1

/-- The condition that a real matrix is nonzero, symmetric, entrywise nonnegative, and zero
between inputs having the same output under `f`. -/
def IsAdversaryMatrix {ι : Type*} {Out : Type} (f : ι → Out) (Γ : Matrix ι ι ℝ) : Prop :=
  Γ ≠ 0 ∧ (∀ x y, Γ x y = Γ y x) ∧ (∀ x y, 0 ≤ Γ x y) ∧
    (∀ x y, f x = f y → Γ x y = 0)

/-- The maximum Euclidean operator norm of `Γ ⊙ diffMatrix bit i` over the nonempty set of input
positions. -/
def advDenom {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (Γ : Matrix ι ι ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i : Fin n => ‖Γ ⊙ diffMatrix bit i‖)

/-- The set of ratios `‖Γ‖ / advDenom bit hn Γ` attained by adversary matrices for `f`. -/
def advRatios {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {Out : Type}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (f : ι → Out) : Set ℝ :=
  {r | ∃ Γ : Matrix ι ι ℝ, IsAdversaryMatrix f Γ ∧ r = ‖Γ‖ / advDenom bit hn Γ}

/-- The real supremum of the set of nonnegative adversary-matrix ratios for the given bit access
and output function. -/
def advValue {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {Out : Type}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (f : ι → Out) : ℝ :=
  sSup (advRatios bit hn f)

/-- Bit access to `t` concatenated input blocks of positive length `n`, using quotient and
remainder to select the block and local position. -/
def sumBit {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (t : ℕ) (hn : 0 < n) :
    (Fin t → ι) → Fin (n * t) → Bool :=
  fun X q =>
    bit (X ⟨q.1 / n, Nat.div_lt_of_lt_mul q.2⟩) ⟨q.1 % n, Nat.mod_lt _ hn⟩

/-- The componentwise application of `f` to a tuple of `t` inputs. -/
def sumFun {ι : Type*} {Out : Type} (f : ι → Out) (t : ℕ) : (Fin t → ι) → Fin t → Out :=
  fun X j => f (X j)

/-- The query-difference matrix is symmetric for every input position. -/
theorem diffMatrix_symm {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (i : Fin n) :
    ∀ x y, diffMatrix bit i x y = diffMatrix bit i y x := by
  intro x y
  unfold diffMatrix
  by_cases h : bit x i = bit y i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]

/-- The entrywise product of two symmetric real matrices is symmetric. -/
theorem hadamard_symm {ι : Type*} (A B : Matrix ι ι ℝ)
    (hA : ∀ x y, A x y = A y x) (hB : ∀ x y, B x y = B y x) :
    ∀ x y, (A ⊙ B) x y = (A ⊙ B) y x := by
  intro x y
  show A x y * B x y = A y x * B y x
  rw [hA x y, hB x y]

end Qatlib.Papers.CertQuery09.MainResults.Source
