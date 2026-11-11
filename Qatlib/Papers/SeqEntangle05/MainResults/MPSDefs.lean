/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic

/-!
# Open-boundary matrix-product amplitudes

This module defines the matrix-product and sequential-isometry descriptions used for the
characterization in [SchoenEtAl2005]. A `Block D` contains two square ancillary matrices, while
an `IsometryMatrix D` has rows indexed by an ancillary label and a qubit label; `isoBlockFamily`
extracts its two blocks.

`mpsAmplitude` contracts the ordered block product between arbitrary boundary vectors. `IsMPS`
allows arbitrary blocks and `SeqGenerable` requires isometric stacked blocks, with neither
predicate imposing normalization of the boundary vectors or final ancillary decoupling.

## Main statements

* `prodBlocks` and `blockProd` define the ordered matrix products for lists and finite chains.
* `mpsAmplitude`, `IsMPS`, and `SeqGenerable` define the amplitude and its two representation
  predicates.
* `isoBlock_completeness` identifies the block completeness equation of an isometry.
* `seqGenerable_isMPS` turns every sequential-isometry representation into a matrix-product
  representation.

## References

* [Schoen et al., 2005][SchoenEtAl2005]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs

/-- A pair of complex `D`-by-`D` ancillary matrices indexed by the physical qubit label `Fin 2`. -/
abbrev Block (D : ℕ) : Type := Fin 2 → Matrix (Fin D) (Fin D) ℂ

/-- A complex matrix with `2 * D` rows indexed by ancillary and qubit labels and `D` columns
indexed by ancillary labels. The type itself does not impose the isometry equation. -/
abbrev IsometryMatrix (D : ℕ) : Type := Matrix (Fin D × Fin 2) (Fin D) ℂ

/-- The column-isometry condition `Matrix.conjTranspose V * V = 1` for a matrix from the
ancillary space to the ancillary-qubit space. -/
def IsIsometry {D : ℕ} (V : IsometryMatrix D) : Prop := Matrix.conjTranspose V * V = 1

/-- Extracts the square ancillary matrix for physical output bit `i` by setting `isoBlock V i a
b = V (a, i) b`. -/
def isoBlock {D : ℕ} (V : IsometryMatrix D) (i : Fin 2) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => V (a, i) b

/-- The two-block family obtained by extracting the physical-bit slices of `V` with `isoBlock`. -/
def isoBlockFamily {D : ℕ} (V : IsometryMatrix D) : Block D := fun i => isoBlock V i

/-- Multiplies the matrices selected by corresponding entries of a block list and a bit list, in
list order. Recursion stops when either list is empty, so unmatched trailing entries are
ignored and the empty product is the identity. -/
def prodBlocks {D : ℕ} : List (Block D) → List (Fin 2) → Matrix (Fin D) (Fin D) ℂ
  | [], _ => 1
  | _, [] => 1
  | A :: As, i :: is => A i * prodBlocks As is

/-- An empty block list gives the identity matrix for every bit list. -/
@[simp] theorem prodBlocks_nil_left {D : ℕ} (is : List (Fin 2)) :
    prodBlocks (D := D) [] is = 1 := rfl

/-- An empty bit list gives the identity matrix for every block list. -/
@[simp] theorem prodBlocks_nil_right {D : ℕ} (As : List (Block D)) :
    prodBlocks As [] = 1 := by cases As <;> rfl

/-- The product for nonempty block and bit lists is the selected head matrix `A i` multiplied on
the left of the product of the remaining lists. -/
theorem prodBlocks_cons {D : ℕ} (A : Block D) (As : List (Block D))
    (i : Fin 2) (is : List (Fin 2)) :
    prodBlocks (A :: As) (i :: is) = A i * prodBlocks As is := rfl

/-- The ordered product of the matrices `A k (bits k)` over the finite chain, obtained by
converting both indexed families to lists in increasing index order. -/
def blockProd {D n : ℕ} (A : Fin n → Block D) (bits : Fin n → Fin 2) :
    Matrix (Fin D) (Fin D) ℂ :=
  prodBlocks (List.ofFn A) (List.ofFn bits)

/-- The open-boundary amplitude obtained by applying `blockProd A bits` to `φI` and contracting
with the complex-conjugated entries of `φF`. -/
def mpsAmplitude {D n : ℕ} (A : Fin n → Block D) (φI φF : Fin D → ℂ)
    (bits : Fin n → Fin 2) : ℂ :=
  ∑ s, star (φF s) * (blockProd A bits *ᵥ φI) s

/-- Asserts that `ψ` is represented by a length-`n` family of bond-dimension-`D` blocks and two
arbitrary boundary vectors through `mpsAmplitude`. No normalization conditions are imposed. -/
def IsMPS (D n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (A : Fin n → Block D) (φI φF : Fin D → ℂ), ∀ bits, ψ bits = mpsAmplitude A φI φF bits

/-- Asserts that `ψ` has a boundary-contracted matrix-product representation whose blocks come
from a length-`n` family of isometries with ancillary dimension `D`. Boundary vectors are
arbitrary, and the predicate does not require final ancillary decoupling. -/
def SeqGenerable (D n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (V : Fin n → IsometryMatrix D) (φI φF : Fin D → ℂ),
    (∀ k, IsIsometry (V k)) ∧
    ∀ bits, ψ bits = mpsAmplitude (fun k => isoBlockFamily (V k)) φI φF bits

/-- The two physical-bit blocks of an isometry satisfy the completeness equation: the sum of
each block's conjugate transpose times itself is the ancillary identity [SchoenEtAl2005]. -/
theorem isoBlock_completeness {D : ℕ} (V : IsometryMatrix D) (hV : IsIsometry V) :
    (∑ i : Fin 2, Matrix.conjTranspose (isoBlock V i) * isoBlock V i) = 1 := by
  ext a b
  have h := congrFun (congrFun hV a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  rw [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  simpa only [isoBlock, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type] using h

/-- Every sequential-isometry representation gives a matrix-product representation with the same
ancillary dimension, chain length, and amplitude function [SchoenEtAl2005]. -/
theorem seqGenerable_isMPS {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : SeqGenerable D n ψ) : IsMPS D n ψ := by
  obtain ⟨V, φI, φF, _, hbits⟩ := h
  exact ⟨fun k => isoBlockFamily (V k), φI, φF, hbits⟩

end Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
