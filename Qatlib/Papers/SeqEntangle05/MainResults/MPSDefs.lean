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

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs

abbrev Block (D : ℕ) : Type := Fin 2 → Matrix (Fin D) (Fin D) ℂ

abbrev IsometryMatrix (D : ℕ) : Type := Matrix (Fin D × Fin 2) (Fin D) ℂ

def IsIsometry {D : ℕ} (V : IsometryMatrix D) : Prop := Matrix.conjTranspose V * V = 1

def isoBlock {D : ℕ} (V : IsometryMatrix D) (i : Fin 2) : Matrix (Fin D) (Fin D) ℂ :=
  fun a b => V (a, i) b

def isoBlockFamily {D : ℕ} (V : IsometryMatrix D) : Block D := fun i => isoBlock V i

def prodBlocks {D : ℕ} : List (Block D) → List (Fin 2) → Matrix (Fin D) (Fin D) ℂ
  | [], _ => 1
  | _, [] => 1
  | A :: As, i :: is => A i * prodBlocks As is

@[simp] theorem prodBlocks_nil_left {D : ℕ} (is : List (Fin 2)) :
    prodBlocks (D := D) [] is = 1 := rfl

@[simp] theorem prodBlocks_nil_right {D : ℕ} (As : List (Block D)) :
    prodBlocks As [] = 1 := by cases As <;> rfl

theorem prodBlocks_cons {D : ℕ} (A : Block D) (As : List (Block D))
    (i : Fin 2) (is : List (Fin 2)) :
    prodBlocks (A :: As) (i :: is) = A i * prodBlocks As is := rfl

def blockProd {D n : ℕ} (A : Fin n → Block D) (bits : Fin n → Fin 2) :
    Matrix (Fin D) (Fin D) ℂ :=
  prodBlocks (List.ofFn A) (List.ofFn bits)

def mpsAmplitude {D n : ℕ} (A : Fin n → Block D) (φI φF : Fin D → ℂ)
    (bits : Fin n → Fin 2) : ℂ :=
  ∑ s, star (φF s) * (blockProd A bits *ᵥ φI) s

def IsMPS (D n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (A : Fin n → Block D) (φI φF : Fin D → ℂ), ∀ bits, ψ bits = mpsAmplitude A φI φF bits

def SeqGenerable (D n : ℕ) (ψ : (Fin n → Fin 2) → ℂ) : Prop :=
  ∃ (V : Fin n → IsometryMatrix D) (φI φF : Fin D → ℂ),
    (∀ k, IsIsometry (V k)) ∧
    ∀ bits, ψ bits = mpsAmplitude (fun k => isoBlockFamily (V k)) φI φF bits

theorem isoBlock_completeness {D : ℕ} (V : IsometryMatrix D) (hV : IsIsometry V) :
    (∑ i : Fin 2, Matrix.conjTranspose (isoBlock V i) * isoBlock V i) = 1 := by
  ext a b
  have h := congrFun (congrFun hV a) b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  rw [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  simpa only [isoBlock, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type] using h

theorem seqGenerable_isMPS {D n : ℕ} {ψ : (Fin n → Fin 2) → ℂ}
    (h : SeqGenerable D n ψ) : IsMPS D n ψ := by
  obtain ⟨V, φI, φF, _, hbits⟩ := h
  exact ⟨fun k => isoBlockFamily (V k), φI, φF, hbits⟩

end Qatlib.Papers.SeqEntangle05.MainResults.MPSDefs
