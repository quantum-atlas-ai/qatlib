/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

def diffMatrix {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (i : Fin n) : Matrix ι ι ℝ :=
  fun x y => if bit x i = bit y i then 0 else 1

def IsAdversaryMatrix {ι : Type*} {Out : Type} (f : ι → Out) (Γ : Matrix ι ι ℝ) : Prop :=
  Γ ≠ 0 ∧ (∀ x y, Γ x y = Γ y x) ∧ (∀ x y, 0 ≤ Γ x y) ∧
    (∀ x y, f x = f y → Γ x y = 0)

def advDenom {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (Γ : Matrix ι ι ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (fun i : Fin n => ‖Γ ⊙ diffMatrix bit i‖)

def advRatios {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {Out : Type}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (f : ι → Out) : Set ℝ :=
  {r | ∃ Γ : Matrix ι ι ℝ, IsAdversaryMatrix f Γ ∧ r = ‖Γ‖ / advDenom bit hn Γ}

def advValue {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {Out : Type}
    (bit : ι → Fin n → Bool) (hn : 0 < n) (f : ι → Out) : ℝ :=
  sSup (advRatios bit hn f)

def sumBit {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (t : ℕ) (hn : 0 < n) :
    (Fin t → ι) → Fin (n * t) → Bool :=
  fun X q =>
    bit (X ⟨q.1 / n, Nat.div_lt_of_lt_mul q.2⟩) ⟨q.1 % n, Nat.mod_lt _ hn⟩

def sumFun {ι : Type*} {Out : Type} (f : ι → Out) (t : ℕ) : (Fin t → ι) → Fin t → Out :=
  fun X j => f (X j)

theorem diffMatrix_symm {ι : Type*} {n : ℕ} (bit : ι → Fin n → Bool) (i : Fin n) :
    ∀ x y, diffMatrix bit i x y = diffMatrix bit i y x := by
  intro x y
  unfold diffMatrix
  by_cases h : bit x i = bit y i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

theorem hadamard_symm {ι : Type*} (A B : Matrix ι ι ℝ)
    (hA : ∀ x y, A x y = A y x) (hB : ∀ x y, B x y = B y x) :
    ∀ x y, (A ⊙ B) x y = (A ⊙ B) y x := by
  intro x y
  show A x y * B x y = A y x * B y x
  rw [hA x y, hB x y]

end Qatlib.Papers.CertQuery09.MainResults.Source
