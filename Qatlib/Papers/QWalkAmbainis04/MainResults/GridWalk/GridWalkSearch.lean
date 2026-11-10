/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

open Matrix
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.GridWalk

def permMat {I : Type} [DecidableEq I] (σ : I → I) : Matrix I I ℂ :=
  Matrix.of fun i j => if i = σ j then (1 : ℂ) else 0

def rankOne {I : Type} [DecidableEq I] (u v : I → ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => u i * star (v j)

abbrev Vertex (n : ℕ) := ZMod n × ZMod n

abbrev State (n : ℕ) := Fin 4 × Vertex n

def shiftFF {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (1, (s.2.1 + 1, s.2.2))
  else if s.1 = 1 then (0, (s.2.1 - 1, s.2.2))
  else if s.1 = 2 then (3, (s.2.1, s.2.2 + 1))
  else (2, (s.2.1, s.2.2 - 1))

def shiftM {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (0, (s.2.1 + 1, s.2.2))
  else if s.1 = 1 then (1, (s.2.1 - 1, s.2.2))
  else if s.1 = 2 then (2, (s.2.1, s.2.2 + 1))
  else (3, (s.2.1, s.2.2 - 1))

def coin4 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if i = j then (-(1 : ℂ) / 2) else ((1 : ℂ) / 2)

def flipFlopU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftFF *
    Matrix.kronecker coin4 (1 : Matrix (Vertex n) (Vertex n) ℂ)

def movingU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftM *
    Matrix.kronecker coin4 (1 : Matrix (Vertex n) (Vertex n) ℂ)

def markVec {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : State n → ℂ :=
  fun s => if s.2 ∈ S then ((1 : ℂ) / 2) else 0

def markRefl {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : Matrix (State n) (State n) ℂ :=
  1 - (2 : ℂ) • rankOne (markVec S) (markVec S)

def flipFlopUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  flipFlopU n * markRefl S

def movingUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  movingU n * markRefl S

def start2 {n : ℕ} : State n → ℂ := fun _ => ((1 : ℂ) / (2 * (n : ℂ)))

def successFF {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((flipFlopUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

def successM {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((movingUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

def ampProb (p : ℝ) (r : ℕ) : ℝ :=
  Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2

def shiftD {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (0, (s.2.1, s.2.2 - 1))
  else if s.1 = 1 then (1, (s.2.1, s.2.2 + 1))
  else if s.1 = 2 then (2, (s.2.1 - 1, s.2.2))
  else (3, (s.2.1 + 1, s.2.2))

def diracU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftD

def diracSVec (c : Fin 4) : ℂ :=
  if c = 0 ∨ c = 1 then (((1 : ℝ) / Real.sqrt 2) : ℂ) else 0

def markVecD {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : State n → ℂ :=
  fun s => if s.2 ∈ S then diracSVec s.1 else 0

def diracUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  diracU n * (1 - (2 : ℂ) • rankOne (markVecD S) (markVecD S))

def successD {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((diracUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

theorem shiftFF_involutive {n : ℕ} (s : State n) : shiftFF (shiftFF s) = s := by
  obtain ⟨c, x, y⟩ := s
  fin_cases c <;> simp [shiftFF]

theorem coin4_mul_self : coin4 * coin4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coin4, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

theorem diracSVec_norm : ∑ c : Fin 4, ‖diracSVec c‖ ^ 2 = 1 := by
  simp [diracSVec, Fin.sum_univ_four]
  norm_num [Real.sq_sqrt]

theorem start2_norm (n : ℕ) [NeZero n] :
    ∑ s : State n, ‖start2 (n := n) s‖ ^ 2 = 1 := by
  simp only [start2, norm_div, norm_mul, Complex.norm_ofNat]
  rw [Finset.sum_const, Finset.card_univ]
  simp [Fintype.card_prod, ZMod.card]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp
  ring

theorem markVec_norm_singleton {n : ℕ} [NeZero n] (v : Vertex n) :
    ∑ s : State n, ‖markVec ({v} : Finset (Vertex n)) s‖ ^ 2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [markVec]
  have h : ∀ c : Fin 4,
      (∑ x : Vertex n,
        ‖(if x ∈ ({v} : Finset (Vertex n)) then ((1 : ℂ) / 2) else 0)‖ ^ 2)
        = (1 : ℝ) / 4 := by
    intro c
    rw [Finset.sum_eq_single v]
    · simp; norm_num
    · intro b _ hb
      simp [Finset.mem_singleton, hb]
    · intro hv
      exact absurd (Finset.mem_univ v) hv
  have h2 : (∑ c : Fin 4,
      (∑ x : Vertex n,
        ‖(if x ∈ ({v} : Finset (Vertex n)) then ((1 : ℂ) / 2) else 0)‖ ^ 2))
      = ∑ _c : Fin 4, (1 : ℝ) / 4 :=
    Finset.sum_congr rfl fun c _ => h c
  rw [h2]
  simp

end Qatlib.Papers.QWalkAmbainis04.MainResults.GridWalk
