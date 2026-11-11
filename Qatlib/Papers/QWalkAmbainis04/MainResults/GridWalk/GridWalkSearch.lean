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

/-!
# Quantum search walks on a periodic square grid

`Vertex` and `State` describe positions and four-direction coin states on a periodic square
grid. The module defines the flip-flop, moving, and Dirac shifts, the associated marked walk
matrices, and their marked-position success expressions.

The uniform starting vector, singleton marking vector, and Dirac coin vector satisfy the stated
normalization identities; the flip-flop shift and Grover coin are involutive. This development
supports the analysis in [AmbainisKempeRivosh2004].

## Main statements

* `shiftFF_involutive`: the flip-flop shift is an involution.
* `coin4_mul_self`: the Grover coin squares to the identity.
* `start2_norm` and `markVec_norm_singleton`: normalization of the starting and singleton
  marking vectors.

## References

* [Ambainis et al., 2004][AmbainisKempeRivosh2004]
-/

open Matrix
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.GridWalk

/-- The matrix whose column indexed by `j` is the coordinate vector at `σ j`. -/
def permMat {I : Type} [DecidableEq I] (σ : I → I) : Matrix I I ℂ :=
  Matrix.of fun i j => if i = σ j then (1 : ℂ) else 0

/-- The outer-product matrix with entries `u i * star (v j)`. -/
def rankOne {I : Type} [DecidableEq I] (u v : I → ℂ) : Matrix I I ℂ :=
  Matrix.of fun i j => u i * star (v j)

/-- The position type `ZMod n × ZMod n` for the periodic square grid. -/
abbrev Vertex (n : ℕ) := ZMod n × ZMod n

/-- The state type pairing a four-valued coin direction with a grid vertex. -/
abbrev State (n : ℕ) := Fin 4 × Vertex n

/-- The grid shift that moves one step in the chosen direction and reverses the coin direction. -/
def shiftFF {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (1, (s.2.1 + 1, s.2.2))
  else if s.1 = 1 then (0, (s.2.1 - 1, s.2.2))
  else if s.1 = 2 then (3, (s.2.1, s.2.2 + 1))
  else (2, (s.2.1, s.2.2 - 1))

/-- The grid shift that moves one step in the chosen direction while preserving the coin
direction. -/
def shiftM {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (0, (s.2.1 + 1, s.2.2))
  else if s.1 = 1 then (1, (s.2.1 - 1, s.2.2))
  else if s.1 = 2 then (2, (s.2.1, s.2.2 + 1))
  else (3, (s.2.1, s.2.2 - 1))

/-- The four-dimensional Grover coin with diagonal entries `-1 / 2` and off-diagonal entries `1
/ 2`. -/
def coin4 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => if i = j then (-(1 : ℂ) / 2) else ((1 : ℂ) / 2)

/-- The unmarked flip-flop walk matrix, applying the Grover coin before the flip-flop shift. -/
def flipFlopU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftFF *
    Matrix.kronecker coin4 (1 : Matrix (Vertex n) (Vertex n) ℂ)

/-- The unmarked moving walk matrix, applying the Grover coin before the moving shift. -/
def movingU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftM *
    Matrix.kronecker coin4 (1 : Matrix (Vertex n) (Vertex n) ℂ)

/-- The marking vector equal to `1 / 2` in each coin direction over `S` and zero elsewhere. -/
def markVec {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : State n → ℂ :=
  fun s => if s.2 ∈ S then ((1 : ℂ) / 2) else 0

/-- The marking matrix `1 - 2 • rankOne (markVec S) (markVec S)`. -/
def markRefl {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : Matrix (State n) (State n) ℂ :=
  1 - (2 : ℂ) • rankOne (markVec S) (markVec S)

/-- The flip-flop walk matrix followed on the right by the marking matrix `markRefl S`. -/
def flipFlopUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  flipFlopU n * markRefl S

/-- The moving walk matrix followed on the right by the marking matrix `markRefl S`. -/
def movingUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  movingU n * markRefl S

/-- The constant starting vector with amplitude `1 / (2 * n)` in every grid state. -/
def start2 {n : ℕ} : State n → ℂ := fun _ => ((1 : ℂ) / (2 * (n : ℂ)))

/-- The sum of squared amplitudes at marked vertices after `T` steps of the marked flip-flop
walk from `start2`. -/
def successFF {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((flipFlopUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

/-- The sum of squared amplitudes at marked vertices after `T` steps of the marked moving walk
from `start2`. -/
def successM {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((movingUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

/-- The amplitude-amplification expression `sin ((2 * r + 1) * arcsin (sqrt p)) ^ 2`. -/
def ampProb (p : ℝ) (r : ℕ) : ℝ :=
  Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2

/-- The direction-preserving grid shift used by the Dirac walk, with directions ordered as down,
up, left, and right. -/
def shiftD {n : ℕ} (s : State n) : State n :=
  if s.1 = 0 then (0, (s.2.1, s.2.2 - 1))
  else if s.1 = 1 then (1, (s.2.1, s.2.2 + 1))
  else if s.1 = 2 then (2, (s.2.1 - 1, s.2.2))
  else (3, (s.2.1 + 1, s.2.2))

/-- The matrix of the Dirac shift `shiftD`. -/
def diracU (n : ℕ) [NeZero n] : Matrix (State n) (State n) ℂ :=
  permMat (I := State n) shiftD

/-- The coin vector equal to `1 / sqrt 2` in directions zero and one and zero in the other
directions. -/
def diracSVec (c : Fin 4) : ℂ :=
  if c = 0 ∨ c = 1 then (((1 : ℝ) / Real.sqrt 2) : ℂ) else 0

/-- The vector equal to `diracSVec` over marked vertices and zero elsewhere. -/
def markVecD {n : ℕ} [NeZero n] (S : Finset (Vertex n)) : State n → ℂ :=
  fun s => if s.2 ∈ S then diracSVec s.1 else 0

/-- The Dirac shift matrix multiplied by the marking matrix formed from `markVecD S`. -/
def diracUmark {n : ℕ} [NeZero n] (S : Finset (Vertex n)) :
    Matrix (State n) (State n) ℂ :=
  diracU n * (1 - (2 : ℂ) • rankOne (markVecD S) (markVecD S))

/-- The sum of squared amplitudes at marked vertices after `T` steps of the marked Dirac walk
from `start2`. -/
def successD {n : ℕ} [NeZero n] (S : Finset (Vertex n)) (T : ℕ) : ℝ :=
  ∑ c : Fin 4, ∑ v ∈ S, ‖(((diracUmark S) ^ T) *ᵥ (start2 (n := n))) (c, v)‖ ^ 2

/-- Applying the flip-flop shift twice returns the original state. -/
theorem shiftFF_involutive {n : ℕ} (s : State n) : shiftFF (shiftFF s) = s := by
  obtain ⟨c, x, y⟩ := s
  fin_cases c <;> simp [shiftFF]

/-- The four-dimensional Grover coin squares to the identity matrix. -/
theorem coin4_mul_self : coin4 * coin4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coin4, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num

/-- The sum of squared component norms of `diracSVec` is one. -/
theorem diracSVec_norm : ∑ c : Fin 4, ‖diracSVec c‖ ^ 2 = 1 := by
  simp [diracSVec, Fin.sum_univ_four]
  norm_num [Real.sq_sqrt]

/-- For nonzero grid size `n`, the sum of squared amplitudes of `start2` is one. -/
theorem start2_norm (n : ℕ) [NeZero n] :
    ∑ s : State n, ‖start2 (n := n) s‖ ^ 2 = 1 := by
  simp only [start2, norm_div, norm_mul, Complex.norm_ofNat]
  rw [Finset.sum_const, Finset.card_univ]
  simp [Fintype.card_prod, ZMod.card]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp
  ring

/-- The marking vector for a singleton vertex has squared norm one. -/
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
