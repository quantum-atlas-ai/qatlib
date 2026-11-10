/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Fin.Tuple
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.WalkReduction.FourDefs

def adjacency (n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, Real.sqrt (3*(n-3)), 0, 0;
     Real.sqrt (3*(n-3)), n-2, 2*Real.sqrt (2*(n-4)), 0;
     0, 2*Real.sqrt (2*(n-4)), 2*(n-4), 3*Real.sqrt (n-5);
     0, 0, 3*Real.sqrt (n-5), 3*(n-6)]

def oracle : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,0,0,0]

def hamiltonian (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := -γ • adjacency n - oracle

theorem adjacency_transpose (n : ℝ) : (adjacency n).transpose = adjacency n := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem oracle_idempotent : oracle*oracle = oracle := by
  unfold oracle
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

theorem hamiltonian_transpose (γ n : ℝ) : (hamiltonian γ n).transpose = hamiltonian γ n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hamiltonian,adjacency,oracle]

theorem hamiltonian_hermitian (γ n : ℝ) : (hamiltonian γ n).IsHermitian := by
  exact hamiltonian_transpose γ n

end Qatlib.Foundations.WalkReduction.FourDefs
