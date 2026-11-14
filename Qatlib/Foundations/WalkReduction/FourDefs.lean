/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic

@[expose] public section

/-!
# Four-state quantum walk Hamiltonian

This module defines the explicit four-state adjacency matrix `adjacency`, the marked-coordinate
projector `oracle`, and the search Hamiltonian `hamiltonian`. It proves symmetry of the
adjacency and Hamiltonian matrices and idempotence of the oracle projector.

The mathematical background is discussed in [Wong2016].

## Main statements

* `adjacency_transpose`: the reduced adjacency matrix is symmetric.
* `oracle_idempotent`: the marked-coordinate oracle is a projector.
* `hamiltonian_hermitian`: the real search Hamiltonian is Hermitian.

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.WalkReduction.FourDefs

/-- The explicit real symmetric four-state adjacency matrix with square-root off-diagonal
couplings and diagonal entries `0`, `n - 2`, `2 * (n - 4)`, and `3 * (n - 6)`. -/
def adjacency (n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, Real.sqrt (3*(n-3)), 0, 0;
     Real.sqrt (3*(n-3)), n-2, 2*Real.sqrt (2*(n-4)), 0;
     0, 2*Real.sqrt (2*(n-4)), 2*(n-4), 3*Real.sqrt (n-5);
     0, 0, 3*Real.sqrt (n-5), 3*(n-6)]

/-- The diagonal projector onto the zeroth, marked coordinate of the four-state register. -/
def oracle : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1,0,0,0]

/-- The search Hamiltonian `-γ • adjacency n - oracle`. -/
def hamiltonian (γ n : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := -γ • adjacency n - oracle

/-- The four-state adjacency matrix equals its transpose. -/
theorem adjacency_transpose (n : ℝ) : (adjacency n).transpose = adjacency n := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The marked-coordinate oracle squares to itself. -/
theorem oracle_idempotent : oracle*oracle = oracle := by
  unfold oracle
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The search Hamiltonian equals its transpose for every real coupling and size parameter. -/
theorem hamiltonian_transpose (γ n : ℝ) : (hamiltonian γ n).transpose = hamiltonian γ n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hamiltonian,adjacency,oracle]

/-- The real search Hamiltonian is Hermitian for every coupling and size parameter. See
[Wong2016]. -/
theorem hamiltonian_hermitian (γ n : ℝ) : (hamiltonian γ n).IsHermitian := by
  exact hamiltonian_transpose γ n

end Qatlib.Foundations.WalkReduction.FourDefs
