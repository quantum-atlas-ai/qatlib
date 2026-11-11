/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Sine eigenmodes of the finite Dirichlet Laplacian

`difference` is the one-dimensional second-difference operator with zero boundary values, and
`laplacian` scales its matrix by `(n + 1)²`. The vectors `sine n j` are nonzero eigenvectors
with positive eigenvalues given by an exact half-angle sine formula.

`eigenvalue_eq_cos` gives the equivalent cosine expression, while `sourceMode` introduces the
conventional square-root scaling of the modes. These are the finite Dirichlet quantities used in
[WangEtAl2020].

## Main statements

* `laplacian_sine`: Sine eigenvector equation.
* `eigenvalue_eq_cos`: Exact cosine formula for each eigenvalue.
* `sourceMode_hasEigenvector`: Eigenvector statement for the scaled modes.

## References

* [Wang et al., 2020][WangEtAl2020]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
namespace Qatlib.Foundations.MatrixAlgebra.DirichletModes

/-- The linear second-difference operator `2vᵢ - vᵢ₋₁ - vᵢ₊₁`, with missing boundary values set
to zero. -/
def difference (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v i := 2 * v i - (if h : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) -
    (if h : i.val + 1 < n then v ⟨i.val + 1, h⟩ else 0)
  map_add' u v := by ext i; dsimp; split_ifs <;> ring
  map_smul' c v := by ext i; dsimp; split_ifs <;> ring

/-- The Dirichlet second-difference matrix scaled by `(n + 1)²`. -/
def laplacian (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ 2 • LinearMap.toMatrix' (difference n)

/-- Multiplication by the Dirichlet Laplacian equals `(n + 1)²` times the second-difference
operator. -/
theorem laplacian_mulVec (n : ℕ) (v : Fin n → ℝ) :
    laplacian n *ᵥ v = ((n + 1 : ℕ) : ℝ) ^ 2 • difference n v := by
  rw [laplacian, Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec]

/-- The mode angle `(j.val + 1) * π / (n + 1)`. -/
def angle (n : ℕ) (j : Fin n) : ℝ := ((j.val + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℕ)

/-- The discrete sine mode with entry `sin ((i.val + 1) * angle n j)`. -/
def sine (n : ℕ) (j : Fin n) (i : Fin n) : ℝ :=
  Real.sin (((i.val + 1 : ℕ) : ℝ) * angle n j)

/-- The eigenvalue `4 * (n + 1)² * sin² (angle n j / 2)`. -/
def eigenvalue (n : ℕ) (j : Fin n) : ℝ :=
  4 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.sin (angle n j / 2) ^ 2

/-- The sine mode vanishes at the two Dirichlet boundary positions. -/
theorem sine_boundary (n : ℕ) (j : Fin n) :
    Real.sin (0 * angle n j) = 0 ∧ Real.sin (((n + 1 : ℕ) : ℝ) * angle n j) = 0 := by
  constructor
  · simp
  · have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h : ((n + 1 : ℕ) : ℝ) * angle n j = ((j.val + 1 : ℕ) : ℝ) * Real.pi := by
      unfold angle; field_simp
    rw [h, Real.sin_nat_mul_pi]

/-- The centered second difference of sine is `4 * sin² (t / 2) * sin x`. -/
theorem sine_recurrence (t x : ℝ) :
    2 * Real.sin x - Real.sin (x - t) - Real.sin (x + t) =
      4 * Real.sin (t / 2) ^ 2 * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]
  have h := Real.cos_two_mul (t / 2)
  have hsc := Real.sin_sq_add_cos_sq (t / 2)
  rw [show 2 * (t / 2) = t by ring] at h
  have hc : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by nlinarith
  rw [hc]
  ring

/-- The discrete sine mode is an eigenvector of the second-difference operator with eigenvalue
`4 * sin² (angle n j / 2)`. -/
theorem difference_sine (n : ℕ) (j : Fin n) :
    difference n (sine n j) = (4 * Real.sin (angle n j / 2) ^ 2) • sine n j := by
  ext i
  have left : (if h : 0 < i.val then sine n j ⟨i.val - 1, by omega⟩ else 0) =
      Real.sin ((((i.val + 1 : ℕ) : ℝ) * angle n j) - angle n j) := by
    by_cases h : 0 < i.val
    · simp only [h, dite_true, sine]
      congr 1
      rw [Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
      push_cast
      ring
    · have hi : i.val = 0 := by omega
      simp [hi]
  have right : (if h : i.val + 1 < n then sine n j ⟨i.val + 1, h⟩ else 0) =
      Real.sin ((((i.val + 1 : ℕ) : ℝ) * angle n j) + angle n j) := by
    by_cases h : i.val + 1 < n
    · simp only [h, dite_true, sine]
      congr 1
      push_cast
      ring
    · have hi : i.val + 1 = n := by omega
      have hb := (sine_boundary n j).2
      have he : (((i.val + 1 : ℕ) : ℝ) * angle n j) + angle n j =
          ((n + 1 : ℕ) : ℝ) * angle n j := by rw [hi]; push_cast; ring
      simp only [h, dite_false, he]
      exact hb.symm
  change 2 * sine n j i - _ - _ = _
  rw [left, right]
  exact sine_recurrence (angle n j) (((i.val + 1 : ℕ) : ℝ) * angle n j)

/-- Applying the Dirichlet Laplacian to a sine mode multiplies it by its specified eigenvalue. -/
theorem laplacian_sine (n : ℕ) (j : Fin n) :
    laplacian n *ᵥ sine n j = eigenvalue n j • sine n j := by
  rw [laplacian_mulVec, difference_sine, smul_smul]
  congr 1
  unfold eigenvalue
  ring

/-- Every mode angle lies strictly between zero and `π`. -/
theorem angle_bounds (n : ℕ) (j : Fin n) : 0 < angle n j ∧ angle n j < Real.pi := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hj : ((j.val + 1 : ℕ) : ℝ) < (n + 1 : ℕ) := by exact_mod_cast (by omega : j.val + 1 < n + 1)
  constructor
  · unfold angle; positivity
  · unfold angle
    rw [div_lt_iff₀ hn]
    nlinarith [Real.pi_pos]

/-- Every indexed discrete sine mode is nonzero. -/
theorem sine_ne_zero (n : ℕ) (j : Fin n) : sine n j ≠ 0 := by
  have hj := j.isLt
  have hn : 0 < n := by omega
  intro h
  have hi := congrFun h ⟨0, hn⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi (angle_bounds n j).1 (angle_bounds n j).2
  simp [sine] at hi
  linarith

/-- Each sine mode is an eigenvector of the linear endomorphism represented by the Dirichlet
Laplacian. -/
theorem laplacian_hasEigenvector (n : ℕ) (j : Fin n) :
    Module.End.HasEigenvector (Matrix.toLin' (laplacian n)) (eigenvalue n j) (sine n j) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact laplacian_sine n j
  · exact sine_ne_zero n j

/-- The Dirichlet Laplacian has diagonal entries `2 * (n + 1)²`, adjacent entries `-(n + 1)²`,
and all other entries zero. -/
theorem laplacian_apply (n : ℕ) (i j : Fin n) :
    laplacian n i j = ((n + 1 : ℕ) : ℝ) ^ 2 *
      ((if i = j then 2 else 0) - (if j.val + 1 = i.val then 1 else 0) -
        (if i.val + 1 = j.val then 1 else 0)) := by
  simp only [laplacian, Matrix.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply]
  congr 1
  simp only [difference, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The real Dirichlet Laplacian matrix is symmetric. -/
theorem laplacian_symmetric (n : ℕ) : (laplacian n).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, laplacian_apply, laplacian_apply]
  simp only [eq_comm (a := j) (b := i)]
  ring

/-- Every indexed Dirichlet eigenvalue is strictly positive. -/
theorem eigenvalue_pos (n : ℕ) (j : Fin n) : 0 < eigenvalue n j := by
  have h := angle_bounds n j
  have hs : 0 < Real.sin (angle n j / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  unfold eigenvalue
  positivity

/-- The Dirichlet eigenvalue equals `2 * (n + 1)² * (1 - cos (angle n j))`, as in the eigenvalue
formula of [WangEtAl2020]. -/
theorem eigenvalue_eq_cos (n : ℕ) (j : Fin n) :
    eigenvalue n j = 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 - Real.cos (angle n j)) := by
  have hc := Real.cos_two_mul (angle n j / 2)
  have hsc := Real.sin_sq_add_cos_sq (angle n j / 2)
  rw [show 2 * (angle n j / 2) = angle n j by ring] at hc
  have he : 4 * Real.sin (angle n j / 2) ^ 2 = 2 * (1 - Real.cos (angle n j)) := by nlinarith
  unfold eigenvalue
  calc
    4 * ((n + 1 : ℕ) : ℝ) ^ 2 * Real.sin (angle n j / 2) ^ 2 =
        ((n + 1 : ℕ) : ℝ) ^ 2 * (4 * Real.sin (angle n j / 2) ^ 2) := by ring
    _ = 2 * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 - Real.cos (angle n j)) := by rw [he]; ring

/-- The discrete sine mode scaled by `sqrt (2 / (n + 1))`. -/
def sourceMode (n : ℕ) (j : Fin n) : Fin n → ℝ :=
  Real.sqrt (2 / (n + 1 : ℕ)) • sine n j

/-- The scaled source mode satisfies the Dirichlet Laplacian eigenvector equation. -/
theorem laplacian_sourceMode (n : ℕ) (j : Fin n) :
    laplacian n *ᵥ sourceMode n j = eigenvalue n j • sourceMode n j := by
  rw [sourceMode, Matrix.mulVec_smul, laplacian_sine, smul_comm]

/-- Every indexed scaled source mode is nonzero. -/
theorem sourceMode_ne_zero (n : ℕ) (j : Fin n) : sourceMode n j ≠ 0 := by
  apply smul_ne_zero
  · exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  · exact sine_ne_zero n j

/-- Each scaled source mode is an eigenvector of the linear endomorphism represented by the
Dirichlet Laplacian. -/
theorem sourceMode_hasEigenvector (n : ℕ) (j : Fin n) :
    Module.End.HasEigenvector (Matrix.toLin' (laplacian n)) (eigenvalue n j) (sourceMode n j) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact laplacian_sourceMode n j
  · exact sourceMode_ne_zero n j
end Qatlib.Foundations.MatrixAlgebra.DirichletModes
