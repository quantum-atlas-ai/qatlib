/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Subsemigroup.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Real axis rotations and operator norm bounds

`driverAngle` and `problemAngle` define real three-dimensional rotations fixing the first and
third coordinate axes, respectively. Their product `rotationStep` combines schedule and field
parameters, and the module proves that all these matrices are orthogonal with operator norm one.

Explicit Gram-matrix calculations give the exact sine formula for the difference of two
field-dependent steps and its Lipschitz bound. These rotation estimates support the
finite-history analysis in [GohMuller2026].

## Main statements

* `step_unitary`: each rotation step is orthogonal.
* `problem_difference_norm`: the exact chord formula for the planar rotation difference.
* `step_difference_le`: the field dependence has Lipschitz constant `2 * |s|`.

## References

* [Goh and Müller, 2026][GohMuller2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
/-- Real three-by-three matrices indexed by `Fin 3`. -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The rotation fixing the first coordinate, with cosine-sine block on the second and third
coordinates. -/
def driverAngle (a : ℝ) : Mat3 :=
  !![1,0,0; 0,Real.cos a,Real.sin a; 0,-Real.sin a,Real.cos a]

/-- The rotation fixing the third coordinate, with cosine-sine block on the first and second
coordinates. -/
def problemAngle (a : ℝ) : Mat3 :=
  !![Real.cos a,Real.sin a,0; -Real.sin a,Real.cos a,0; 0,0,1]

/-- The product of a driver rotation at angle `2 * (1 - s)` and a problem rotation at angle `2 *
s * x`. -/
def rotationStep (s x : ℝ) : Mat3 := driverAngle (2*(1-s)) * problemAngle (2*s*x)

/-- The driver rotation matrix is orthogonal for every real angle. -/
theorem driver_unitary (a : ℝ) : driverAngle a ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [driverAngle, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.star_eq_conjTranspose] <;> nlinarith [Real.sin_sq_add_cos_sq a]

/-- The problem rotation matrix is orthogonal for every real angle. -/
theorem problem_unitary (a : ℝ) : problemAngle a ∈ Matrix.unitaryGroup (Fin 3) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [problemAngle, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.star_eq_conjTranspose] <;> nlinarith [Real.sin_sq_add_cos_sq a]

/-- Every rotation step is an orthogonal matrix. -/
theorem step_unitary (s x : ℝ) : rotationStep s x ∈ Matrix.unitaryGroup (Fin 3) ℝ :=
  mul_mem (driver_unitary _) (problem_unitary _)

/-- Every rotation step has operator norm one. -/
theorem step_norm (s x : ℝ) : ‖rotationStep s x‖=1 :=
    CStarRing.norm_of_mem_unitary (step_unitary s x)

/-- The squared distance between the sine-cosine pairs at two angles equals four times the
squared sine of their half-difference. -/
theorem chord_sq (a b : ℝ) :
    (Real.cos a-Real.cos b)^2+(Real.sin a-Real.sin b)^2=4*Real.sin ((a-b)/2)^2 := by
  rw [Real.cos_sub_cos, Real.sin_sub_sin]
  calc
    _ = 4*Real.sin ((a-b)/2)^2*(Real.sin ((a+b)/2)^2+Real.cos ((a+b)/2)^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- The diagonal projection onto the first two coordinates has operator norm one. -/
theorem plane_projection_norm : ‖(Matrix.diagonal (![1,1,0] : Fin 3 → ℝ) : Mat3)‖=1 := by
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).2
    intro i
    fin_cases i <;> norm_num
  · simpa using norm_le_pi_norm (![1,1,0] : Fin 3 → ℝ) (0:Fin 3)

/-- The Gram matrix of a difference of problem rotations equals the squared sine-cosine chord
length times the projection onto the first two coordinates. -/
theorem problem_difference_gram (a b : ℝ) :
    (problemAngle a-problemAngle b).conjTranspose * (problemAngle a-problemAngle b) =
      ((Real.cos a-Real.cos b)^2+(Real.sin a-Real.sin b)^2) •
        (Matrix.diagonal (![1,1,0] : Fin 3 → ℝ) : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [problemAngle, Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply] <;> ring

/-- The operator norm of the difference of two problem rotations equals twice the absolute sine
of their half-angle difference. -/
theorem problem_difference_norm (a b : ℝ) :
    ‖problemAngle a-problemAngle b‖=2*|Real.sin ((a-b)/2)| := by
  have hg := Matrix.l2_opNorm_conjTranspose_mul_self (problemAngle a-problemAngle b)
  rw [problem_difference_gram, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), plane_projection_norm, mul_one, chord_sq] at hg
  have hn := norm_nonneg (problemAngle a-problemAngle b)
  have hs := abs_nonneg (Real.sin ((a-b)/2))
  nlinarith [sq_abs (Real.sin ((a-b)/2))]

/-- The exact operator norm difference between steps at fields `x` and `y` is `2 * |sin (s * (x
- y))|`, giving the rotation estimate used in [GohMuller2026]. -/
theorem step_difference_norm (s x y : ℝ) :
    ‖rotationStep s x-rotationStep s y‖=2*|Real.sin (s*(x-y))| := by
  unfold rotationStep
  rw [← mul_sub, CStarRing.norm_mem_unitary_mul _ (driver_unitary _), problem_difference_norm]
  congr 3
  ring

/-- The operator norm difference between steps at fields `x` and `y` is at most `2 * |s| * |x -
y|`. -/
theorem step_difference_le (s x y : ℝ) :
    ‖rotationStep s x-rotationStep s y‖≤2 * |s| * |x-y| := by
  rw [step_difference_norm]
  calc
    _ ≤ 2*|s*(x-y)| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = _ := by rw [abs_mul]; ring

end Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
