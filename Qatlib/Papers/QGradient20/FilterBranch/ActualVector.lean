/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs

/-!
# Successful filter vectors and their mass bounds

`normalizedMatrix` rescales a matrix to a contraction, and `project` removes a distinguished
coordinate. These operations define the signed update and `successfulVector`; norm estimates
place its squared mass in the unit interval and bound it below for branch parameters at most
one. The mathematical context is [GaoEtAl2021].

## Main statements

* `successMass_lower`: For a unit input and `0 ≤ ξ ≤ 1`, the successful mass is at least
  `((1-ξ)/(1+ξ))²`.
* `successMass_mem_unit`: For a unit input and nonnegative branch parameter, the successful mass
  lies between zero and one.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The normalization scale `max 1 ‖M‖` in the matrix operator norm. -/
def spectralScale (M : Matrix I I ℂ) : ℝ := max 1 ‖M‖

/-- The matrix `M` divided by its spectral normalization scale. -/
def normalizedMatrix (M : Matrix I I ℂ) : Matrix I I ℂ := (spectralScale M)⁻¹ • M

/-- The spectral normalization scale is strictly positive. -/
theorem spectralScale_pos (M : Matrix I I ℂ) : 0 < spectralScale M :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The normalized matrix has operator norm at most one. -/
theorem normalizedMatrix_norm (M : Matrix I I ℂ) : ‖normalizedMatrix M‖ ≤ 1 := by
  rw [normalizedMatrix, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (spectralScale_pos M))]
  rw [← div_eq_inv_mul]
  exact (div_le_one (spectralScale_pos M)).mpr (le_max_right _ _)

/-- The diagonal matrix that removes the distinguished coordinate and preserves every other
coordinate. -/
def projectionMatrix (zero : I) : Matrix I I ℂ := diagonal (fun i => if i = zero then 0 else 1)

/-- The continuous linear operator induced by the coordinate-removal matrix. -/
def project (zero : I) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (projectionMatrix zero)

/-- The projection sets the distinguished coordinate to zero and preserves every other
coordinate. -/
theorem project_apply (zero : I) (x : EuclideanSpace ℂ I) (i : I) :
    project zero x i = if i = zero then 0 else x i := by
  change (projectionMatrix zero *ᵥ x.ofLp) i = _
  simp [projectionMatrix, Matrix.mulVec_diagonal]

/-- Removing the distinguished coordinate cannot increase the Euclidean norm. -/
theorem project_norm_le (zero : I) (x : EuclideanSpace ℂ I) : ‖project zero x‖ ≤ ‖x‖ := by
  have hs : ‖project zero x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [project_apply]
    split_ifs
    · simp
    · exact le_rfl
  nlinarith [norm_nonneg (project zero x), norm_nonneg x]

/-- The continuous linear operator induced by `normalizedMatrix M`. -/
def derivativeAction (M : Matrix I I ℂ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)) (normalizedMatrix M)

/-- The normalized derivative action cannot increase the Euclidean norm. -/
theorem derivativeAction_norm_le (M : Matrix I I ℂ) (x : EuclideanSpace ℂ I) :
    ‖derivativeAction M x‖ ≤ ‖x‖ := by
  have h := (derivativeAction M).le_opNorm x
  have hn : ‖derivativeAction M‖ ≤ 1 := by
    rw [derivativeAction, Matrix.l2_opNorm_toEuclideanCLM]
    exact normalizedMatrix_norm M
  exact h.trans ((mul_le_mul_of_nonneg_right hn (norm_nonneg x)).trans_eq (one_mul _))

/-- The real sign equal to one for ascent and minus one for descent. -/
def branchSign (ascent : Bool) : ℝ := if ascent then 1 else -1

/-- The absolute value of the ascent-or-descent sign is one. -/
theorem branchSign_abs (ascent : Bool) : |branchSign ascent| = 1 := by
    cases ascent <;> norm_num [branchSign]

/-- The input vector plus the signed step-size multiple of the projected normalized derivative
action. -/
def update (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ I := x + (branchSign ascent * ξ) • project zero (derivativeAction M x)

/-- The signed update divided by `1+ξ`. -/
def successfulVector (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ I := (1 + ξ)⁻¹ • update zero M ξ ascent x

/-- The squared Euclidean norm of the successful filter vector. -/
def successMass (zero : I) (M : Matrix I I ℂ) (ξ : ℝ) (ascent : Bool) (x : EuclideanSpace ℂ I) : ℝ :=
  ‖successfulVector zero M ξ ascent x‖ ^ 2

/-- For nonnegative `ξ`, the signed projected derivative contribution has norm at most `ξ *
‖x‖`. -/
theorem contribution_norm_le (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (ascent : Bool) (x : EuclideanSpace ℂ I) :
    ‖(branchSign ascent * ξ) • project zero (derivativeAction M x)‖ ≤ ξ * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, branchSign_abs, abs_of_nonneg hξ, one_mul]
  exact mul_le_mul_of_nonneg_left ((project_norm_le zero _).trans (derivativeAction_norm_le M x)) hξ

/-- For nonnegative `ξ`, the successful filter vector has norm at most that of its input. -/
theorem successfulVector_norm_le (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (ascent : Bool) (x : EuclideanSpace ℂ I) :
    ‖successfulVector zero M ξ ascent x‖ ≤ ‖x‖ := by
  have hp : 0 < 1 + ξ := by linarith
  rw [successfulVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have hu : ‖update zero M ξ ascent x‖ ≤ (1 + ξ) * ‖x‖ := by
    calc
      ‖update zero M ξ ascent x‖ ≤ ‖x‖ + ‖(branchSign ascent * ξ) • project zero (derivativeAction M x)‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ξ * ‖x‖ := add_le_add (le_refl ‖x‖) (contribution_norm_le zero M hξ ascent x)
      _ = (1 + ξ) * ‖x‖ := by ring
  exact (mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hp.le)).trans_eq (by field_simp)

/-- For a unit input and nonnegative `ξ`, the successful vector has norm at least `(1-ξ)/(1+ξ)`. -/
theorem successfulVector_norm_ge (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (ascent : Bool) (x : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) :
    (1 - ξ) / (1 + ξ) ≤ ‖successfulVector zero M ξ ascent x‖ := by
  have hp : 0 < 1 + ξ := by linarith
  let w := (branchSign ascent * ξ) • project zero (derivativeAction M x)
  have hw : ‖w‖ ≤ ξ := by simpa only [hx, mul_one] using contribution_norm_le zero M hξ ascent x
  have hu : 1 - ξ ≤ ‖update zero M ξ ascent x‖ := by
    have h := norm_sub_norm_le x (-w)
    simp only [norm_neg, sub_neg_eq_add, hx] at h
    dsimp [update]
    change 1 - ξ ≤ ‖x + w‖
    linarith
  rw [successfulVector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hp.le)

/-- For a unit input and `0 ≤ ξ ≤ 1`, the successful mass is at least `((1-ξ)/(1+ξ))²`. See
[GaoEtAl2021]. -/
theorem successMass_lower (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (ascent : Bool) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    ((1-ξ)/(1+ξ))^2 ≤ successMass zero M ξ ascent x := by
  have h := successfulVector_norm_ge zero M hξ ascent x hx
  have hp : 0 ≤ (1-ξ)/(1+ξ) := div_nonneg (by linarith) (by linarith)
  unfold successMass
  nlinarith [norm_nonneg (successfulVector zero M ξ ascent x)]

/-- For a unit input and branch parameter `ξ = 1/3`, the successful mass is at least `1/4`. -/
theorem successMass_third (zero : I) (M : Matrix I I ℂ) (ascent : Bool)
    (x : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) :
    (1 / 4 : ℝ) ≤ successMass zero M (1 / 3) ascent x := by
  have h := successfulVector_norm_ge zero M (ξ := 1 / 3) (by norm_num) ascent x hx
  norm_num at h
  unfold successMass
  nlinarith [norm_nonneg (successfulVector zero M (1 / 3) ascent x)]

/-- For a unit input and nonnegative branch parameter, the successful mass lies between zero and
one. -/
theorem successMass_mem_unit (zero : I) (M : Matrix I I ℂ) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (ascent : Bool) (x : EuclideanSpace ℂ I) (hx : ‖x‖ = 1) :
    0 ≤ successMass zero M ξ ascent x ∧ successMass zero M ξ ascent x ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  have h := successfulVector_norm_le zero M hξ ascent x
  rw [hx] at h
  unfold successMass
  nlinarith [norm_nonneg (successfulVector zero M ξ ascent x)]

end Qatlib.Papers.QGradient20.FilterBranch
