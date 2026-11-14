/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

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
