/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Algebra
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

/-!
# Normalization of exponential imaginary-time flow

This module differentiates vector normalization along real inner-product-space curves satisfying
a linear evolution equation. The normalized derivative includes the scalar correction that
preserves unit norm.

For complex finite-dimensional matrices, `rawState` is the actual matrix-exponential evolution.
Nonzero initial states remain nonzero, so their normalized curves have unit norm and satisfy
`actual_normalized_ode`, supporting the imaginary-time formulation in [McArdleTew2020].

## Main statements

* `normalized_ode`: the normalization rule for a curve satisfying a linear evolution equation.
* `rawState_ne_zero`: nonvanishing of exponential evolution from a nonzero initial state.
* `actual_normalized_ode`: the differential equation for normalized matrix-exponential
  evolution.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ImaginaryFlow.Normalize
open Matrix NormedSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace

section RealHilbertCurve
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The vector scaled by the reciprocal of its norm. -/
def normalized (v : E) : E := ‖v‖⁻¹ • v

/-- Normalizing a nonzero vector gives a vector of norm one. -/
theorem normalized_norm {v : E} (hv : v ≠ 0) : ‖normalized v‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

/-- At a nonzero point of a differentiable real inner-product-space curve, the norm derivative
is the inner product of the state and its derivative divided by the state norm. -/
theorem hasDerivAt_curve_norm {ψ : ℝ → E} {v : E} {t : ℝ}
    (hψ : HasDerivAt ψ v t) (h0 : ψ t ≠ 0) :
    HasDerivAt (fun s => ‖ψ s‖) (inner ℝ (ψ t) v / ‖ψ t‖) t := by
  have hsq := hψ.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
  have hnorm : (fun s => Real.sqrt (‖ψ s‖ ^ 2)) = fun s => ‖ψ s‖ := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [hnorm, Real.sqrt_sq (norm_nonneg _)] at hsq
  convert! hsq using 1
  field_simp

/-- At a nonzero point of a curve satisfying `ψ' = -H ψ`, its normalization has derivative `-H u
+ inner ℝ u (H u) • u`, where `u` is the normalized state. -/
theorem normalized_ode {ψ : ℝ → E} (H : E →ₗ[ℝ] E) {t : ℝ}
    (hψ : HasDerivAt ψ (-H (ψ t)) t) (h0 : ψ t ≠ 0) :
    HasDerivAt (fun s => normalized (ψ s))
      (- H (normalized (ψ t)) +
        inner ℝ (normalized (ψ t)) (H (normalized (ψ t))) • normalized (ψ t)) t := by
  have hnorm := hasDerivAt_curve_norm hψ h0
  have hinv := hnorm.inv (norm_ne_zero_iff.mpr h0)
  have hd := hinv.smul hψ
  change HasDerivAt (fun s => normalized (ψ s)) _ t at hd
  apply hd.congr_deriv
  dsimp only [normalized, Pi.inv_apply]
  simp only [map_smul, real_inner_smul_left, inner_smul_right, inner_neg_right,
    smul_smul, div_eq_mul_inv]
  module

end RealHilbertCurve

section ActualMatrixExponential
open scoped Matrix.Norms.L2Operator
/-- Complex square matrices indexed by `Fin d`. -/
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
/-- The complex Euclidean state space indexed by `Fin d`. -/
abbrev State (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- The continuous real-linear map sending a matrix to its action on the fixed state `ψ0`. -/
def matrixApply {d : ℕ} (ψ0 : State d) : Op d →L[ℝ] State d :=
  (((LinearMap.applyₗ ψ0).comp
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).toLinearMap).restrictScalars ℝ).toContinuousLinearMap

/-- The finite-dimensional exponential evolution `exp(-t • H)` applied to the initial state
`ψ0`. -/
def rawState {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) : State d :=
  WithLp.toLp 2 (NormedSpace.exp ((-t) • H) *ᵥ ψ0.ofLp)

/-- The raw evolution can equivalently be written using the complex scalar `-(t : ℂ)` in its
matrix exponential. -/
theorem rawState_complex_scalar {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) :
    rawState H ψ0 t = WithLp.toLp 2 (NormedSpace.exp ((-(t : ℂ)) • H) *ᵥ ψ0.ofLp) := by
  simp only [rawState, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_neg]
  rfl

/-- The derivative of the raw exponential evolution is minus the action of `H` on the current
state. -/
theorem rawState_hasDerivAt {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) :
    HasDerivAt (rawState H ψ0) (- Matrix.toEuclideanLin H (rawState H ψ0 t)) t := by
  let : NormedAlgebra ℝ (Op d) := NormedAlgebra.restrictScalars ℝ ℂ _
  have he : HasDerivAt (fun s : ℝ => NormedSpace.exp ((-s) • H))
      ((-H) * NormedSpace.exp ((-t) • H)) t := by
    simpa only [smul_neg, neg_smul] using
      (hasDerivAt_exp_smul_const' (-H) t)
  have hv := (matrixApply ψ0).hasFDerivAt.comp_hasDerivAt t he
  convert! hv using 1
  apply WithLp.ofLp_injective 2
  change -(H *ᵥ (NormedSpace.exp ((-t) • H) *ᵥ ψ0.ofLp)) =
    ((-H) * NormedSpace.exp ((-t) • H)) *ᵥ ψ0.ofLp
  simp only [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_mulVec]

/-- Exponential evolution of a nonzero initial state is nonzero at every real time. -/
theorem rawState_ne_zero {d : ℕ} (H : Op d) (ψ0 : State d) (hψ0 : ψ0 ≠ 0) (t : ℝ) :
    rawState H ψ0 t ≠ 0 := by
  intro hz
  have hv : NormedSpace.exp ((-t) • H) *ᵥ ψ0.ofLp = 0 := by
    have h := congrArg WithLp.ofLp hz
    simpa only [rawState, WithLp.ofLp_toLp, WithLp.ofLp_zero] using h
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp ((-t) • H))
  have hx : ψ0.ofLp = 0 := hi (by simpa only [Matrix.mulVec_zero] using hv)
  apply hψ0
  apply WithLp.ofLp_injective 2
  simpa only [WithLp.ofLp_zero] using hx

local instance (d : ℕ) : InnerProductSpace ℝ (State d) :=
  InnerProductSpace.rclikeToReal ℂ (State d)

/-- The normalized exponential evolution of a nonzero initial state has norm one at every real
time. -/
theorem actual_normalized_norm {d : ℕ} (H : Op d) (ψ0 : State d) (hψ0 : ψ0 ≠ 0) (t : ℝ) :
    ‖normalized (rawState H ψ0 t)‖ = 1 :=
  normalized_norm (rawState_ne_zero H ψ0 hψ0 t)

/-- For a nonzero initial state and any complex matrix `H`, normalized exponential evolution has
derivative `-H u + (inner ℂ u (H u)).re • u` [McArdleTew2020]. -/
theorem actual_normalized_ode {d : ℕ} (H : Op d) (ψ0 : State d) (hψ0 : ψ0 ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => normalized (rawState H ψ0 s))
      (- Matrix.toEuclideanLin H (normalized (rawState H ψ0 t)) +
        (inner ℂ (normalized (rawState H ψ0 t))
          (Matrix.toEuclideanLin H (normalized (rawState H ψ0 t)))).re •
            normalized (rawState H ψ0 t)) t := by
  exact normalized_ode ((Matrix.toEuclideanLin H).restrictScalars ℝ)
    (rawState_hasDerivAt H ψ0 t) (rawState_ne_zero H ψ0 hψ0 t)

end ActualMatrixExponential

end Qatlib.Concepts.ImaginaryFlow.Normalize
