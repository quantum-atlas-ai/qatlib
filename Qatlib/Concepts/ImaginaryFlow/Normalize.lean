/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ImaginaryFlow.Normalize
open Matrix NormedSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace

section RealHilbertCurve
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalized (v : E) : E := ‖v‖⁻¹ • v

theorem normalized_norm {v : E} (hv : v ≠ 0) : ‖normalized v‖ = 1 := by
  rw [normalized, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

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
abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev State (d : ℕ) := EuclideanSpace ℂ (Fin d)

def matrixApply {d : ℕ} (ψ0 : State d) : Op d →L[ℝ] State d :=
  (((LinearMap.applyₗ ψ0).comp
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).toLinearMap).restrictScalars ℝ).toContinuousLinearMap

def rawState {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) : State d :=
  WithLp.toLp 2 (NormedSpace.exp ((-t) • H) *ᵥ ψ0.ofLp)

theorem rawState_complex_scalar {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) :
    rawState H ψ0 t = WithLp.toLp 2 (NormedSpace.exp ((-(t : ℂ)) • H) *ᵥ ψ0.ofLp) := by
  simp only [rawState, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_neg]
  rfl

theorem rawState_hasDerivAt {d : ℕ} (H : Op d) (ψ0 : State d) (t : ℝ) :
    HasDerivAt (rawState H ψ0) (- Matrix.toEuclideanLin H (rawState H ψ0 t)) t := by
  letI : NormedAlgebra ℝ (Op d) := NormedAlgebra.restrictScalars ℝ ℂ _
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

theorem actual_normalized_norm {d : ℕ} (H : Op d) (ψ0 : State d) (hψ0 : ψ0 ≠ 0) (t : ℝ) :
    ‖normalized (rawState H ψ0 t)‖ = 1 :=
  normalized_norm (rawState_ne_zero H ψ0 hψ0 t)

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
