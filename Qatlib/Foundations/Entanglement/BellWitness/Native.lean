/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-!
# Finite state vectors and rank-one projectors

This module represents finite quantum state vectors by `QState`, defines `Inner`, `TensorState`,
and `outerProduct`, and relates normalization to the inner product. It proves projector and
unitary reflection identities for normalized vectors.

The final trace-norm estimate bounds the real quadratic form of a traceless matrix by half its
trace norm. These finite-dimensional quantum information constructions follow the background of
[NielsenChuang2010].

## Main statements

* `outerProduct_projector`: The outer product of a normalized vector is idempotent and
  Hermitian.
* `outerProduct_reflection_unitary`: The reflection defined by the outer product of a normalized
  vector is unitary.
* `abs_quadratic_re_le_half_traceNorm`: For a traceless matrix and a normalized vector, the
  absolute real part of the quadratic form is at most half the matrix trace norm.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace Qatlib.Foundations.Entanglement.BellWitness

/-- Complex coordinate functions indexed by `I`, representing state vectors. -/
abbrev QState (I : Type*) := I → ℂ

/-- A vector is normalized when the sum of the squared norms of its coordinates equals one. -/
def Normalized {I : Type*} [Fintype I] (v : QState I) : Prop := ∑i,‖v i‖^2=1

/-- The tensor product vector on pairs of indices, with coordinates `a i * b j`. -/
def TensorState {I J : Type*} (a : QState I) (b : QState J) : QState (I × J) := fun p=>a p.1*b p.2

/-- The finite complex inner product, conjugate linear in the first argument. -/
def Inner {I : Type*} [Fintype I] (a b : QState I) : ℂ := star a ⬝ᵥ b
variable {I : Type*} [Fintype I]

/-- The inner product is the sum of conjugated coordinates of the first vector times coordinates
of the second. -/
theorem inner_apply (ψ φ : QState I) : Inner ψ φ = ∑ i, (starRingEnd ℂ) (ψ i) * φ i := by
  simp only [Inner, dotProduct, Pi.star_apply, RCLike.star_def]

/-- The self-inner product is the complex coercion of the sum of squared coordinate norms. -/
theorem inner_self (ψ : QState I) : Inner ψ ψ = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- A vector is normalized if and only if its self-inner product equals one. -/
theorem normalized_iff_inner_self (ψ : QState I) : Normalized ψ ↔ Inner ψ ψ = 1 := by
  rw [inner_self, ← Complex.ofReal_sum]
  unfold Normalized
  exact_mod_cast Iff.rfl

/-- The tensor product of normalized finite vectors is normalized. -/
theorem normalized_tensorState {J : Type*} [Fintype J] {a : QState I} {b : QState J}
    (ha : Normalized a) (hb : Normalized b) : Normalized (TensorState a b) := by
  unfold Normalized TensorState
  simp only [Fintype.sum_prod_type,norm_mul,mul_pow,← Finset.mul_sum,← Finset.sum_mul]
  rw [ha,hb,one_mul]

/-- Complex conjugation interchanges the arguments of the inner product. -/
theorem star_inner (a b : QState I) : star (Inner a b)=Inner b a := by
  simp only [Inner,dotProduct,Pi.star_apply,star_sum,star_mul,star_star]

/-- The outer product matrix with entries `ψ i * conj(ψ j)`. -/
noncomputable def outerProduct (ψ : QState I) : Matrix I I ℂ :=
  Matrix.of fun i j => ψ i * (starRingEnd ℂ) (ψ j)

omit [Fintype I] in

/-- The entry of the outer product is the corresponding coordinate times the conjugate
coordinate. -/
theorem outerProduct_apply (ψ : QState I) (i j : I) :
    outerProduct ψ i j = ψ i * (starRingEnd ℂ) (ψ j) := rfl

/-- The outer product of `ψ` acts on `φ` by multiplying `ψ` by their inner product. -/
theorem outerProduct_mulVec (ψ φ : QState I) :
    outerProduct ψ *ᵥ φ = (Inner ψ φ) • ψ := by
  funext i
  have h : (∑ j, ψ i * (starRingEnd ℂ) (ψ j) * φ j)
      = (∑ j, (starRingEnd ℂ) (ψ j) * φ j) * ψ i := by
    rw [Finset.sum_mul Finset.univ (fun j => (starRingEnd ℂ) (ψ j) * φ j) (ψ i)]
    exact Finset.sum_congr rfl fun j _ => by ring
  simpa using! h

/-- The self-inner product of a normalized vector equals one. -/
theorem inner_self_eq_one {ψ : QState I} (hψ : Normalized ψ) : Inner ψ ψ = 1 := by
  rw [normalized_iff_inner_self] at hψ
  exact hψ

/-- The outer product of a normalized vector is idempotent and Hermitian. -/
theorem outerProduct_projector {ψ : QState I} (hψ : Normalized ψ) :
    outerProduct ψ*outerProduct ψ=outerProduct ψ ∧ (outerProduct ψ)ᴴ=outerProduct ψ := by
  constructor
  · show outerProduct ψ * outerProduct ψ = outerProduct ψ
    ext i j
    simp only [outerProduct, Matrix.mul_apply, Matrix.of_apply]
    have hterm : ∀ k : I,
        ψ i * (starRingEnd ℂ) (ψ k) * (ψ k * (starRingEnd ℂ) (ψ j))
          = ((starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)) :=
      fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k, ((starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)))
        = (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) * (ψ i * (starRingEnd ℂ) (ψ j)) from
      (Finset.sum_mul Finset.univ (fun k => (starRingEnd ℂ) (ψ k) * ψ k)
        (ψ i * (starRingEnd ℂ) (ψ j))).symm]
    rw [show (∑ k, (starRingEnd ℂ) (ψ k) * ψ k) = Inner ψ ψ from rfl,
      inner_self_eq_one hψ, one_mul]
  · show (outerProduct ψ)ᴴ = outerProduct ψ
    ext i j
    simp only [outerProduct, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def,
      map_mul]
    rw [show (starRingEnd ℂ) ((starRingEnd ℂ) (ψ i)) = ψ i from star_star _]
    ring

variable [DecidableEq I]

/-- The matrix `2P - 1`, which is a reflection when `P` is an orthogonal projector. -/
def ReflectionAbout (P : Matrix I I ℂ) : Matrix I I ℂ := (2 : ℂ) • P-1

/-- The reflection defined by the outer product of a normalized vector is unitary. -/
theorem outerProduct_reflection_unitary {ψ : QState I} (hψ : Normalized ψ) :
    ReflectionAbout (outerProduct ψ) ∈ Matrix.unitaryGroup I ℂ := by
  obtain ⟨hid,hstar⟩ := outerProduct_projector hψ
  have hm : ReflectionAbout (outerProduct ψ)*ReflectionAbout (outerProduct ψ)=1 := by
    simp only [ReflectionAbout,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hid]
    module
  have hs : (ReflectionAbout (outerProduct ψ))ᴴ=ReflectionAbout (outerProduct ψ) := by
    simp [ReflectionAbout,hstar]
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,hs]
  exact hm

/-- The trace of `outerProduct z * X` equals the quadratic form of `X` at `z`. -/
theorem trace_outerProduct_mul_eq_quadratic
    {I : Type*} [Fintype I] [DecidableEq I] (z : QState I) (X : Matrix I I ℂ) :
    (outerProduct z * X).trace = star z ⬝ᵥ X *ᵥ z := by
  classical
  simp only [Matrix.trace, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change z i*star (z j)*X j i = star (z j)*(X j i*z i)
  ring

/-- For a traceless matrix and a normalized vector, the absolute real part of the quadratic form
is at most half the matrix trace norm. -/
theorem abs_quadratic_re_le_half_traceNorm
    {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ)
    (htrace : X.trace = 0) (z : QState I) (hz : Normalized z) :
    |(star z ⬝ᵥ X *ᵥ z).re| ≤ (1/2 : ℝ)*X.traceNorm := by
  classical
  let U := ReflectionAbout (outerProduct z)
  have hu : U.Isometry := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using!
      outerProduct_reflection_unitary hz
  have ht : (U*X).trace = 2*(outerProduct z*X).trace := by
    simp only [U, ReflectionAbout, sub_mul, smul_mul_assoc, one_mul,
      Matrix.trace_sub, Matrix.trace_smul, htrace, sub_zero]
    rfl
  have hb := Matrix.abs_trace_le_traceNorm (U*X)
  rw [Matrix.traceNorm_isometry_left (by convert! hu using 1), ht, norm_mul] at hb
  norm_num at hb
  rw [← trace_outerProduct_mul_eq_quadratic]
  have hr := Complex.abs_re_le_norm ((outerProduct z*X).trace)
  linarith

end Qatlib.Foundations.Entanglement.BellWitness
