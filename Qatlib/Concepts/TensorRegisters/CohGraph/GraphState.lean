/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

@[expose] public section

/-!
# Normalized coherent graph states

The vector `graphState f` is the equal-amplitude superposition of the tagged basis states `(i, f
i)` over a finite nonempty input type. Its norm is one, and its inner product with another graph
state equals the fraction of agreeing inputs. For background, see [NielsenChuang2010].

## Main statements

* `graph_inner_quotient`: the inner product is the agreement count divided by the input
  cardinality.
* `graphState_norm`: coherent graph states have unit norm.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.TensorRegisters.CohGraph

open scoped ComplexConjugate

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- The coherent superposition of basis vectors `(i, f i)`, each with amplitude `1 /
√(Fintype.card I)`. -/
noncomputable def graphState (f : I → O) : EuclideanSpace ℂ (I × O) :=
  ∑ i, EuclideanSpace.single (i,f i) ((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ)

/-- The inner product of two graph states is their agreement count times the square of the
inverse square root of the input cardinality. -/
theorem graph_inner (f g : I → O) :
    inner ℂ (graphState f) (graphState g) =
      ((Finset.univ.filter (fun i => f i = g i)).card : ℂ) *
        (((Real.sqrt (Fintype.card I : ℝ))⁻¹ : ℂ) ^ 2) := by
  classical
  unfold graphState
  simp only [sum_inner, inner_sum, EuclideanSpace.inner_single_left,
    PiLp.single_apply, map_inv₀, Complex.conj_ofReal]
  simp only [Prod.mk.injEq, ite_and, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, pow_two]

/-- The inner product of two graph states equals the fraction of inputs on which their functions
agree. -/
theorem graph_inner_quotient (f g : I → O) :
    inner ℂ (graphState f) (graphState g) =
      ((Finset.univ.filter (fun i => f i = g i)).card : ℂ) / (Fintype.card I : ℂ) := by
  rw [graph_inner, div_eq_mul_inv]
  congr 1
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [Complex.ofReal_natCast]

variable [Nonempty I]

/-- The coherent graph state of a function on a finite nonempty input type has norm one. -/
theorem graphState_norm (f : I → O) : ‖graphState f‖ = 1 := by
  have h := graph_inner_quotient f f
  simp only [Finset.filter_true, Finset.card_univ] at h
  rw [div_self (by exact_mod_cast Fintype.card_ne_zero)] at h
  have hh := congrArg (RCLike.re : ℂ → ℝ) h
  simp only [inner_self_eq_norm_sq, RCLike.one_re] at hh
  nlinarith [norm_nonneg (graphState f)]

end Qatlib.Concepts.TensorRegisters.CohGraph
