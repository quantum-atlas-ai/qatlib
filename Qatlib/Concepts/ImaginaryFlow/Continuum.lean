/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
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
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Monoid
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.TypeTags
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# Continuum transcorrelated differential expressions

This module defines coordinate derivatives, the differential expression `schrodingerAction`, and
multiplication by a real function or its exponential. Product rules give the explicit action of
exponential conjugation used in transcorrelated methods [McArdleTew2020].

The first two commutators with multiplication by `g` are computed directly, and all commutators
of order at least three vanish for twice continuously differentiable inputs.
`actual_continuum_bch` expresses the conjugated action as the resulting finite commutator
expansion.

## Main statements

* `actual_continuum_tc_action`: the explicit differential correction under exponential
  conjugation.
* `actual_continuum_bch`: the finite commutator formula.
* `higherCommutator_zero`: vanishing of all commutators of order at least three.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ImaginaryFlow.Continuum
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise multiplication of a vector-valued function by the real scalar `exp (g x)`. -/
def expMultiply {X : Type*} (g : X → ℝ) (f : X → E) : X → E :=
  fun x => Real.exp (g x) • f x

/-- For differentiable `g` and `f`, the derivative of `expMultiply g f` is `exp(g)` times `g' •
f + f'`. -/
theorem deriv_expMultiply (g : ℝ → ℝ) (f : ℝ → E)
    (hg : Differentiable ℝ g) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (expMultiply g f) x =
      Real.exp (g x) • (deriv g x • f x + deriv f x) := by
  have hd := ((hg x).hasDerivAt.exp).smul ((hf x).hasDerivAt)
  change HasDerivAt (expMultiply g f) _ x at hd
  rw [hd.deriv]
  module

/-- For twice continuously differentiable functions, the second derivative of `exp(g) • f` is
`exp(g) • (f'' + 2*g' • f' + (g''+(g')^2) • f)`. -/
theorem secondDeriv_expMultiply (g : ℝ → ℝ) (f : ℝ → E)
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (expMultiply g f)) x =
      Real.exp (g x) • (deriv (deriv f) x +
        (2 * deriv g x) • deriv f x +
        (deriv (deriv g) x + deriv g x ^ 2) • f x) := by
  have hgd := hg.differentiable (by norm_num)
  have hfd := hf.differentiable (by norm_num)
  have hfirst : deriv (expMultiply g f) =
      fun t => Real.exp (g t) • (deriv g t • f t + deriv f t) := by
    ext t
    exact deriv_expMultiply g f hgd hfd t
  have hd := ((hgd x).hasDerivAt.exp).smul
    ((((hg.differentiable_deriv_two x).hasDerivAt).smul ((hfd x).hasDerivAt)).add
      ((hf.differentiable_deriv_two x).hasDerivAt))
  change HasDerivAt (fun t => Real.exp (g t) • (deriv g t • f t + deriv f t)) _ x at hd
  rw [hfirst, hd.deriv]
  dsimp only [Pi.add_apply, Pi.smul_apply']
  module

/-- The affine coordinate line through `x` in the direction of the `j`th standard basis vector. -/
def coordinateLine {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) : Fin n → ℝ :=
  x + t • Pi.single j 1

/-- The first derivative at zero of a function restricted to the `j`th coordinate line through
`x`. -/
def firstPartial {n : ℕ} (f : (Fin n → ℝ) → E) (j : Fin n) (x : Fin n → ℝ) : E :=
  deriv (fun t => f (coordinateLine x j t)) 0

/-- The second derivative at zero of a function restricted to the `j`th coordinate line through
`x`. -/
def secondPartial {n : ℕ} (f : (Fin n → ℝ) → E) (j : Fin n) (x : Fin n → ℝ) : E :=
  deriv (deriv (fun t => f (coordinateLine x j t))) 0

/-- Every coordinate line is twice continuously differentiable. -/
theorem coordinateLine_contDiff {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    ContDiff ℝ 2 (coordinateLine x j) :=
  contDiff_const.add (contDiff_id.smul_const (Pi.single j 1))

/-- For twice continuously differentiable `g` and `f`, the second coordinate derivative of
`exp(g) • f` satisfies the exponential product rule. -/
theorem secondPartial_expMultiply {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (j : Fin n) (x : Fin n → ℝ) :
    secondPartial (expMultiply g f) j x = Real.exp (g x) •
      (secondPartial f j x + (2 * firstPartial g j x) • firstPartial f j x +
        (secondPartial g j x + firstPartial g j x ^ 2) • f x) := by
  have h := secondDeriv_expMultiply
    (fun t => g (coordinateLine x j t)) (fun t => f (coordinateLine x j t))
    (hg.comp (coordinateLine_contDiff x j)) (hf.comp (coordinateLine_contDiff x j)) 0
  simpa only [secondPartial, firstPartial, expMultiply, coordinateLine, zero_smul, add_zero] using!
      h

/-- The differential expression given by minus one half the sum of second coordinate derivatives
plus multiplication by `V`. -/
def schrodingerAction {n : ℕ} (V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (x : Fin n → ℝ) : E :=
  -(1 / 2 : ℝ) • (∑ j, secondPartial f j x) + V x • f x

/-- The coordinate correction `∂g • ∂f + (1/2) • ((∂²g + (∂g)^2) • f)` for exponential
conjugation of the Schrödinger differential expression. -/
def correction {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (j : Fin n) (x : Fin n → ℝ) : E :=
  firstPartial g j x • firstPartial f j x +
    (1 / 2 : ℝ) • ((secondPartial g j x + firstPartial g j x ^ 2) • f x)

/-- For twice continuously differentiable `g` and `f`, conjugating the Schrödinger differential
expression by multiplication by `exp(g)` subtracts the sum of coordinate corrections
[McArdleTew2020]. -/
theorem actual_continuum_tc_action {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x - ∑ j, correction g f j x := by
  have he : Real.exp (-g x) * Real.exp (g x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscale (c : ℝ) (v : E) :
      Real.exp (-g x) • (c • (Real.exp (g x) • v)) = c • v := by
    simp only [smul_smul]
    have hc : Real.exp (-g x) * (c * Real.exp (g x)) = c := by
      calc
        _ = c * (Real.exp (-g x) * Real.exp (g x)) := by ring
        _ = c := by rw [he, mul_one]
    rw [hc]
  have hsum : (∑ j, secondPartial (expMultiply g f) j x) = Real.exp (g x) •
      (∑ j, (secondPartial f j x + (2 * firstPartial g j x) • firstPartial f j x +
        (secondPartial g j x + firstPartial g j x ^ 2) • f x)) := by
    simp_rw [secondPartial_expMultiply g f hg hf]
    rw [Finset.smul_sum]
  unfold schrodingerAction
  rw [hsum]
  change Real.exp (-g x) •
    (-(1 / 2 : ℝ) • (Real.exp (g x) • _) + V x • (Real.exp (g x) • f x)) = _
  rw [smul_add, hscale, hscale]
  have hterm (j : Fin n) :
      -(1 / 2 : ℝ) • (secondPartial f j x + (2 * firstPartial g j x) • firstPartial f j x +
        (secondPartial g j x + firstPartial g j x ^ 2) • f x) =
      -(1 / 2 : ℝ) • secondPartial f j x - correction g f j x := by
    unfold correction
    module
  rw [Finset.smul_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
    ← Finset.smul_sum]
  module

/-- Pointwise multiplication of a vector-valued function by a real-valued function. -/
def multiply {X : Type*} (g : X → ℝ) (f : X → E) : X → E := fun x => g x • f x

/-- Pointwise scalar multiplication satisfies the first-derivative product rule for
differentiable functions. -/
theorem deriv_multiply (g : ℝ → ℝ) (f : ℝ → E)
    (hg : Differentiable ℝ g) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (multiply g f) x = deriv g x • f x + g x • deriv f x := by
  have hd := (hg x).hasDerivAt.smul (hf x).hasDerivAt
  change HasDerivAt (multiply g f) _ x at hd
  rw [hd.deriv]
  module

/-- Pointwise scalar multiplication satisfies the second-derivative product rule for twice
continuously differentiable functions. -/
theorem secondDeriv_multiply (g : ℝ → ℝ) (f : ℝ → E)
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (multiply g f)) x = deriv (deriv g) x • f x +
      (2 * deriv g x) • deriv f x + g x • deriv (deriv f) x := by
  have hgd := hg.differentiable (by norm_num)
  have hfd := hf.differentiable (by norm_num)
  have hfirst : deriv (multiply g f) = fun t => deriv g t • f t + g t • deriv f t := by
    ext t
    exact deriv_multiply g f hgd hfd t
  have hd := (((hg.differentiable_deriv_two x).hasDerivAt).smul ((hfd x).hasDerivAt)).add
    (((hgd x).hasDerivAt).smul ((hf.differentiable_deriv_two x).hasDerivAt))
  change HasDerivAt (fun t => deriv g t • f t + g t • deriv f t) _ x at hd
  rw [hfirst, hd.deriv]
  module

/-- The first coordinate derivative of a scalar-vector product satisfies the product rule for
twice continuously differentiable factors. -/
theorem firstPartial_multiply {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (j : Fin n) (x : Fin n → ℝ) :
    firstPartial (multiply g f) j x =
      firstPartial g j x • f x + g x • firstPartial f j x := by
  have h := deriv_multiply (fun t => g (coordinateLine x j t))
    (fun t => f (coordinateLine x j t))
    ((hg.comp (coordinateLine_contDiff x j)).differentiable (by norm_num))
    ((hf.comp (coordinateLine_contDiff x j)).differentiable (by norm_num)) 0
  simpa only [firstPartial, multiply, coordinateLine, zero_smul, add_zero] using! h

/-- The second coordinate derivative of a scalar-vector product is the sum of the two
second-derivative terms and twice the product of first derivatives. -/
theorem secondPartial_multiply {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (j : Fin n) (x : Fin n → ℝ) :
    secondPartial (multiply g f) j x = secondPartial g j x • f x +
      (2 * firstPartial g j x) • firstPartial f j x + g x • secondPartial f j x := by
  have h := secondDeriv_multiply (fun t => g (coordinateLine x j t))
    (fun t => f (coordinateLine x j t))
    (hg.comp (coordinateLine_contDiff x j)) (hf.comp (coordinateLine_contDiff x j)) 0
  simpa only [secondPartial, firstPartial, multiply, coordinateLine, zero_smul, add_zero] using! h

/-- The commutator of the Schrödinger differential expression with multiplication by `g`, acting
on `f`. -/
def firstCommutator {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) : (Fin n → ℝ) → E :=
  fun x => schrodingerAction V (multiply g f) x - g x • schrodingerAction V f x

/-- The coordinate expression `∂g • ∂f + (1/2) • (∂²g • f)` for the negative first commutator. -/
def firstCorrection {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (j : Fin n) (x : Fin n → ℝ) : E :=
  firstPartial g j x • firstPartial f j x + (1 / 2 : ℝ) • (secondPartial g j x • f x)

/-- For twice continuously differentiable `g` and `f`, the first commutator is minus the sum of
the coordinate first corrections. -/
theorem firstCommutator_action {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) : firstCommutator g V f x = - ∑ j, firstCorrection g f j x := by
  have hterm (j : Fin n) : -(1 / 2 : ℝ) • secondPartial (multiply g f) j x =
      g x • (-(1 / 2 : ℝ) • secondPartial f j x) - firstCorrection g f j x := by
    rw [secondPartial_multiply g f hg hf]
    unfold firstCorrection
    module
  unfold firstCommutator schrodingerAction
  rw [Finset.smul_sum]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
  dsimp only [multiply]
  module

/-- The commutator of `firstCommutator` with multiplication by `g`. -/
def secondCommutator {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) : (Fin n → ℝ) → E :=
  fun x => firstCommutator g V (multiply g f) x - g x • firstCommutator g V f x

/-- For twice continuously differentiable `g` and `f`, the second commutator is multiplication
by minus the sum of squared first coordinate derivatives of `g`. -/
theorem secondCommutator_action {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) :
    secondCommutator g V f x = - ∑ j, (firstPartial g j x ^ 2) • f x := by
  have hmul : ContDiff ℝ 2 (multiply g f) := hg.smul hf
  have hterm (j : Fin n) : firstCorrection g (multiply g f) j x -
      g x • firstCorrection g f j x = (firstPartial g j x ^ 2) • f x := by
    unfold firstCorrection
    rw [firstPartial_multiply g f hg hf]
    dsimp only [multiply]
    module
  unfold secondCommutator
  rw [firstCommutator_action g V (multiply g f) hg hmul,
    firstCommutator_action g V f hg hf]
  calc
    -(∑ j, firstCorrection g (multiply g f) j x) - g x • (-(∑ j, firstCorrection g f j x)) =
        -((∑ j, firstCorrection g (multiply g f) j x) - g x • (∑ j, firstCorrection g f j x)) := by
      module
    _ = -(∑ j, (firstCorrection g (multiply g f) j x - g x • firstCorrection g f j x)) := by
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
    _ = -(∑ j, (firstPartial g j x ^ 2) • f x) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j)]

/-- The commutator of `secondCommutator` with multiplication by `g`. -/
def thirdCommutator {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) : (Fin n → ℝ) → E :=
  fun x => secondCommutator g V (multiply g f) x - g x • secondCommutator g V f x

/-- For twice continuously differentiable `g` and `f`, the third commutator with multiplication
by `g` vanishes. -/
theorem thirdCommutator_zero {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) : thirdCommutator g V f x = 0 := by
  have hmul : ContDiff ℝ 2 (multiply g f) := hg.smul hf
  unfold thirdCommutator
  rw [secondCommutator_action g V (multiply g f) hg hmul,
    secondCommutator_action g V f hg hf]
  have hsum : (∑ j, (firstPartial g j x ^ 2) • multiply g f x) =
      g x • (∑ j, (firstPartial g j x ^ 2) • f x) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [multiply]
    module
  rw [hsum]
  module

/-- For twice continuously differentiable `g` and `f`, exponential conjugation equals the
Schrödinger action plus the first commutator and one half the second commutator
[McArdleTew2020]. -/
theorem actual_continuum_bch {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (x : Fin n → ℝ) :
    Real.exp (-g x) • schrodingerAction V (expMultiply g f) x =
      schrodingerAction V f x + firstCommutator g V f x +
        (1 / 2 : ℝ) • secondCommutator g V f x := by
  rw [actual_continuum_tc_action g V f hg hf,
    firstCommutator_action g V f hg hf, secondCommutator_action g V f hg hf]
  have hterm (j : Fin n) : correction g f j x = firstCorrection g f j x +
      (1 / 2 : ℝ) • ((firstPartial g j x ^ 2) • f x) := by
    unfold correction firstCorrection
    module
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
    ← Finset.smul_sum]
  module

/-- Repeated commutation with multiplication by `g`, starting from the Schrödinger differential
expression at order zero. -/
def iteratedCommutator {n : ℕ} (g V : (Fin n → ℝ) → ℝ) :
    ℕ → ((Fin n → ℝ) → E) → (Fin n → ℝ) → E
  | 0, f => schrodingerAction V f
  | k + 1, f => fun x => iteratedCommutator g V k (multiply g f) x -
      g x • iteratedCommutator g V k f x

/-- For twice continuously differentiable `g` and `f`, every iterated commutator of order `k+3`
vanishes. -/
theorem higherCommutator_zero {n : ℕ} (g V : (Fin n → ℝ) → ℝ)
    (f : (Fin n → ℝ) → E) (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 2 f)
    (k : ℕ) (x : Fin n → ℝ) : iteratedCommutator g V (k + 3) f x = 0 := by
  induction k generalizing f with
  | zero => exact thirdCommutator_zero g V f hg hf x
  | succ k ih =>
    change iteratedCommutator g V (k + 3) (multiply g f) x -
      g x • iteratedCommutator g V (k + 3) f x = 0
    rw [ih (multiply g f) (hg.smul hf), ih f hf, smul_zero, sub_self]

/-- The second coordinate derivative equals the first coordinate derivative of the first
coordinate derivative. -/
theorem secondPartial_eq_iterated_first {n : ℕ} (f : (Fin n → ℝ) → E)
    (j : Fin n) (x : Fin n → ℝ) :
    secondPartial f j x = firstPartial (fun y => firstPartial f j y) j x := by
  have hline (t u : ℝ) : coordinateLine (coordinateLine x j t) j u =
      coordinateLine x j (t + u) := by
    unfold coordinateLine
    rw [add_smul]
    abel
  have heq : (fun t => firstPartial f j (coordinateLine x j t)) =
      deriv (fun t => f (coordinateLine x j t)) := by
    ext t
    change deriv (fun u => f (coordinateLine (coordinateLine x j t) j u)) 0 = _
    simp_rw [hline]
    simpa only [add_zero] using
      (deriv_comp_const_add (fun u => f (coordinateLine x j u)) t 0)
  change deriv (deriv (fun t => f (coordinateLine x j t))) 0 =
    deriv (fun t => firstPartial f j (coordinateLine x j t)) 0
  rw [heq]

end Qatlib.Concepts.ImaginaryFlow.Continuum
