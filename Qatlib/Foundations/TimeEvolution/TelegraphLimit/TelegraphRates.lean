/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Rates and coefficients for the telegraph limit

This module defines the discriminant `discr`, slow and fast decay rates, and the mixing
coefficient `coeff` for scalar telegraph modes. For positive `δ`, nonnegative `a`, and `4 * δ *
a ≤ 3/4`, it proves bounds on these quantities, their characteristic equations, and the identity
imposing zero initial derivative.

The mathematical background is discussed in [JinLiu2024].

## Main statements

* `discr_bounds`: bounds the square-root discriminant between one half and one.
* `rate_bounds`: compares the two rates and bounds their corrections.
* `characteristic` and `zero_initial_flux`: the algebraic identities for the telegraph solution.

## References

* [Jin and Liu, 2024][JinLiu2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Foundations.TimeEvolution.TelegraphLimit

/-- The square-root discriminant `sqrt (1 - 4 * δ * a)`. -/
def discr (δ a : ℝ) : ℝ := Real.sqrt (1-4*δ*a)

/-- The rationalized slow decay rate `2 * a / (1 + discr δ a)`. -/
def slow (δ a : ℝ) : ℝ := 2*a/(1+discr δ a)

/-- The fast decay rate `(1 + discr δ a) / (2 * δ)`. -/
def fast (δ a : ℝ) : ℝ := (1+discr δ a)/(2*δ)

/-- The mixing coefficient `(1 - discr δ a) / (2 * discr δ a)`. -/
def coeff (δ a : ℝ) : ℝ := (1-discr δ a)/(2*discr δ a)

/-- For positive `δ`, nonnegative `a`, and `4 * δ * a ≤ 3/4`, the discriminant lies between one
half and one and its square is `1 - 4 * δ * a`. -/
theorem discr_bounds {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    1/2 ≤ discr δ a ∧ discr δ a ≤ 1 ∧ (discr δ a)^2=1-4*δ*a := by
  have h0 : 0 ≤ 1-4*δ*a := by linarith
  have hs := Real.sq_sqrt h0
  have hn := Real.sqrt_nonneg (1-4*δ*a)
  have hp : 0 ≤ δ*a := mul_nonneg hδ.le ha
  dsimp [discr]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · exact hs

/-- Under the stated rate restrictions, the slow-rate correction is `4 * δ * a ^ 2 / (1 + discr
δ a) ^ 2`. -/
theorem slow_gap {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    slow δ a-a=4*δ*a^2/(1+discr δ a)^2 := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  dsimp [slow]
  field_simp
  nlinarith [hs]

/-- Under the stated rate restrictions, the mixing coefficient equals `2 * δ * a / (discr δ a *
(1 + discr δ a))`. -/
theorem coeff_eq {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    coeff δ a=2*δ*a/(discr δ a*(1+discr δ a)) := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hz : discr δ a≠0 := by linarith
  have hp : 1+discr δ a≠0 := by linarith
  dsimp [coeff]
  field_simp
  nlinarith [hs]

/-- Under the stated restrictions, `a ≤ slow δ a ≤ fast δ a`, the coefficient lies in `[0, 4 * δ
* a]`, and the slow-rate correction is at most `4 * δ * a ^ 2`. -/
theorem rate_bounds {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    a  ≤  slow δ a ∧ slow δ a  ≤  fast δ a ∧
    0 ≤ coeff δ a ∧ coeff δ a ≤ 4*δ*a ∧ slow δ a-a ≤ 4*δ*a^2 := by
  obtain ⟨hd,hd1,hs⟩ := discr_bounds hδ ha hm
  have hp : 0<1+discr δ a := by linarith
  have hz : 0<discr δ a := by linarith
  have hg := slow_gap hδ ha hm
  have hc := coeff_eq hδ ha hm
  have hgap : 0 ≤ slow δ a-a := by rw [hg]; positivity
  have hfg : slow δ a  ≤  fast δ a := by
    dsimp [slow,fast]
    rw [div_le_div_iff₀ hp (by positivity : 0<2*δ)]
    nlinarith [sq_nonneg (discr δ a)]
  refine ⟨by linarith,hfg,?_,?_,?_⟩
  · rw [hc]; positivity
  · rw [hc]
    apply (div_le_iff₀ (mul_pos hz hp)).mpr
    have hh : 1/2 ≤ discr δ a*(1+discr δ a) := by nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ δ*a) (show 0 ≤ discr δ a*(1+discr δ a)-1/2 by linarith)]
  · rw [hg]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    have hh : 1 ≤ (1+discr δ a)^2 := by nlinarith
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4*δ*a^2) (show 0 ≤ (1+discr δ a)^2-1 by linarith)]

/-- Under the stated restrictions, both decay rates satisfy the quadratic equation `δ * rate ^ 2
- rate + a = 0`. -/
theorem characteristic {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    δ*(slow δ a)^2-slow δ a+a=0 ∧ δ*(fast δ a)^2-fast δ a+a=0 := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  have hz : δ≠0 := ne_of_gt hδ
  constructor
  · dsimp [slow]
    field_simp
    nlinarith [mul_nonneg ha (show 0 ≤ δ from hδ.le)]
  · dsimp [fast]
    field_simp
    nlinarith [hs]

/-- Under the stated rate restrictions, `(1 + coeff δ a) * slow δ a = coeff δ a * fast δ a`, so
the two derivative contributions cancel initially. -/
theorem zero_initial_flux {δ a : ℝ} (hδ : 0<δ) (ha : 0 ≤ a) (hm : 4*δ*a ≤ 3/4) :
    (1+coeff δ a)*slow δ a=coeff δ a*fast δ a := by
  obtain ⟨hd,_,hs⟩ := discr_bounds hδ ha hm
  have hp : 1+discr δ a≠0 := by linarith
  have hz : discr δ a≠0 := by linarith
  have hδz := ne_of_gt hδ
  dsimp [coeff,slow,fast]
  field_simp
  nlinarith [hs]
end Qatlib.Foundations.TimeEvolution.TelegraphLimit
