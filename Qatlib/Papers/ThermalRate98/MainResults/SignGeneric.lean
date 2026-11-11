/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Real amplitude recovery from connected edge data

This module proves algebraic uniqueness statements for real amplitude recovery, related to the
sign reconstruction discussion of [LidarWang1999]. Squared sums and differences determine the
product of two amplitudes, and equality of edge products propagates equality from a root through
a reachable relation when the reference amplitudes are nonzero.

A positive root convention together with equal squared amplitudes supplies the root equality
needed for uniqueness of the entire function.

## Main statements

* `edge_product_unique`: recovers equality of products from squared sum and difference data.
* `sign_eq_of_connected`: propagates root equality along reachable edges with matching products.
* `sign_function_eq_of_connected_pos`: derives function equality using positive root values.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults

/-- The product of two real numbers is one quarter of the difference between their squared sum
and squared difference. See [LidarWang1999]. -/
theorem edge_product_from_sums (a b : ℝ) :
    a * b = ((a + b) ^ 2 - (a - b) ^ 2) / 4 := by
  ring

/-- Equal squared sums and equal squared differences of two real pairs force equality of their
products. See [LidarWang1999]. -/
theorem edge_product_unique (a b a' b' : ℝ)
    (hsum : (a' + b') ^ 2 = (a + b) ^ 2)
    (hdiff : (a' - b') ^ 2 = (a - b) ^ 2) :
    a' * b' = a * b := by
  nlinarith

/-- If every vertex is reachable from the root, matching edge products and equal root values
force pointwise equality when the reference function is everywhere nonzero. -/
theorem sign_eq_of_connected {V : Type*} (r : V → V → Prop) (root : V)
    (s t : V → ℝ) (hs0 : ∀ v, s v ≠ 0)
    (hroot : s root = t root)
    (hedge : ∀ v w, r v w → s v * s w = t v * t w)
    (hconn : ∀ v, Relation.ReflTransGen r root v) :
    ∀ v, s v = t v := by
  have key : ∀ {a b : V}, Relation.ReflTransGen r a b → s a = t a → s b = t b := by
    intro a b hab
    induction hab using Relation.ReflTransGen.trans_induction_on with
    | refl => intro h; exact h
    | single h =>
        intro ha
        have hprod := hedge _ _ h
        rw [← ha] at hprod
        exact mul_left_cancel₀ (hs0 _) hprod
    | trans h1 h2 ih1 ih2 => intro ha; exact ih2 (ih1 ha)
  intro v
  exact key (hconn v) hroot

/-- Two real functions are equal when their root values and edge products agree, every vertex is
reachable from the root, and the reference function is everywhere nonzero. -/
theorem sign_function_eq_of_connected {V : Type*} (r : V → V → Prop) (root : V)
    (s t : V → ℝ) (hs0 : ∀ v, s v ≠ 0)
    (hroot : s root = t root)
    (hedge : ∀ v w, r v w → s v * s w = t v * t w)
    (hconn : ∀ v, Relation.ReflTransGen r root v) :
    s = t := by
  funext v
  exact sign_eq_of_connected r root s t hs0 hroot hedge hconn v

/-- On a relation reachable from the root, equal squared amplitudes, equal edge products, and
positive root values determine the same real function when the reference function is
everywhere nonzero. See [LidarWang1999]. -/
theorem sign_function_eq_of_connected_pos {V : Type*} (r : V → V → Prop) (root : V)
    (s t : V → ℝ) (hs0 : ∀ v, s v ≠ 0)
    (hroot : 0 < s root) (hroot' : 0 < t root)
    (habs : ∀ v, s v ^ 2 = t v ^ 2)
    (hedge : ∀ v w, r v w → s v * s w = t v * t w)
    (hconn : ∀ v, Relation.ReflTransGen r root v) :
    s = t := by
  apply sign_function_eq_of_connected r root s t hs0 _ hedge hconn
  have h := habs root
  nlinarith

end Qatlib.Papers.ThermalRate98.MainResults
