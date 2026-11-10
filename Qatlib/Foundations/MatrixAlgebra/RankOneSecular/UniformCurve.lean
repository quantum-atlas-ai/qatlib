/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

def uniformCurve (d : I → ℝ) (z : ℝ) : ℝ :=
  (1/(Fintype.card I:ℝ))*∑ i,(d i-z)⁻¹

omit [DecidableEq I] [Nonempty I] in

theorem uniformCurve_continuousOn (d : I → ℝ) (S : Set ℝ)
    (hpole : ∀ i z,z∈S → d i≠z) : ContinuousOn (uniformCurve d) S := by
  unfold uniformCurve
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro i _
  exact (continuousOn_const.sub continuousOn_id).inv₀ (fun z hz => sub_ne_zero.mpr (hpole i z hz))

theorem reciprocal_increasing (d x y : ℝ) (hxy : x<y) (hprod : 0<(d-y)*(d-x)) :
    (d-x)⁻¹<(d-y)⁻¹ := by
  have hne : (d-y)*(d-x)≠0 := ne_of_gt hprod
  have hx : d-x≠0 := (mul_ne_zero_iff.mp hne).2
  have hy : d-y≠0 := (mul_ne_zero_iff.mp hne).1
  have he : (d-y)⁻¹-(d-x)⁻¹=(y-x)/((d-y)*(d-x)) := by field_simp;ring
  have hpos : 0<(y-x)/((d-y)*(d-x)) := div_pos (sub_pos.mpr hxy) hprod
  rw [← he] at hpos
  exact sub_pos.mp hpos

omit [DecidableEq I] in

theorem uniformCurve_increasing (d : I → ℝ) (x y : ℝ) (hxy : x<y)
    (hp : ∀ i,0<(d i-y)*(d i-x)) : uniformCurve d x<uniformCurve d y := by
  unfold uniformCurve
  apply mul_lt_mul_of_pos_left _ (one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  apply Finset.sum_lt_sum
  · intro i _
    exact (reciprocal_increasing (d i) x y hxy (hp i)).le
  · let i : I:=Classical.choice inferInstance
    exact ⟨i,Finset.mem_univ i,reciprocal_increasing (d i) x y hxy (hp i)⟩

omit [DecidableEq I] in

theorem uniformCurve_strictMono_negative (d : I → ℝ) (hd : ∀ i,0≤d i) :
    StrictMonoOn (uniformCurve d) (Set.Iio (0:ℝ)) := by
  intro x hx y hy hxy
  change x<0 at hx
  change y<0 at hy
  apply uniformCurve_increasing d x y hxy
  intro i
  exact mul_pos (by linarith [hd i]) (by linarith [hd i])

theorem uniformCurve_strictMono_positive (d : I → ℝ) (zero : I) (hz : d zero=0)
    (emin : ℝ) (_hemin : 0<emin) (hlow : ∀ i,i≠zero → emin≤d i) :
    StrictMonoOn (uniformCurve d) (Set.Ioo (0:ℝ) emin) := by
  intro x hx y hy hxy
  apply uniformCurve_increasing d x y hxy
  intro i
  by_cases hi : i=zero
  · subst i
    rw [hz]
    exact mul_pos_of_neg_of_neg (by linarith [hy.1]) (by linarith [hx.1])
  · exact mul_pos (by linarith [hlow i hi,hy.2]) (by linarith [hlow i hi,hx.2])
end Qatlib.Foundations.MatrixAlgebra.RankOneSecular
