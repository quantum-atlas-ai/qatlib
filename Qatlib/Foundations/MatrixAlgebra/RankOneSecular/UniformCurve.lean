/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Monotonicity of the uniform secular curve

`uniformCurve` is the average of the reciprocal functions `(d i - z)⁻¹` over a finite index set.
The module proves continuity away from poles and strict monotonicity between points for which
each pair of denominators has positive product.

The negative half-line and the interval between a distinguished zero pole and a positive lower
bound on the remaining poles give useful special cases of secular-curve monotonicity
[Bhatia1997].

## Main statements

* `uniformCurve_continuousOn`: continuity on sets avoiding every pole.
* `uniformCurve_strictMono_negative`: strict monotonicity below zero for nonnegative poles.
* `uniformCurve_strictMono_positive`: strict monotonicity between a zero pole and a positive
  lower bound for the others.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular
open scoped Classical BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The average of `(d i - z)⁻¹` over the finite index type. -/
def uniformCurve (d : I → ℝ) (z : ℝ) : ℝ :=
  (1/(Fintype.card I:ℝ))*∑ i,(d i-z)⁻¹

omit [DecidableEq I] [Nonempty I] in

/-- The uniform secular curve is continuous on any set avoiding all diagonal poles. -/
theorem uniformCurve_continuousOn (d : I → ℝ) (S : Set ℝ)
    (hpole : ∀ i z,z∈S → d i≠z) : ContinuousOn (uniformCurve d) S := by
  unfold uniformCurve
  apply ContinuousOn.mul continuousOn_const
  apply continuousOn_finsetSum
  intro i _
  exact (continuousOn_const.sub continuousOn_id).inv₀ (fun z hz => sub_ne_zero.mpr (hpole i z hz))

/-- For `x < y`, the reciprocal `(d - z)⁻¹` increases from `x` to `y` whenever the two
denominators have positive product. -/
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

/-- On a nonempty finite index set, the uniform curve strictly increases between `x < y` if
every corresponding denominator pair has positive product. -/
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

/-- If all diagonal poles are nonnegative, the uniform secular curve is strictly increasing on
the negative half-line. -/
theorem uniformCurve_strictMono_negative (d : I → ℝ) (hd : ∀ i,0≤d i) :
    StrictMonoOn (uniformCurve d) (Set.Iio (0:ℝ)) := by
  intro x hx y hy hxy
  change x<0 at hx
  change y<0 at hy
  apply uniformCurve_increasing d x y hxy
  intro i
  exact mul_pos (by linarith [hd i]) (by linarith [hd i])

/-- With one pole at zero and every other pole at least a positive `emin`, the uniform curve is
strictly increasing on `(0, emin)`. -/
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
