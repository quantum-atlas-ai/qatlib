/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs

/-!
# One-bit oracle evolution and its time lower bound

This module defines the two-component rotation `oneBitEvol`, proves its initial value and
differential equations, and evaluates it at time 1/2. The theorem `oneBit_zeroError_minimumTime`
combines this endpoint with a lower bound for angular trajectories starting at zero and having
speed at most π/2. See [Mochon2007] for the Hamiltonian oracle formulation.

## Main statements

* `oneBitEvol_solves_ODE`: The components of `oneBitEvol` satisfy the coupled rotation equations
  with angular speed π / 2.
* `oneBit_zeroError_minimumTime`: The evolution `oneBitEvol` reaches (√2 / 2, √2 / 2) at time 1
  / 2, and every angular trajectory satisfying the stated derivative and speed bounds and the
  target cosine requires at least that time.

## References

* [Mochon, 2007][Mochon2007]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamOracle06.MainResults

/-- The two-component evolution (cos(πt / 2), sin(πt / 2)). -/
def oneBitEvol (t : ℝ) : ℝ × ℝ :=
  (Real.cos (Real.pi / 2 * t), Real.sin (Real.pi / 2 * t))

/-- The one-bit evolution starts at the vector (1, 0). -/
theorem oneBitEvol_initial : oneBitEvol 0 = (1, 0) := by
  simp [oneBitEvol]

/-- The derivative of cos(πt / 2) is −(π / 2) sin(πt / 2). -/
theorem oneBitEvol_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.cos (Real.pi / 2 * s))
      (-(Real.pi / 2) * Real.sin (Real.pi / 2 * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 * s) (Real.pi / 2) t :=
    hasDerivAt_const_mul (Real.pi / 2)
  have h := (Real.hasDerivAt_cos (Real.pi / 2 * t)).comp t hinner
  have hfun : (Real.cos ∘ fun s : ℝ => Real.pi / 2 * s)
      = fun s => Real.cos (Real.pi / 2 * s) := rfl
  rw [hfun] at h
  convert! h using 1
  ring

/-- The derivative of sin(πt / 2) is (π / 2) cos(πt / 2). -/
theorem oneBitEvol_snd_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => Real.sin (Real.pi / 2 * s))
      ((Real.pi / 2) * Real.cos (Real.pi / 2 * t)) t := by
  have hinner : HasDerivAt (fun s : ℝ => Real.pi / 2 * s) (Real.pi / 2) t :=
    hasDerivAt_const_mul (Real.pi / 2)
  have h := (Real.hasDerivAt_sin (Real.pi / 2 * t)).comp t hinner
  have hfun : (Real.sin ∘ fun s : ℝ => Real.pi / 2 * s)
      = fun s => Real.sin (Real.pi / 2 * s) := rfl
  rw [hfun] at h
  convert! h using 1
  ring

/-- The components of `oneBitEvol` satisfy the coupled rotation equations with angular speed π /
2. See [Mochon2007]. -/
theorem oneBitEvol_solves_ODE (t : ℝ) :
    HasDerivAt (fun s => (oneBitEvol s).1) (-(Real.pi / 2) * (oneBitEvol t).2) t ∧
      HasDerivAt (fun s => (oneBitEvol s).2) ((Real.pi / 2) * (oneBitEvol t).1) t := by
  constructor
  · simpa [oneBitEvol] using oneBitEvol_fst_hasDerivAt t
  · simpa [oneBitEvol] using oneBitEvol_snd_hasDerivAt t

/-- At time 1 / 2, the one-bit evolution equals (√2 / 2, √2 / 2). -/
theorem oneBitEvol_final : oneBitEvol (1 / 2) = (Real.sqrt 2 / 2, Real.sqrt 2 / 2) := by
  have harg : Real.pi / 2 * (1 / 2) = Real.pi / 4 := by ring
  unfold oneBitEvol
  rw [harg, Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- A differentiable angular trajectory starting at zero, with speed bounded by π / 2 on [0, T),
and satisfying cos(φ(T)) = √2 / 2 requires T ≥ 1 / 2. -/
theorem oneBit_lowerBound (φ u : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (hφ0 : φ 0 = 0)
    (hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt φ (u x) (Set.Icc 0 T) x)
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) T, |u x| ≤ Real.pi / 2)
    (hcos : Real.cos (φ T) = Real.sqrt 2 / 2) : 1 / 2 ≤ T := by
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := T) (f := φ) (f' := u) hderiv
    (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx) T (Set.right_mem_Icc.2 hT)
  rw [hφ0, sub_zero, Real.norm_eq_abs, sub_zero] at hmvt
  have habs : Real.pi / 4 ≤ |φ T| := by
    by_contra hlt
    rw [not_le] at hlt
    have hpi : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hcoslt : Real.cos (Real.pi / 4) < Real.cos |φ T| :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi hlt
    rw [Real.cos_abs, Real.cos_pi_div_four, hcos] at hcoslt
    exact lt_irrefl _ hcoslt
  nlinarith [Real.pi_pos]

/-- The evolution `oneBitEvol` reaches (√2 / 2, √2 / 2) at time 1 / 2, and every angular
trajectory satisfying the stated derivative and speed bounds and the target cosine requires
at least that time. See [Mochon2007]. -/
theorem oneBit_zeroError_minimumTime :
    (oneBitEvol (1 / 2) = (Real.sqrt 2 / 2, Real.sqrt 2 / 2)) ∧
      (∀ (φ u : ℝ → ℝ) (T : ℝ), 0 ≤ T → φ 0 = 0 →
        (∀ x ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt φ (u x) (Set.Icc 0 T) x) →
        (∀ x ∈ Set.Ico (0 : ℝ) T, |u x| ≤ Real.pi / 2) →
        Real.cos (φ T) = Real.sqrt 2 / 2 → 1 / 2 ≤ T) :=
  ⟨oneBitEvol_final, fun φ u T hT hφ0 hd hb hc =>
    oneBit_lowerBound φ u T hT hφ0 hd hb hc⟩

end Qatlib.Papers.HamOracle06.MainResults
