/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Defs

/-!
# Trigonometric constants for search lower bounds

This module proves polynomial bounds for sine and cosine and certifies the numerical constants
used in the advice-search lower bound. The theorem `prop_2_3_sharp` specializes a supplied
family of Zalka-type inequalities to obtain coefficient 0.2059 and offset 0.316.

The source paper is [Montanaro2011].

## Main statements

* `sin_ge_cubic`: For x ≥ 0, sin x ≥ x − x³/6.
* `coef_ge`: The coefficient 0.6537·cos²(0.6537)/2 is at least 0.2059.
* `prop_2_3_sharp`: For n ≥ 2, the supplied family of success-dependent lower bounds implies T ≥
  0.2059/arcsin(1/√n) − 0.316.

## References

* [Montanaro, 2011][Montanaro2011]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QSearchAdvice09.MainResults

/-- For x ≥ 0, cos x ≥ 1 − x²/2. -/
theorem cos_ge_one_sub_sq_div_two (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 ≤ Real.cos x := by
  have hmono : MonotoneOn (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun y => y - Real.sin y)
        (by fun_prop) ?_ ?_
    · intro y _
      have h : HasDerivAt (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2)) (y - Real.sin y) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (- Real.sin y) y := Real.hasDerivAt_cos y
        have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2 / 2) (-y) y := by
          have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
          have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
            simpa using hasDerivAt_pow 2 y
          have hm : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * y) / 2) y := hp.div_const 2
          have h := hc.sub hm
          have heq : (0 - (2 * y) / 2 : ℝ) = -y := by ring
          rw [heq] at h
          exact h
        have h := h1.sub h2
        have heq : (- Real.sin y - -y : ℝ) = y - Real.sin y := by ring
        rw [heq] at h
        exact h
      exact h.hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact sub_nonneg.2 (Real.sin_le hy.le)
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

/-- For x ≥ 0, sin x ≥ x − x³/6. -/
theorem sin_ge_cubic (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x := by
  have hmono : MonotoneOn (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6)) (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (f' := fun y => Real.cos y - (1 - y ^ 2 / 2)) (by fun_prop) ?_ ?_
    · intro y _
      have h : HasDerivAt (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6))
          (Real.cos y - (1 - y ^ 2 / 2)) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.sin y) (Real.cos y) y := Real.hasDerivAt_sin y
        have h2 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6) (1 - y ^ 2 / 2) y := by
          have hy : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
          have hp : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            simpa using hasDerivAt_pow 3 y
          have hm : HasDerivAt (fun y : ℝ => y ^ 3 / 6) ((3 * y ^ 2) / 6) y := hp.div_const 6
          have h := hy.sub hm
          have heq : (1 - (3 * y ^ 2) / 6 : ℝ) = 1 - y ^ 2 / 2 := by ring
          rw [heq] at h
          exact h
        exact h1.sub h2
      exact h.hasDerivWithinAt
    · intro y _
      have hy : 0 < y := by rwa [interior_Ici] at *
      linarith [cos_ge_one_sub_sq_div_two y hy.le]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

/-- For x ≥ 0, cos x ≤ 1 − x²/2 + x⁴/24. -/
theorem cos_le_quartic (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hanti : AntitoneOn (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24))
      (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
        (f' := fun y => -(Real.sin y - (y - y ^ 3 / 6))) (by fun_prop) ?_ ?_
    · intro y _
      have h : HasDerivAt (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24))
          (-(Real.sin y - (y - y ^ 3 / 6))) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (- Real.sin y) y := Real.hasDerivAt_cos y
        have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2 / 2 + y ^ 4 / 24)
            (-y + y ^ 3 / 6) y := by
          have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
          have hp2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
            simpa using hasDerivAt_pow 2 y
          have hm2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * y) / 2) y := hp2.div_const 2
          have hp4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * y ^ 3) y := by
            simpa using hasDerivAt_pow 4 y
          have hm4 : HasDerivAt (fun y : ℝ => y ^ 4 / 24) ((4 * y ^ 3) / 24) y :=
            hp4.div_const 24
          have h := (hc.sub hm2).add hm4
          have heq : (0 - (2 * y) / 2 + (4 * y ^ 3) / 24 : ℝ) = -y + y ^ 3 / 6 := by ring
          rw [heq] at h
          exact h
        have h := h1.sub h2
        have heq : (- Real.sin y - (-y + y ^ 3 / 6) : ℝ) = -(Real.sin y - (y - y ^ 3 / 6)) := by
          ring
        rw [heq] at h
        exact h
      exact h.hasDerivWithinAt
    · intro y _
      have hy : 0 < y := by rwa [interior_Ici] at *
      have := sin_ge_cubic y hy.le
      linarith
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

/-- For x ≥ 0, sin x ≤ x − x³/6 + x⁵/120. -/
theorem sin_le_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hanti : AntitoneOn (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6 + y ^ 5 / 120))
      (Set.Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
        (f' := fun y => Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)) (by fun_prop) ?_ ?_
    · intro y _
      have h : HasDerivAt (fun y : ℝ => Real.sin y - (y - y ^ 3 / 6 + y ^ 5 / 120))
          (Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24)) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.sin y) (Real.cos y) y := Real.hasDerivAt_sin y
        have h2 : HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 120)
            (1 - y ^ 2 / 2 + y ^ 4 / 24) y := by
          have hy : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
          have hp3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * y ^ 2) y := by
            simpa using hasDerivAt_pow 3 y
          have hm3 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) ((3 * y ^ 2) / 6) y := hp3.div_const 6
          have hp5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * y ^ 4) y := by
            simpa using hasDerivAt_pow 5 y
          have hm5 : HasDerivAt (fun y : ℝ => y ^ 5 / 120) ((5 * y ^ 4) / 120) y :=
            hp5.div_const 120
          have h := (hy.sub hm3).add hm5
          have heq : (1 - (3 * y ^ 2) / 6 + (5 * y ^ 4) / 120 : ℝ) = 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
            ring
          rw [heq] at h
          exact h
        exact h1.sub h2
      exact h.hasDerivWithinAt
    · intro y _
      have hy : 0 < y := by rwa [interior_Ici] at *
      linarith [cos_le_quartic y hy.le]
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

/-- For x ≥ 0, cos x ≥ 1 − x²/2 + x⁴/24 − x⁶/720. -/
theorem cos_ge_sextic (x : ℝ) (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hmono : MonotoneOn
      (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720))
      (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (f' := fun y => -(Real.sin y - (y - y ^ 3 / 6 + y ^ 5 / 120))) (by fun_prop) ?_ ?_
    · intro y _
      have h : HasDerivAt
          (fun y : ℝ => Real.cos y - (1 - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720))
          (-(Real.sin y - (y - y ^ 3 / 6 + y ^ 5 / 120))) y := by
        have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (- Real.sin y) y := Real.hasDerivAt_cos y
        have h2 : HasDerivAt (fun y : ℝ => (1 : ℝ) - y ^ 2 / 2 + y ^ 4 / 24 - y ^ 6 / 720)
            (-y + y ^ 3 / 6 - y ^ 5 / 120) y := by
          have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
          have hp2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
            simpa using hasDerivAt_pow 2 y
          have hm2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * y) / 2) y := hp2.div_const 2
          have hp4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * y ^ 3) y := by
            simpa using hasDerivAt_pow 4 y
          have hm4 : HasDerivAt (fun y : ℝ => y ^ 4 / 24) ((4 * y ^ 3) / 24) y :=
            hp4.div_const 24
          have hp6 : HasDerivAt (fun y : ℝ => y ^ 6) (6 * y ^ 5) y := by
            simpa using hasDerivAt_pow 6 y
          have hm6 : HasDerivAt (fun y : ℝ => y ^ 6 / 720) ((6 * y ^ 5) / 720) y :=
            hp6.div_const 720
          have h := ((hc.sub hm2).add hm4).sub hm6
          have heq : (0 - (2 * y) / 2 + (4 * y ^ 3) / 24 - (6 * y ^ 5) / 720 : ℝ)
              = -y + y ^ 3 / 6 - y ^ 5 / 120 := by ring
          rw [heq] at h
          exact h
        have h := h1.sub h2
        have heq : (- Real.sin y - (-y + y ^ 3 / 6 - y ^ 5 / 120) : ℝ)
            = -(Real.sin y - (y - y ^ 3 / 6 + y ^ 5 / 120)) := by ring
        rw [heq] at h
        exact h
      exact h.hasDerivWithinAt
    · intro y _
      have hy : 0 < y := by rwa [interior_Ici] at *
      have := sin_le_quintic y hy.le
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simpa using this

/-- The square root of 37/100 is at least 0.6082. -/
theorem sqrt_37_100_ge : (0.6082 : ℝ) ≤ Real.sqrt ((37 : ℝ) / 100) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- The value sin(0.6537) is at most √(37/100). -/
theorem sin_frac_le_sqrt : Real.sin (0.6537 : ℝ) ≤ Real.sqrt ((37 : ℝ) / 100) := by
  have h := sin_le_quintic (0.6537 : ℝ) (by norm_num)
  have hnum : (0.6537 : ℝ) - (0.6537 : ℝ) ^ 3 / 6 + (0.6537 : ℝ) ^ 5 / 120 ≤ 0.6082 := by
    norm_num
  linarith [sqrt_37_100_ge]

/-- The value arcsin(√(37/100)) is at least 0.6537. -/
theorem arcsin_sqrt_frac_ge : (0.6537 : ℝ) ≤ Real.arcsin (Real.sqrt ((37 : ℝ) / 100)) := by
  rw [Real.le_arcsin_iff_sin_le]
  · exact sin_frac_le_sqrt
  · constructor <;> nlinarith [Real.pi_gt_three]
  · constructor
    · have h := Real.sqrt_nonneg ((37 : ℝ) / 100)
      linarith
    · have h : Real.sqrt ((37 : ℝ) / 100) ≤ 1 := by
        rw [Real.sqrt_le_one]
        norm_num
      exact h

/-- The value cos(0.6537) is at least 0.7938. -/
theorem cos_frac_ge : (0.7938 : ℝ) ≤ Real.cos (0.6537 : ℝ) := by
  have h := cos_ge_sextic (0.6537 : ℝ) (by norm_num)
  have hnum : (0.7938 : ℝ) ≤
      1 - (0.6537 : ℝ) ^ 2 / 2 + (0.6537 : ℝ) ^ 4 / 24 - (0.6537 : ℝ) ^ 6 / 720 := by
    norm_num
  linarith

/-- The value cos(0.6537) is at most 0.794. -/
theorem cos_frac_le : Real.cos (0.6537 : ℝ) ≤ (0.794 : ℝ) := by
  have h := cos_le_quartic (0.6537 : ℝ) (by norm_num)
  have hnum : (1 : ℝ) - (0.6537 : ℝ) ^ 2 / 2 + (0.6537 : ℝ) ^ 4 / 24 ≤ 0.794 := by
    norm_num
  linarith

/-- The coefficient 0.6537·cos²(0.6537)/2 is at least 0.2059. -/
theorem coef_ge : (0.2059 : ℝ) ≤ (0.6537 : ℝ) * (Real.cos (0.6537 : ℝ)) ^ 2 / 2 := by
  have hcos := cos_frac_ge
  have hsq : (0.7938 : ℝ) ^ 2 ≤ (Real.cos (0.6537 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hcos 2
  nlinarith [hsq]

/-- The offset cos²(0.6537)/2 is at most 0.316. -/
theorem offset_le : (Real.cos (0.6537 : ℝ)) ^ 2 / 2 ≤ (0.316 : ℝ) := by
  have hle := cos_frac_le
  have h0 : (0 : ℝ) ≤ Real.cos (0.6537 : ℝ) := le_trans (by norm_num) cos_frac_ge
  have hsq : (Real.cos (0.6537 : ℝ)) ^ 2 ≤ (0.794 : ℝ) ^ 2 :=
    pow_le_pow_left₀ h0 hle 2
  nlinarith [hsq]

/-- For n ≥ 2, the supplied family of success-dependent lower bounds implies T ≥
0.2059/arcsin(1/√n) − 0.316 [Montanaro2011]. -/
theorem prop_2_3_sharp (n : ℕ) (hn : 2 ≤ n) (T : ℝ)
    (hZalka : ∀ p : ℝ, 0 < p → p < 1 →
      (1 - p) * (Real.arcsin (Real.sqrt p) /
          (2 * Real.arcsin (1 / Real.sqrt (n : ℝ))) - 1 / 2) ≤ T) :
    0.2059 / Real.arcsin (1 / Real.sqrt (n : ℝ)) - 0.316 ≤ T := by
  set a : ℝ := 0.6537 with ha
  have ha0 : (0 : ℝ) < a := by rw [ha]; norm_num
  have haπ : a < Real.pi := by rw [ha]; nlinarith [Real.pi_gt_three]
  have hsin0 : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 haπ
  have ha1 : a < 1 := by rw [ha]; norm_num
  have hsinlt : Real.sin a < 1 := by
    have h := Real.sin_le ha0.le
    linarith
  have hp0 : 0 < Real.sin a ^ 2 := pow_pos hsin0 2
  have hp1 : Real.sin a ^ 2 < 1 := pow_lt_one₀ hsin0.le hsinlt (by norm_num)
  have hA : (0 : ℝ) < Real.arcsin (1 / Real.sqrt (n : ℝ)) := by
    apply Real.arcsin_pos.2
    positivity
  have harg_sqrt : Real.sqrt (Real.sin a ^ 2) = Real.sin a := Real.sqrt_sq hsin0.le
  have harcsin : Real.arcsin (Real.sqrt (Real.sin a ^ 2)) = a := by
    rw [harg_sqrt]
    exact Real.arcsin_sin (by rw [ha]; nlinarith [Real.pi_gt_three])
      (by rw [ha]; nlinarith [Real.pi_gt_three])
  have hcos_sq : 1 - Real.sin a ^ 2 = Real.cos a ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  have hmain := hZalka (Real.sin a ^ 2) hp0 hp1
  rw [harcsin, hcos_sq] at hmain

  have hcoef : (0.2059 : ℝ) ≤ a * Real.cos a ^ 2 / 2 := by
    simpa [ha] using coef_ge
  have hoff : Real.cos a ^ 2 / 2 ≤ (0.316 : ℝ) := by
    simpa [ha] using offset_le
  have hrewrite : Real.cos a ^ 2 * (a / (2 * Real.arcsin (1 / Real.sqrt (n : ℝ))) - 1 / 2)
      = a * Real.cos a ^ 2 / (2 * Real.arcsin (1 / Real.sqrt (n : ℝ)))
          - Real.cos a ^ 2 / 2 := by
    field_simp
  rw [hrewrite] at hmain
  have hterm : 0.2059 / Real.arcsin (1 / Real.sqrt (n : ℝ))
      ≤ a * Real.cos a ^ 2 / (2 * Real.arcsin (1 / Real.sqrt (n : ℝ))) := by
    have h1 : 0.2059 / Real.arcsin (1 / Real.sqrt (n : ℝ))
        ≤ (a * Real.cos a ^ 2 / 2) / Real.arcsin (1 / Real.sqrt (n : ℝ)) :=
      div_le_div_of_nonneg_right hcoef hA.le
    have h2 : (a * Real.cos a ^ 2 / 2) / Real.arcsin (1 / Real.sqrt (n : ℝ))
        = a * Real.cos a ^ 2 / (2 * Real.arcsin (1 / Real.sqrt (n : ℝ))) := by
      rw [div_div]
    rwa [h2] at h1
  linarith

end Qatlib.Papers.QSearchAdvice09.MainResults
