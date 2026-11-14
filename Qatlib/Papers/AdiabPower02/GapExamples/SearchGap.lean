/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.Lattice
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

/-!
# Search gap and inverse-gap integral

Defines `searchGap` from the scalar two-level search expression and proves that its minimum on
the interpolation interval is `1 / sqrt N`, attained at one half. An explicit arctangent
antiderivative evaluates the integral of the inverse squared gap and yields a square-root upper
bound. See [VanDamMoscaVazirani2001].

## Main statements

* `searchGap_half`: Evaluates the gap at the midpoint.
* `searchGap_ge_min`: Bounds the gap below by its midpoint value.
* `delayIntegral_eq`: Evaluates the inverse squared gap integral.
* `delayIntegral_le`: Bounds the integral by `π * sqrt N` for `N ≥ 2`.

## References

* [van Dam et al., 2001][VanDamMoscaVazirani2001]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Real

namespace Qatlib.Papers.AdiabPower02.GapExamples

/-- The search gap `sqrt ((N + 4 * (N - 1) * (s ^ 2 - s)) / N)`. -/
def searchGap (N s : ℝ) : ℝ :=
  Real.sqrt ((N + 4 * (N - 1) * (s ^ 2 - s)) / N)

/-- The numerator of the squared search gap equals `1 + 4 * (N - 1) * (s - 1 / 2) ^ 2`. -/
lemma searchNum_eq (N s : ℝ) :
    N + 4 * (N - 1) * (s ^ 2 - s) = 1 + 4 * (N - 1) * (s - 1 / 2) ^ 2 := by
  ring

/-- For `N ≥ 1`, the numerator of the squared search gap is strictly positive for every real
parameter. -/
lemma searchNum_pos {N : ℝ} (hN : 1 ≤ N) (s : ℝ) :
    0 < N + 4 * (N - 1) * (s ^ 2 - s) := by
  rw [searchNum_eq]
  have h : 0 ≤ 4 * (N - 1) * (s - 1 / 2) ^ 2 := by positivity
  linarith

/-- For `N ≥ 1`, squaring the search gap recovers its defining rational quadratic expression. -/
lemma searchGap_sq {N : ℝ} (hN : 1 ≤ N) (s : ℝ) :
    searchGap N s ^ 2 = (N + 4 * (N - 1) * (s ^ 2 - s)) / N := by
  rw [searchGap, Real.sq_sqrt
    (div_nonneg (le_of_lt (searchNum_pos hN s)) (by linarith))]

/-- For `N ≥ 1`, the search gap at `s = 1 / 2` equals `1 / sqrt N`. -/
theorem searchGap_half {N : ℝ} (hN : 1 ≤ N) :
    searchGap N (1 / 2) = 1 / Real.sqrt N := by
  rw [searchGap]
  have hnum : (N + 4 * (N - 1) * ((1 / 2 : ℝ) ^ 2 - 1 / 2)) / N = 1 / N := by
    field_simp; ring
  rw [hnum, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  simp

/-- For `N ≥ 1` and `0 ≤ s ≤ 1`, the search gap is at least `1 / sqrt N`. -/
theorem searchGap_ge_min {N s : ℝ} (hN : 1 ≤ N) (_hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    1 / Real.sqrt N ≤ searchGap N s := by
  have hNpos : 0 < N := by linarith
  have hleft : (1 : ℝ) / Real.sqrt N = Real.sqrt (1 / N) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]; simp
  rw [hleft]
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (le_of_lt hNpos)
  have hnum := searchNum_pos hN s
  have hnum1 : 1 ≤ N + 4 * (N - 1) * (s ^ 2 - s) := by
    rw [searchNum_eq]
    have : 0 ≤ 4 * (N - 1) * (s - 1 / 2) ^ 2 := by positivity
    linarith
  exact hnum1

/-- The arctangent expression `N / (2 * sqrt (N - 1)) * arctan (2 * sqrt (N - 1) * (s - 1 /
2))`. -/
def searchAnti (N s : ℝ) : ℝ :=
  N / (2 * Real.sqrt (N - 1)) * Real.arctan (2 * Real.sqrt (N - 1) * (s - 1 / 2))

/-- For `N > 1`, the inverse squared search gap equals `N` divided by its quadratic numerator. -/
lemma one_div_searchGap_sq {N : ℝ} (hN : 1 < N) (s : ℝ) :
    1 / (searchGap N s) ^ 2 = N / (N + 4 * (N - 1) * (s ^ 2 - s)) := by
  rw [searchGap_sq (le_of_lt hN)]
  have hnum : 0 < N + 4 * (N - 1) * (s ^ 2 - s) := searchNum_pos (le_of_lt hN) s
  have hNpos : 0 < N := by linarith
  field_simp

/-- For `N > 1`, the derivative of `searchAnti N` is the inverse squared search gap. -/
lemma searchAnti_deriv {N : ℝ} (hN : 1 < N) (s : ℝ) :
    HasDerivAt (searchAnti N) (1 / (searchGap N s) ^ 2) s := by
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have ha2 : (Real.sqrt (N - 1)) ^ 2 = N - 1 := Real.sq_sqrt (le_of_lt hN1)
  have ha_pos : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr hN1
  have harg : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (N - 1) * (u - 1 / 2))
      (2 * Real.sqrt (N - 1)) s := by
    have h := (hasDerivAt_id s).sub_const (1 / 2 : ℝ)
    have h2 := h.const_mul (2 * Real.sqrt (N - 1))
    convert! h2 using 1
    ring
  have hcomp : HasDerivAt
      (fun u : ℝ => Real.arctan (2 * Real.sqrt (N - 1) * (u - 1 / 2)))
      (1 / (1 + (2 * Real.sqrt (N - 1) * (s - 1 / 2)) ^ 2)
        * (2 * Real.sqrt (N - 1))) s :=
    harg.arctan
  have hmul : HasDerivAt (searchAnti N)
      (N / (2 * Real.sqrt (N - 1))
        * (1 / (1 + (2 * Real.sqrt (N - 1) * (s - 1 / 2)) ^ 2)
          * (2 * Real.sqrt (N - 1)))) s := by
    unfold searchAnti
    exact hcomp.const_mul _
  convert! hmul using 1
  rw [one_div_searchGap_sq hN]
  have hden : 1 + (2 * Real.sqrt (N - 1) * (s - 1 / 2)) ^ 2
      = N + 4 * (N - 1) * (s ^ 2 - s) := by
    rw [show (2 * Real.sqrt (N - 1) * (s - 1 / 2)) ^ 2
        = 4 * (Real.sqrt (N - 1)) ^ 2 * (s - 1 / 2) ^ 2 by ring]
    rw [ha2]; ring
  rw [hden]
  have hnum : 0 < N + 4 * (N - 1) * (s ^ 2 - s) := searchNum_pos (le_of_lt hN) s
  have ha_ne : Real.sqrt (N - 1) ≠ 0 := ne_of_gt ha_pos
  field_simp [ha_ne, ne_of_gt hnum]

/-- For `N > 1`, the inverse squared search gap integrates over `[0,1]` to `N * arctan (sqrt (N
- 1)) / sqrt (N - 1)` [VanDamMoscaVazirani2001]. -/
theorem delayIntegral_eq {N : ℝ} (hN : 1 < N) :
    (∫ s in (0 : ℝ)..1, 1 / (searchGap N s) ^ 2)
      = N * Real.arctan (Real.sqrt (N - 1)) / Real.sqrt (N - 1) := by
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have ha_pos : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr hN1
  have ha_ne : Real.sqrt (N - 1) ≠ 0 := ne_of_gt ha_pos
  have hgap_cont : Continuous (fun s : ℝ => searchGap N s) := by
    unfold searchGap
    exact Real.continuous_sqrt.comp (by fun_prop)
  have hpos : ∀ s : ℝ, searchGap N s ≠ 0 := by
    intro s
    apply ne_of_gt
    unfold searchGap
    exact Real.sqrt_pos.mpr
      (div_pos (searchNum_pos (le_of_lt hN) s) (by linarith))
  have hcont : Continuous (fun s : ℝ => 1 / (searchGap N s) ^ 2) := by
    have := (hgap_cont.pow 2).inv₀ (fun s => pow_ne_zero 2 (hpos s))
    simpa [one_div] using! this
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => searchAnti_deriv hN s) (hcont.intervalIntegrable 0 1)
  rw [hFTC]
  have h1 : 2 * Real.sqrt (N - 1) * (1 - 1 / 2) = Real.sqrt (N - 1) := by ring
  have h0 : 2 * Real.sqrt (N - 1) * (0 - 1 / 2) = -Real.sqrt (N - 1) := by ring
  simp only [searchAnti, h1, h0, Real.arctan_neg]
  field_simp [ha_ne]
  ring

/-- For `N ≥ 2`, the integral of the inverse squared search gap over `[0,1]` is at most `π *
sqrt N`. -/
theorem delayIntegral_le {N : ℝ} (hN : 2 ≤ N) :
    (∫ s in (0 : ℝ)..1, 1 / (searchGap N s) ^ 2) ≤ Real.pi * Real.sqrt N := by
  rw [delayIntegral_eq (by linarith)]
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have ha_pos : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr hN1
  have ha2 : (Real.sqrt (N - 1)) ^ 2 = N - 1 := Real.sq_sqrt (le_of_lt hN1)

  have step1 : N * Real.arctan (Real.sqrt (N - 1)) / Real.sqrt (N - 1)
      ≤ N * (Real.pi / 2) / Real.sqrt (N - 1) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
    exact mul_le_mul_of_nonneg_left
      (le_of_lt (Real.arctan_lt_pi_div_two (Real.sqrt (N - 1)))) (by linarith)

  have hle : N / (2 * Real.sqrt (N - 1)) ≤ Real.sqrt N := by
    have hsq : (N / (2 * Real.sqrt (N - 1))) ^ 2 ≤ (Real.sqrt N) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ N)]
      rw [show (2 * Real.sqrt (N - 1)) ^ 2 = 4 * (Real.sqrt (N - 1)) ^ 2 by ring]
      rw [ha2]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (N - 1))]
      nlinarith
    have h1 : 0 ≤ N / (2 * Real.sqrt (N - 1)) := by positivity
    have h2 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
    have := sq_le_sq.mp hsq
    rwa [abs_of_nonneg h1, abs_of_nonneg h2] at this
  calc N * Real.arctan (Real.sqrt (N - 1)) / Real.sqrt (N - 1)
      ≤ N * (Real.pi / 2) / Real.sqrt (N - 1) := step1
    _ = Real.pi * (N / (2 * Real.sqrt (N - 1))) := by ring
    _ ≤ Real.pi * Real.sqrt N :=
        mul_le_mul_of_nonneg_left hle (le_of_lt Real.pi_pos)

end Qatlib.Papers.AdiabPower02.GapExamples
