/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.LinearAlgebra.Matrix.Defs
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
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.EigenEngine
import Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Quantitative

/-!
# Abstract search norm and overlap estimates

This module specializes the abstract search eigenvector construction to a zero-phase coordinate
and paired coordinates with phases `θ j` and `-θ j`. It defines the scaled sum `wGood` and
scaled difference `wStart`, computes their squared norms, and develops the overlap estimates
associated with Lemmas 4 and 5 of [AmbainisKempeRivosh2004].

The results retain explicit constants and phase separation hypotheses. The theorem
`corollary2_rotation` gives an exact sine identity for the overlap after `t` steps, while
`corollary2_lower` supplies the corresponding elementary bound near angle `π / 4`.

## Main statements

* `lemma5_overlap_sq` expresses `2 / normSq (wGood ...)` as a reciprocal spectral sum.
* `lemma5_overlap_lower` bounds this ratio below by one ninth of a truncated reciprocal
  cotangent sum.
* `normSq_wStart_eq` and `lemma4_overlap_sq` compute the squared norm and
  distinguished-coordinate overlap of `wStart`.
* `lemma4_overlap_lower` bounds the norm of `wStart` in terms of its distinguished-coordinate
  overlap and an explicit error term.
* `corollary2_rotation` and `corollary2_lower` give the exact sine overlap and a bound at the
  selected rotation time.

## References

* [Ambainis et al., 2004][AmbainisKempeRivosh2004]
-/

open Matrix
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Lemmas45

open Eigen Quantitative

variable {m : ℕ}

/-- The real cotangent function is odd. -/
lemma cot_neg' (x : ℝ) : Real.cot (-x) = -Real.cot x := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.cos_neg, Real.sin_neg]
  exact div_neg _

/-- When `sin x` and `sin y` are nonzero, the difference `cot x - cot y` equals `sin (y - x) /
(sin x * sin y)`. -/
lemma cot_sub_eq (x y : ℝ) (hx : Real.sin x ≠ 0) (hy : Real.sin y ≠ 0) :
    Real.cot x - Real.cot y = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  field_simp [hx, hy]
  rw [Real.sin_sub]
  ring

/-- Under the stated nonvanishing hypotheses, the cotangent difference at `(α - θ) / 2` and `(α
+ θ) / 2` equals `2 * sin θ / (cos θ - cos α)`. -/
lemma cot_pair_diff {α θ : ℝ}
    (h1 : Real.sin ((α - θ) / 2) ≠ 0) (h2 : Real.sin ((α + θ) / 2) ≠ 0)
    (_hcos : Real.cos θ ≠ Real.cos α) :
    Real.cot ((α - θ) / 2) - Real.cot ((α + θ) / 2)
      = 2 * Real.sin θ / (Real.cos θ - Real.cos α) := by
  have h := cot_sub_eq ((α - θ) / 2) ((α + θ) / 2) h1 h2
  rw [show ((α + θ) / 2) - ((α - θ) / 2) = θ by ring] at h
  rw [h]
  have hprod : Real.cos θ - Real.cos α
      = 2 * (Real.sin ((α + θ) / 2) * Real.sin ((α - θ) / 2)) := by
    have h' := Real.cos_sub_cos θ α
    have hneg : Real.sin ((θ - α) / 2) = -Real.sin ((α - θ) / 2) := by
      rw [show (θ - α) / 2 = -((α - θ) / 2) by ring, Real.sin_neg]
    rw [h', hneg]
    ring_nf
  rw [hprod]
  field_simp [h1, h2]

/-- Real cotangent is positive on the interval `(0, π / 2)`. -/
lemma cot_pos' {x : ℝ} (h0 : 0 < x) (hπ : x < Real.pi / 2) : 0 < Real.cot x := by
  rw [Real.cot_eq_cos_div_sin]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, hπ⟩)
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith))

/-- For `0 < x ≤ y < π`, one has `cot y ≤ cot x`. -/
lemma cot_le_cot {x y : ℝ} (hx0 : 0 < x) (hxy : x ≤ y) (hyπ : y < Real.pi) :
    Real.cot y ≤ Real.cot x := by
  rcases lt_or_eq_of_le hxy with hlt | heq
  · have hy0 : 0 < y := lt_trans hx0 hlt
    have hsinx : Real.sin x ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)).ne'
    have hsiny : Real.sin y ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ).ne'
    have h := cot_sub_eq x y hsinx hsiny
    have hpos : 0 < Real.sin (y - x) / (Real.sin x * Real.sin y) :=
      div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
        (mul_pos (Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith))
          (Real.sin_pos_of_pos_of_lt_pi hy0 hyπ))
    linarith [h]
  · rw [heq]

/-- For `0 < α ≤ 1`, the quantity `α^2 * cot (α / 2)^2` is at least one. -/
lemma one_le_sq_cot {α : ℝ} (h0 : 0 < α) (h1 : α ≤ 1) :
    1 ≤ α ^ 2 * Real.cot (α / 2) ^ 2 := by
  have hα2 : 0 < α / 2 := by linarith
  have hsin : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hα2 (by nlinarith [Real.pi_gt_three])
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos (α / 2) := by
    have hle := Real.one_sub_sq_div_two_le_cos (x := α / 2)
    nlinarith [hle, hα2, h1]
  have hsin2 : Real.sin (α / 2) ≤ α / 2 := by
    have h := Real.abs_sin_le_abs (x := α / 2)
    rwa [abs_of_pos hsin, abs_of_pos hα2] at h
  have hkey : Real.sin (α / 2) ≤ α * Real.cos (α / 2) := by
    have h1 : α * (1 / 2) ≤ α * Real.cos (α / 2) :=
      mul_le_mul_of_nonneg_left hcos2 h0.le
    linarith
  have hαcot : 1 ≤ α * (Real.cos (α / 2) / Real.sin (α / 2)) := by
    rw [← mul_div_assoc, le_div_iff₀ hsin]
    simpa using hkey
  have hsq : (1 : ℝ) ≤ (α * (Real.cos (α / 2) / Real.sin (α / 2))) ^ 2 := by
    nlinarith
  have hrew : (α * (Real.cos (α / 2) / Real.sin (α / 2))) ^ 2
      = α ^ 2 * Real.cot (α / 2) ^ 2 := by
    rw [Real.cot_eq_cos_div_sin, div_eq_mul_inv]
    ring
  rw [← hrew]
  exact hsq

/-- For `0 < θ < π`, rewrites `(sin θ)^2 / (1 - cos θ)^2` as `cot (θ / 2)^2`. -/
lemma sin_sq_div_one_sub_cos_sq {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    Real.sin θ ^ 2 / (1 - Real.cos θ) ^ 2 = Real.cot (θ / 2) ^ 2 := by
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (θ / 2)
      rwa [show 2 * (θ / 2) = θ by ring] at h
    have hsc := Real.sin_sq_add_cos_sq (θ / 2)
    linarith
  have hsin0 : Real.sin (θ / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_gt_three])).ne'
  rw [hs, hc, Real.cot_eq_cos_div_sin]
  field_simp
  ring

/-- For `0 < θ < π`, the square of `cot (θ / 2)` is at most the square of `cot (θ / 4)`. -/
lemma cot_sq_half_le_cot_sq_quarter {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    Real.cot (θ / 2) ^ 2 ≤ Real.cot (θ / 4) ^ 2 := by
  have hq0 : 0 < θ / 4 := by linarith
  have hqπ : θ / 2 < Real.pi := by linarith
  have hc2 : 0 ≤ Real.cot (θ / 2) :=
    (cot_pos' (by linarith) (by nlinarith [Real.pi_gt_three, hπ])).le
  have hle : Real.cot (θ / 2) ≤ Real.cot (θ / 4) :=
    cot_le_cot hq0 (by linarith) hqπ
  exact pow_le_pow_left₀ hc2 hle 2

/-- The real amplitude function taking value `a0` at `none` and value `a j` at either coordinate
of pair `j`. -/
def amp (a0 : ℝ) (a : Fin m → ℝ) : SpecIdx m → ℝ
  | none => a0
  | some (j, _) => a j

/-- Each coordinate of `goodVec a0 a` is the complex embedding of the corresponding real
amplitude `amp a0 a`. -/
lemma goodVec_eq_amp (a0 : ℝ) (a : Fin m → ℝ) (i : SpecIdx m) :
    goodVec a0 a i = ((amp a0 a i : ℝ) : ℂ) := by
  cases i with
  | none => rfl
  | some p => obtain ⟨j, b⟩ := p; rfl

/-- The squared norm of `I` times a real scalar embedded in the complex numbers is the square of
that scalar. -/
lemma norm_I_mul_real (r : ℝ) : ‖Complex.I * ((r : ℝ) : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The squared complex norm of `r + I * s`, for real `r` and `s`, is `r^2 + s^2`. -/
lemma normSq_real_add_I_mul (r s : ℝ) :
    ‖((r : ℂ) + Complex.I * ((s : ℂ)))‖ ^ 2 = r ^ 2 + s ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Scaling a vector by a real scalar multiplies `normSq` by the square of that scalar. -/
lemma normSq_smul_real (c : ℝ) (v : SpecIdx m → ℂ) :
    normSq (c • v) = c ^ 2 * normSq v := by
  unfold normSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- The real imaginary-coordinate function for the sum of the `omega` vectors at phases `α` and
`-α`. -/
def wSumIm (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) : SpecIdx m → ℝ :=
  fun i => amp a0 a i *
    (Real.cot ((α - phase θ i) / 2) + Real.cot ((-α - phase θ i) / 2))

/-- Each coordinate of the opposite-phase `omega` sum has real part `2 * amp a0 a i` and
imaginary part `wSumIm θ a0 a α i`. -/
lemma wSum_apply (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) (i : SpecIdx m) :
    (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α)) i
      = ((2 * amp a0 a i : ℝ) : ℂ) + Complex.I * ((wSumIm θ a0 a α i : ℝ) : ℂ) := by
  simp only [Pi.add_apply, omega_apply, goodVec_eq_amp, wSumIm]
  push_cast
  ring

/-- Splits the squared norm of the opposite-phase `omega` sum into sums of squares of its real
and imaginary coordinates. -/
lemma normSq_wSum (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    normSq (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α))
      = (∑ i, (2 * amp a0 a i) ^ 2) + ∑ i, (wSumIm θ a0 a α i) ^ 2 := by
  have h1 : (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α))
      = fun i => ((2 * amp a0 a i : ℝ) : ℂ)
          + Complex.I * ((wSumIm θ a0 a α i : ℝ) : ℂ) := funext (wSum_apply θ a0 a α)
  rw [h1]
  unfold normSq
  simp only [normSq_real_add_I_mul]
  rw [Finset.sum_add_distrib]

/-- The sum of the squared doubled amplitudes over the zero coordinate and paired coordinates is
`4 * a0^2 + 8 * ∑ j, (a j)^2`. -/
lemma sum_amp_sq (a0 : ℝ) (a : Fin m → ℝ) :
    ∑ i, (2 * amp a0 a i) ^ 2 = 4 * a0 ^ 2 + 8 * ∑ j, (a j) ^ 2 := by
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, amp]
  rw [show (∑ j : Fin m, ((2 * a j) ^ 2 + (2 * a j) ^ 2))
      = ∑ j, 8 * (a j) ^ 2 by
    apply Finset.sum_congr rfl
    intro j _
    ring]
  rw [← Finset.mul_sum]
  ring

/-- The imaginary coordinate of the opposite-phase `omega` sum vanishes at `none`. -/
lemma wSumIm_none (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    wSumIm θ a0 a α none = 0 := by
  simp only [wSumIm, amp, phase]
  rw [show (α - 0) / 2 = α / 2 by ring,
    show (-α - 0) / 2 = -(α / 2) by ring, cot_neg']
  ring

/-- Under the nonvanishing hypotheses, evaluates `wSumIm` at `(j, true)` as `a j * (2 * sin (θ
j) / (cos (θ j) - cos α))`. -/
lemma wSumIm_true (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) (j : Fin m) :
    wSumIm θ a0 a α (some (j, true))
      = a j * (2 * Real.sin (θ j) / (Real.cos (θ j) - Real.cos α)) := by
  simp only [wSumIm, amp, phase]
  rw [show (-α - θ j) / 2 = -((α + θ j) / 2) by ring, cot_neg']
  rw [show Real.cot ((α - θ j) / 2) + -Real.cot ((α + θ j) / 2)
      = Real.cot ((α - θ j) / 2) - Real.cot ((α + θ j) / 2) by ring,
    cot_pair_diff (hb1 j) (hb2 j) (hb3 j)]

/-- Under the nonvanishing hypotheses, evaluates `wSumIm` at `(j, false)` as the negative of `a
j * (2 * sin (θ j) / (cos (θ j) - cos α))`. -/
lemma wSumIm_false (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) (j : Fin m) :
    wSumIm θ a0 a α (some (j, false))
      = -(a j * (2 * Real.sin (θ j) / (Real.cos (θ j) - Real.cos α))) := by
  simp only [wSumIm, amp, phase]
  rw [show (α - -θ j) / 2 = (α + θ j) / 2 by ring,
    show (-α - -θ j) / 2 = -((α - θ j) / 2) by ring, cot_neg']
  rw [show Real.cot ((α + θ j) / 2) + -Real.cot ((α - θ j) / 2)
      = -(Real.cot ((α - θ j) / 2) - Real.cot ((α + θ j) / 2)) by ring,
    cot_pair_diff (hb1 j) (hb2 j) (hb3 j)]
  ring

/-- Under the nonvanishing hypotheses, the sum of squared `wSumIm` coordinates equals `8 * ∑ j,
(a j)^2 * sin (θ j)^2 / (cos (θ j) - cos α)^2`. -/
lemma sum_wSumIm_sq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    ∑ i, (wSumIm θ a0 a α i) ^ 2
      = 8 * ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  have hpair : ∀ j : Fin m,
      wSumIm θ a0 a α (some (j, true)) ^ 2
        + wSumIm θ a0 a α (some (j, false)) ^ 2
      = 8 * ((a j) ^ 2 * Real.sin (θ j) ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2) := by
    intro j
    rw [wSumIm_true θ a0 a α hb1 hb2 hb3 j, wSumIm_false θ a0 a α hb1 hb2 hb3 j]
    have hD : Real.cos (θ j) - Real.cos α ≠ 0 := sub_ne_zero.mpr (hb3 j)
    field_simp
    ring
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [wSumIm_none, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  calc ∑ j : Fin m, (wSumIm θ a0 a α (some (j, true)) ^ 2
        + wSumIm θ a0 a α (some (j, false)) ^ 2)
      = ∑ j : Fin m, 8 * ((a j) ^ 2 * Real.sin (θ j) ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2) :=
        Finset.sum_congr rfl fun j _ => hpair j
    _ = 8 * ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2 := by
        rw [Finset.mul_sum]

/-- Computes the squared norm of the opposite-phase `omega` sum as `4 * a0^2 + 8 * ∑ j, (a j)^2`
plus the explicit sine-weighted spectral sum, under the nonvanishing hypotheses. -/
lemma normSq_wSum_eq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    normSq (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α))
      = 4 * a0 ^ 2 + 8 * (∑ j, (a j) ^ 2)
        + 8 * ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2
            / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  rw [normSq_wSum, sum_amp_sq, sum_wSumIm_sq θ a0 a α hb1 hb2 hb3]

/-- The raw sum of the `omega` vectors at `α` and `-α`, scaled by `1 / sqrt 2`. -/
def wGood (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) : SpecIdx m → ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) •
    (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α))

/-- Under the nonvanishing hypotheses, `normSq (wGood ...)` equals `2 * a0^2 + 4 * ∑ j, (a j)^2
+ 4 * ∑ j, (a j)^2 * sin (θ j)^2 / (cos (θ j) - cos α)^2`. -/
lemma normSq_wGood_eq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    normSq (wGood θ a0 a α)
      = 2 * a0 ^ 2 + 4 * (∑ j, (a j) ^ 2)
        + 4 * ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2
            / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, show Real.sqrt 2 ^ 2 = (2 : ℝ) from Real.sq_sqrt (by norm_num)]
    norm_num
  unfold wGood
  rw [normSq_smul_real, hs, normSq_wSum_eq θ a0 a α hb1 hb2 hb3]
  ring

/-- If `goodVec` has self-inner-product one and is orthogonal to both cotangent vectors, its
inner product with the opposite-phase `omega` sum is two. -/
lemma inner_goodVec_wSum (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hnorm : inner (goodVec a0 a) (goodVec a0 a) = 1)
    (horthα : inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) α) = 0)
    (horthm : inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) (-α)) = 0) :
    inner (goodVec a0 a)
        (omega (phase θ) (goodVec a0 a) α + omega (phase θ) (goodVec a0 a) (-α))
      = 2 := by
  rw [Eigen.inner_add_right, inner_omega _ _ _ hnorm horthα,
    inner_omega _ _ _ hnorm horthm]
  norm_num

/-- Assuming normalized amplitudes and the nonvanishing hypotheses, expresses `2 / normSq (wGood
...)` as `1 / (1 + 2 * ∑ j, (a j)^2 * sin (θ j)^2 / (cos (θ j) - cos α)^2)`. This is the
exact norm-ratio identity used for Lemma 5 in [AmbainisKempeRivosh2004]. -/
theorem lemma5_overlap_sq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α)
    (hunit : a0 ^ 2 + 2 * (∑ j, (a j) ^ 2) = 1) :
    (2 : ℝ) / normSq (wGood θ a0 a α)
      = 1 / (1 + 2 * ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2) := by
  set Y : ℝ := ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
    with hY
  set S : ℝ := ∑ j, (a j) ^ 2 with hS
  have hunit' : a0 ^ 2 + 2 * S = 1 := by
    rw [hS]
    exact hunit
  have hnorm : 2 * a0 ^ 2 + 4 * S + 4 * Y = 2 * (1 + 2 * Y) := by
    have hS' : a0 ^ 2 = 1 - 2 * S := by linarith
    nlinarith
  rw [normSq_wGood_eq θ a0 a α hb1 hb2 hb3, ← hS, ← hY, hnorm]
  by_cases hz : (1 + 2 * Y) = 0
  · simp [hz]
  · field_simp [hz]

/-- For `0 < α < θ / 2` and `0 < θ < π`, bounds `(sin θ)^2 / (cos θ - cos α)^2` above by `4 *
cot (θ / 4)^2`. -/
lemma X_le_cot_sq {α θ : ℝ} (hαpos : 0 < α) (hαhalf : α < θ / 2)
    (hθpos : 0 < θ) (hθπ : θ < Real.pi) :
    Real.sin θ ^ 2 / (Real.cos θ - Real.cos α) ^ 2 ≤ 4 * Real.cot (θ / 4) ^ 2 := by
  have hcα : Real.cos (θ / 2) ≤ Real.cos α :=
    (Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ / 2) hαpos.le
      (by linarith) hαhalf).le
  have hcθ1 : Real.cos θ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ) (le_refl 0)
      hθπ.le hθpos
    simpa using h
  have hch := half_one_sub_cos_le_cos_half_sub_cos θ hθpos hθπ
  have hd : (1 - Real.cos θ) / 2 ≤ Real.cos α - Real.cos θ := by linarith
  have hkey : ((1 - Real.cos θ) / 2) ^ 2 ≤ (Real.cos θ - Real.cos α) ^ 2 := by
    have heq : (Real.cos θ - Real.cos α) ^ 2 = (Real.cos α - Real.cos θ) ^ 2 := by ring
    rw [heq]
    exact pow_le_pow_left₀ (by linarith) hd 2
  have hb : 0 < ((1 - Real.cos θ) / 2) ^ 2 := by
    have h1 : 0 < 1 - Real.cos θ := by linarith
    have h2 : 0 < (1 - Real.cos θ) / 2 := by linarith
    exact pow_pos h2 2
  have hstep := div_le_div_of_nonneg_left (sq_nonneg (Real.sin θ)) hb hkey
  have hsimp : Real.sin θ ^ 2 / (Real.cos θ - Real.cos α) ^ 2
      ≤ Real.sin θ ^ 2 / ((1 - Real.cos θ) / 2) ^ 2 := hstep
  have hne : (1 - Real.cos θ) ≠ 0 := by linarith
  have hrew : Real.sin θ ^ 2 / ((1 - Real.cos θ) / 2) ^ 2
      = 4 * (Real.sin θ ^ 2 / (1 - Real.cos θ) ^ 2) := by
    field_simp
    ring
  have hid := sin_sq_div_one_sub_cos_sq hθpos hθπ
  have hquarter := cot_sq_half_le_cot_sq_quarter hθpos hθπ
  calc Real.sin θ ^ 2 / (Real.cos θ - Real.cos α) ^ 2
      ≤ Real.sin θ ^ 2 / ((1 - Real.cos θ) / 2) ^ 2 := hsimp
    _ = 4 * (Real.sin θ ^ 2 / (1 - Real.cos θ) ^ 2) := hrew
    _ = 4 * Real.cot (θ / 2) ^ 2 := by rw [hid]
    _ ≤ 4 * Real.cot (θ / 4) ^ 2 := by linarith [hquarter]

/-- Under normalized amplitudes and the stated phase separation and nonvanishing hypotheses,
bounds `2 / normSq (wGood ...)` below by `(1 / 9) * min 1 (1 / ∑ j, (a j)^2 * cot (θ j /
4)^2)`. This gives an explicit lower estimate associated with Lemma 5 in
[AmbainisKempeRivosh2004]. -/
theorem lemma5_overlap_lower (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α)
    (hunit : a0 ^ 2 + 2 * (∑ j, (a j) ^ 2) = 1)
    (hαpos : 0 < α) (hαhalf : ∀ j, α < θ j / 2)
    (hθpos : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j < Real.pi) :
    (1 / 9) * min 1 (1 / ∑ j, (a j) ^ 2 * Real.cot (θ j / 4) ^ 2)
      ≤ 2 / normSq (wGood θ a0 a α) := by
  set Y : ℝ := ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
    with hY
  set L : ℝ := ∑ j, (a j) ^ 2 * Real.cot (θ j / 4) ^ 2 with hL
  have hXle : ∀ j : Fin m,
      (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
        ≤ (a j) ^ 2 * (4 * Real.cot (θ j / 4) ^ 2) := by
    intro j
    have := X_le_cot_sq (α := α) (θ := θ j) hαpos (hαhalf j) (hθpos j) (hθπ j)
    have hnn : (0 : ℝ) ≤ (a j) ^ 2 := sq_nonneg _
    calc (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
        = (a j) ^ 2 * (Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2) := by ring
      _ ≤ (a j) ^ 2 * (4 * Real.cot (θ j / 4) ^ 2) :=
          mul_le_mul_of_nonneg_left this hnn
  have hYle : Y ≤ 4 * L := by
    rw [hY, hL]
    calc ∑ j, (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
        ≤ ∑ j, (a j) ^ 2 * (4 * Real.cot (θ j / 4) ^ 2) :=
          Finset.sum_le_sum (fun j _ => hXle j)
      _ = 4 * ∑ j, (a j) ^ 2 * Real.cot (θ j / 4) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  have hY0 : 0 ≤ Y := by
    rw [hY]
    apply Finset.sum_nonneg
    intro j _
    have hD : Real.cos (θ j) - Real.cos α ≠ 0 := sub_ne_zero.mpr (hb3 j)
    have hden : 0 < (Real.cos (θ j) - Real.cos α) ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hD
    have hnum : 0 ≤ (a j) ^ 2 * Real.sin (θ j) ^ 2 := by positivity
    calc (a j) ^ 2 * Real.sin (θ j) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
        = ((a j) ^ 2 * Real.sin (θ j) ^ 2) / (Real.cos (θ j) - Real.cos α) ^ 2 := by ring
      _ ≥ 0 := div_nonneg hnum hden.le
  have hL0 : 0 ≤ L := by
    rw [hL]
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hnorm := normSq_wGood_eq θ a0 a α hb1 hb2 hb3
  set S : ℝ := ∑ j, (a j) ^ 2 with hS
  have hunit' : a0 ^ 2 + 2 * S = 1 := by
    rw [hS]
    exact hunit
  have hval : normSq (wGood θ a0 a α) = 2 * (1 + 2 * Y) := by
    rw [hnorm, ← hY]
    have hS' : a0 ^ 2 = 1 - 2 * S := by linarith
    nlinarith
  have hR : 2 / normSq (wGood θ a0 a α) = 1 / (1 + 2 * Y) := by
    rw [hval]
    by_cases hz : (1 + 2 * Y) = 0
    · simp [hz]
    · field_simp [hz]
  rw [hR]
  have hpos1 : 0 < 1 + 2 * Y := by nlinarith
  have h8 : 0 < 1 + 8 * L := by nlinarith
  have step1 : 1 / (1 + 8 * L) ≤ 1 / (1 + 2 * Y) := by
    apply one_div_le_one_div_of_le hpos1
    linarith
  have hden2 : 0 < 1 + 2 * Y := by linarith
  rcases eq_or_lt_of_le hL0 with hLz | hLpos
  · rw [← hLz]
    have hzero : (1 / 9 : ℝ) * min 1 (1 / (0 : ℝ)) = 0 := by simp
    rw [hzero]
    exact div_nonneg zero_le_one hden2.le
  · by_cases hL1 : L ≤ 1
    · have hmin : min 1 (1 / L) = 1 := by
        apply min_eq_left
        rw [le_div_iff₀ hLpos]
        linarith
      rw [hmin]
      have h9 : (1 / 9 : ℝ) ≤ 1 / (1 + 8 * L) := by
        apply one_div_le_one_div_of_le h8
        linarith
      linarith
    · have hL1' : 1 < L := not_le.mp hL1
      have hmin : min 1 (1 / L) = 1 / L := by
        apply min_eq_right
        rw [div_le_iff₀ hLpos]
        linarith
      rw [hmin]
      have h9 : (1 / 9) * (1 / L) ≤ 1 / (1 + 8 * L) := by
        rw [show (1 / 9 : ℝ) * (1 / L) = 1 / (9 * L) by ring]
        rw [div_le_div_iff₀ (by positivity) h8]
        nlinarith
      linarith

/-- The real imaginary-coordinate function for the difference of the `omega` vectors at phases
`α` and `-α`. -/
def wDiffIm (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) : SpecIdx m → ℝ :=
  fun i => amp a0 a i *
    (Real.cot ((α - phase θ i) / 2) - Real.cot ((-α - phase θ i) / 2))

/-- Each coordinate of the opposite-phase `omega` difference is `I` times the real value
`wDiffIm θ a0 a α i`. -/
lemma wDiff_apply (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) (i : SpecIdx m) :
    (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α)) i
      = Complex.I * ((wDiffIm θ a0 a α i : ℝ) : ℂ) := by
  simp only [Pi.sub_apply, omega_apply, goodVec_eq_amp, wDiffIm]
  push_cast
  ring

/-- The squared norm of the opposite-phase `omega` difference is the sum of the squared
`wDiffIm` coordinates. -/
lemma normSq_wDiff (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    normSq (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))
      = ∑ i, (wDiffIm θ a0 a α i) ^ 2 := by
  have h1 : (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))
      = fun i => Complex.I * ((wDiffIm θ a0 a α i : ℝ) : ℂ) :=
    funext (wDiff_apply θ a0 a α)
  rw [h1]
  unfold normSq
  simp only [norm_I_mul_real]

/-- The value of `wDiffIm` at `none` is `2 * a0 * cot (α / 2)`. -/
lemma wDiffIm_none (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    wDiffIm θ a0 a α none = a0 * (2 * Real.cot (α / 2)) := by
  simp only [wDiffIm, amp, phase]
  rw [show (α - 0) / 2 = α / 2 by ring,
    show (-α - 0) / 2 = -(α / 2) by ring, cot_neg']
  ring

/-- Under the nonvanishing hypotheses, evaluates `wDiffIm` at `(j, true)` as `a j * (2 * sin α /
(cos (θ j) - cos α))`. -/
lemma wDiffIm_true (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) (j : Fin m) :
    wDiffIm θ a0 a α (some (j, true))
      = a j * (2 * Real.sin α / (Real.cos (θ j) - Real.cos α)) := by
  simp only [wDiffIm, amp, phase]
  rw [show (-α - θ j) / 2 = -((α + θ j) / 2) by ring, cot_neg']
  rw [show Real.cot ((α - θ j) / 2) - -Real.cot ((α + θ j) / 2)
      = Real.cot ((α - θ j) / 2) + Real.cot ((α + θ j) / 2) by ring,
    cot_pair_eq (hb1 j) (hb2 j) (hb3 j)]

/-- Under the nonvanishing hypotheses, evaluates `wDiffIm` at `(j, false)` as `a j * (2 * sin α
/ (cos (θ j) - cos α))`. -/
lemma wDiffIm_false (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) (j : Fin m) :
    wDiffIm θ a0 a α (some (j, false))
      = a j * (2 * Real.sin α / (Real.cos (θ j) - Real.cos α)) := by
  simp only [wDiffIm, amp, phase]
  rw [show (α - -θ j) / 2 = (α + θ j) / 2 by ring,
    show (-α - -θ j) / 2 = -((α - θ j) / 2) by ring, cot_neg']
  rw [show Real.cot ((α + θ j) / 2) - -Real.cot ((α - θ j) / 2)
      = Real.cot ((α - θ j) / 2) + Real.cot ((α + θ j) / 2) by ring,
    cot_pair_eq (hb1 j) (hb2 j) (hb3 j)]

/-- Under the nonvanishing hypotheses, the sum of squared `wDiffIm` coordinates is `4 * a0^2 *
cot (α / 2)^2 + 8 * ∑ j, (a j)^2 * (sin α)^2 / (cos (θ j) - cos α)^2`. -/
lemma sum_wDiffIm_sq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    ∑ i, (wDiffIm θ a0 a α i) ^ 2
      = 4 * a0 ^ 2 * Real.cot (α / 2) ^ 2
        + 8 * ∑ j, (a j) ^ 2 * Real.sin α ^ 2
            / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  have hpair : ∀ j : Fin m,
      wDiffIm θ a0 a α (some (j, true)) ^ 2
        + wDiffIm θ a0 a α (some (j, false)) ^ 2
      = 8 * ((a j) ^ 2 * Real.sin α ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2) := by
    intro j
    rw [wDiffIm_true θ a0 a α hb1 hb2 hb3 j, wDiffIm_false θ a0 a α hb1 hb2 hb3 j]
    have hD : Real.cos (θ j) - Real.cos α ≠ 0 := sub_ne_zero.mpr (hb3 j)
    field_simp
    ring
  rw [Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [wDiffIm_none, show (a0 * (2 * Real.cot (α / 2))) ^ 2
      = 4 * a0 ^ 2 * Real.cot (α / 2) ^ 2 by ring]
  rw [show (∑ j : Fin m, (wDiffIm θ a0 a α (some (j, true)) ^ 2
        + wDiffIm θ a0 a α (some (j, false)) ^ 2))
      = ∑ j : Fin m, 8 * ((a j) ^ 2 * Real.sin α ^ 2
          / (Real.cos (θ j) - Real.cos α) ^ 2) from
    Finset.sum_congr rfl fun j _ => hpair j]
  rw [Finset.mul_sum]

/-- Under the nonvanishing hypotheses, computes the squared norm of the opposite-phase `omega`
difference as `4 * a0^2 * cot (α / 2)^2` plus the explicit sine-weighted spectral sum. -/
lemma normSq_wDiff_eq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    normSq (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))
      = 4 * a0 ^ 2 * Real.cot (α / 2) ^ 2
        + 8 * ∑ j, (a j) ^ 2 * Real.sin α ^ 2
            / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  rw [normSq_wDiff, sum_wDiffIm_sq θ a0 a α hb1 hb2 hb3]

/-- The raw difference of the `omega` vectors at `α` and `-α`, scaled by `1 / sqrt 2`. -/
def wStart (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) : SpecIdx m → ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) •
    (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))

/-- Multiplying `2 * x` by the reciprocal of `sqrt 2` gives `sqrt 2 * x`. -/
lemma sqrt2_inv_mul (x : ℝ) : (Real.sqrt 2)⁻¹ * (2 * x) = Real.sqrt 2 * x := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [show (Real.sqrt 2)⁻¹ * (2 * x) = ((Real.sqrt 2)⁻¹ * 2) * x by ring]
  rw [show (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 by
    field_simp
    linarith]

/-- Under the nonvanishing hypotheses, computes `normSq (wStart ...)` as `2 * a0^2 * cot (α /
2)^2 + 4 * ∑ j, (a j)^2 * (sin α)^2 / (cos (θ j) - cos α)^2`. This is the norm identity used
in the Lemma 4 analysis of [AmbainisKempeRivosh2004]. -/
lemma normSq_wStart_eq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α) :
    normSq (wStart θ a0 a α)
      = 2 * a0 ^ 2 * Real.cot (α / 2) ^ 2
        + 4 * ∑ j, (a j) ^ 2 * Real.sin α ^ 2
            / (Real.cos (θ j) - Real.cos α) ^ 2 := by
  have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, show Real.sqrt 2 ^ 2 = (2 : ℝ) from Real.sq_sqrt (by norm_num)]
    norm_num
  unfold wStart
  rw [normSq_smul_real, hs, normSq_wDiff_eq θ a0 a α hb1 hb2 hb3]
  ring

/-- The distinguished basis vector with value one at `none` and zero at all paired coordinates. -/
def phi0 : SpecIdx m → ℂ
  | none => 1
  | some _ => 0

/-- Taking the inner product with `phi0` extracts the coordinate at `none`. -/
lemma inner_phi0_eq (v : SpecIdx m → ℂ) : inner phi0 v = v none := by
  rw [Eigen.inner, Fintype.sum_option]
  simp [phi0]

/-- The inner product distributes over subtraction in its second argument. -/
lemma inner_sub_right (u v w : SpecIdx m → ℂ) :
    inner u (v - w) = inner u v - inner u w := by
  simp only [Eigen.inner, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Scaling the second argument by a real scalar multiplies the inner product by its complex
embedding. -/
lemma inner_smul_right_real (u w : SpecIdx m → ℂ) (c : ℝ) :
    inner u (c • w) = (c : ℂ) * inner u w := by
  simp only [Eigen.inner, Pi.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.real_smul]
  ring

/-- The inner product of `phi0` with the opposite-phase `omega` difference is `I * (2 * a0 * cot
(α / 2))`. -/
lemma inner_phi0_wDiff (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    inner phi0 (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))
      = Complex.I * ((2 * a0 * Real.cot (α / 2) : ℝ) : ℂ) := by
  rw [inner_phi0_eq, wDiff_apply, wDiffIm_none]
  push_cast
  ring

/-- The inner product of `phi0` with `wStart` is `I * (sqrt 2 * a0 * cot (α / 2))`. -/
lemma inner_phi0_wStart (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    inner phi0 (wStart θ a0 a α)
      = Complex.I * ((Real.sqrt 2 * a0 * Real.cot (α / 2) : ℝ) : ℂ) := by
  rw [inner_phi0_eq]
  have hdiff : (omega (phase θ) (goodVec a0 a) α
        - omega (phase θ) (goodVec a0 a) (-α)) none
      = Complex.I * ((2 * a0 * Real.cot (α / 2) : ℝ) : ℂ) := by
    rw [wDiff_apply, wDiffIm_none]
    push_cast
    ring
  unfold wStart
  rw [Pi.smul_apply, Complex.real_smul, hdiff]
  rw [show (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        * (Complex.I * (((2 * a0 * Real.cot (α / 2)) : ℝ) : ℂ))
      = Complex.I * ((((Real.sqrt 2)⁻¹ : ℝ) * (2 * a0 * Real.cot (α / 2)) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [show Real.sqrt 2 * a0 * Real.cot (α / 2)
      = Real.sqrt 2 * (a0 * Real.cot (α / 2)) by ring]
  rw [show 2 * a0 * Real.cot (α / 2) = 2 * (a0 * Real.cot (α / 2)) by ring,
    sqrt2_inv_mul]

/-- The squared complex norm of `inner phi0 (wStart ...)` is exactly `2 * a0^2 * cot (α / 2)^2`.
This computes the overlap numerator used for Lemma 4 in [AmbainisKempeRivosh2004]. -/
theorem lemma4_overlap_sq (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ) :
    Complex.normSq (inner phi0 (wStart θ a0 a α))
      = 2 * a0 ^ 2 * Real.cot (α / 2) ^ 2 := by
  rw [inner_phi0_wStart, Complex.normSq_mul, Complex.normSq_I, one_mul,
    show Complex.normSq ((Real.sqrt 2 * a0 * Real.cot (α / 2) : ℝ) : ℂ)
        = (Real.sqrt 2 * a0 * Real.cot (α / 2))
            * (Real.sqrt 2 * a0 * Real.cot (α / 2)) from
      Complex.normSq_ofReal _]
  rw [show (Real.sqrt 2 * a0 * Real.cot (α / 2))
        * (Real.sqrt 2 * a0 * Real.cot (α / 2))
      = (Real.sqrt 2) ^ 2 * (a0 * Real.cot (α / 2)) ^ 2 by ring]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- The difference of the complex exponentials at opposite imaginary angles is `2 * I * sin x`. -/
lemma exp_I_sub_exp_neg_I (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (-(Complex.I * (x : ℂ)))
      = 2 * Complex.I * ((Real.sin x : ℝ) : ℂ) := by
  have h2 : -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h1 : Complex.I * (x : ℂ) = (x : ℂ) * Complex.I := by ring
  rw [h2, h1, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The difference of the `t`th powers of the exponentials at phases `α` and `-α` is `2 * I *
sin (α * t)`. -/
lemma exp_sub_eq_two_I_sin (α : ℝ) (t : ℕ) :
    Complex.exp (Complex.I * (α : ℂ)) ^ t
      - Complex.exp (Complex.I * ((-α : ℝ) : ℂ)) ^ t
      = 2 * Complex.I * ((Real.sin (α * t) : ℝ) : ℂ) := by
  rw [exp_pow_eq_exp_mul, exp_pow_eq_exp_mul]
  have h1 : (t : ℂ) * (Complex.I * (α : ℂ)) = Complex.I * ((α * t : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : (t : ℂ) * (Complex.I * ((-α : ℝ) : ℂ))
      = -(Complex.I * ((α * t : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h1, h2, exp_I_sub_exp_neg_I]

/-- Under normalization, orthogonality at both phases, and the nonvanishing sine hypotheses, the
overlap of `goodVec` with `wStart` after `t` walk steps is `I * (sqrt 2 * sin (α * t))`.
This is the exact rotation identity used for Corollary 2 in [AmbainisKempeRivosh2004]. -/
theorem corollary2_rotation (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hnorm : inner (goodVec a0 a) (goodVec a0 a) = 1)
    (horthα : inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) α) = 0)
    (horthm : inner (goodVec a0 a) (wPrime (phase θ) (goodVec a0 a) (-α)) = 0)
    (hsinα : ∀ i, Real.sin ((α - phase θ i) / 2) ≠ 0)
    (hsinm : ∀ i, Real.sin ((-α - phase θ i) / 2) ≠ 0) (t : ℕ) :
    inner (goodVec a0 a) (((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ wStart θ a0 a α)
      = Complex.I * ((Real.sqrt 2 * Real.sin (α * t) : ℝ) : ℂ) := by
  have hαeig := lemma13_omega_eigenvector (phase θ) (goodVec a0 a) α hnorm horthα hsinα
  have hmEig := lemma13_omega_eigenvector (phase θ) (goodVec a0 a) (-α) hnorm horthm hsinm
  have h1 : inner (goodVec a0 a)
        (((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ omega (phase θ) (goodVec a0 a) α)
      = Complex.exp (Complex.I * (α : ℂ)) ^ t := by
    rw [matrix_pow_mulVec_eigen _ _ _ hαeig t, Eigen.inner_smul_right,
      inner_omega _ _ _ hnorm horthα, mul_one]
  have h2 : inner (goodVec a0 a)
        (((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ omega (phase θ) (goodVec a0 a) (-α))
      = Complex.exp (Complex.I * ((-α : ℝ) : ℂ)) ^ t := by
    rw [matrix_pow_mulVec_eigen _ _ _ hmEig t, Eigen.inner_smul_right,
      inner_omega _ _ _ hnorm horthm, mul_one]
  have hsub : ((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ
        (omega (phase θ) (goodVec a0 a) α - omega (phase θ) (goodVec a0 a) (-α))
      = ((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ omega (phase θ) (goodVec a0 a) α
        - ((walkM (phase θ) (goodVec a0 a)) ^ t) *ᵥ omega (phase θ) (goodVec a0 a) (-α) :=
    Matrix.mulVec_sub _ _ _
  unfold wStart
  rw [Matrix.mulVec_smul, hsub, inner_smul_right_real, inner_sub_right, h1, h2,
    exp_sub_eq_two_I_sin]
  rw [show (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
        * (2 * Complex.I * ((Real.sin (α * t) : ℝ) : ℂ))
      = Complex.I * ((((Real.sqrt 2)⁻¹ : ℝ) * (2 * Real.sin (α * t)) : ℝ) : ℂ) by
    push_cast
    ring]
  rw [sqrt2_inv_mul]

/-- If `t * α` lies between `π / 4` and `π / 4 + α`, then `sqrt 2 * sin (t * α)` is at least `1
- sqrt 2 * α`. This supplies the elementary rotation-time estimate for Corollary 2 in
[AmbainisKempeRivosh2004]. -/
theorem corollary2_lower {t : ℕ} {α : ℝ}
    (hT1 : Real.pi / 4 ≤ t * α) (hT2 : t * α ≤ Real.pi / 4 + α) :
    1 - Real.sqrt 2 * α ≤ Real.sqrt 2 * Real.sin (t * α) := by
  have hpi4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hd : |t * α - Real.pi / 4| ≤ α := by
    rw [abs_le]
    constructor <;> linarith
  have hbound : |Real.sin (t * α) - Real.sin (Real.pi / 4)| ≤ α :=
    le_trans (Real.abs_sin_sub_sin_le _ _) hd
  have hsin : Real.sqrt 2 / 2 - α ≤ Real.sin (t * α) := by
    have := (abs_le.mp hbound).1
    rw [hpi4] at this
    linarith
  have hsq : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
    have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp
    linarith
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hsin hpos.le
  nlinarith [hsq, hmul]

/-- With `δ = 8 * α^4 * (∑ j, (a j)^2 / (1 - cos (θ j))^2) / a0^2`, bounds `(1 - δ)^2 * normSq
(wStart ...)` above by `2 * (a0 * cot (α / 2))^2` under the stated hypotheses. This gives an
explicit squared-overlap estimate associated with Lemma 4 in [AmbainisKempeRivosh2004]. -/
theorem lemma4_overlap_lower (θ : Fin m → ℝ) (a0 : ℝ) (a : Fin m → ℝ) (α : ℝ)
    (hb1 : ∀ j, Real.sin ((α - θ j) / 2) ≠ 0)
    (hb2 : ∀ j, Real.sin ((α + θ j) / 2) ≠ 0)
    (hb3 : ∀ j, Real.cos (θ j) ≠ Real.cos α)
    (hαpos : 0 < α) (hα1 : α ≤ 1) (hαhalf : ∀ j, α < θ j / 2)
    (hθpos : ∀ j, 0 < θ j) (hθπ : ∀ j, θ j < Real.pi)
    (ha0 : a0 ≠ 0)
    (hδ1 : 8 * α ^ 4 * (∑ j, (a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2) / a0 ^ 2 ≤ 1) :
    (1 - 8 * α ^ 4 * (∑ j, (a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2) / a0 ^ 2) ^ 2
        * normSq (wStart θ a0 a α)
      ≤ 2 * (a0 * Real.cot (α / 2)) ^ 2 := by
  set c : ℝ := Real.cot (α / 2) with hc
  set T : ℝ :=
    ∑ j, (a j) ^ 2 * Real.sin α ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2 with hT
  set D : ℝ := ∑ j, (a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2 with hD
  set δ : ℝ := 8 * α ^ 4 * D / a0 ^ 2 with hδ
  have hδstmt : (1 - 8 * α ^ 4 * (∑ j, (a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2) / a0 ^ 2)
      = 1 - δ := by rw [hδ, hD]
  have hterm : ∀ j : Fin m,
      2 * ((a j) ^ 2 * Real.sin α ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2)
        ≤ 8 * α ^ 4 * c ^ 2 * ((a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2) := by
    intro j
    have hcα : Real.cos (θ j / 2) ≤ Real.cos α :=
      (Real.cos_lt_cos_of_nonneg_of_le_pi (x := α) (y := θ j / 2) hαpos.le
        (by linarith [hθπ j, Real.pi_pos]) (hαhalf j)).le
    have hch := half_one_sub_cos_le_cos_half_sub_cos (θ j) (hθpos j) (hθπ j)
    have hcos1 : Real.cos (θ j) < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := θ j) (le_refl 0)
        (hθπ j).le (hθpos j)
      simpa using h
    have hD1 : (1 - Real.cos (θ j)) / 2 ≤ Real.cos α - Real.cos (θ j) := by linarith
    have hkey : ((1 - Real.cos (θ j)) / 2) ^ 2
        ≤ (Real.cos (θ j) - Real.cos α) ^ 2 := by
      rw [show (Real.cos (θ j) - Real.cos α) ^ 2
          = (Real.cos α - Real.cos (θ j)) ^ 2 by ring]
      exact pow_le_pow_left₀ (by linarith) hD1 2
    have hb : 0 < ((1 - Real.cos (θ j)) / 2) ^ 2 := by
      have h1 : 0 < 1 - Real.cos (θ j) := by linarith
      have h2 : 0 < (1 - Real.cos (θ j)) / 2 := by linarith
      exact pow_pos h2 2
    have hden1 : 0 < (Real.cos (θ j) - Real.cos α) ^ 2 := by
      rw [pow_two]; exact mul_self_pos.mpr (sub_ne_zero.mpr (hb3 j))
    have hden2 : 0 < (1 - Real.cos (θ j)) ^ 2 := pow_pos (by linarith) 2
    have hinv : 1 / (Real.cos (θ j) - Real.cos α) ^ 2
        ≤ 4 / (1 - Real.cos (θ j)) ^ 2 := by
      have h := one_div_le_one_div_of_le hb hkey
      have heq : 1 / ((1 - Real.cos (θ j)) / 2) ^ 2
          = 4 / (1 - Real.cos (θ j)) ^ 2 := by
        field_simp
        ring
      linarith [h, heq]
    have hstep1 : (Real.sin α) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
        ≤ 4 * (Real.sin α) ^ 2 / (1 - Real.cos (θ j)) ^ 2 := by
      rw [show (Real.sin α) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
          = (Real.sin α) ^ 2 * (1 / (Real.cos (θ j) - Real.cos α) ^ 2) by ring]
      rw [show 4 * (Real.sin α) ^ 2 / (1 - Real.cos (θ j)) ^ 2
          = (Real.sin α) ^ 2 * (4 / (1 - Real.cos (θ j)) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
    have hsinα : (Real.sin α) ^ 2 ≤ α ^ 2 * (α ^ 2 * c ^ 2) := by
      have h1 : (Real.sin α) ^ 2 ≤ α ^ 2 := Real.sin_sq_le_sq (x := α)
      have h2 : 1 ≤ α ^ 2 * c ^ 2 := by rw [hc]; exact one_le_sq_cot hαpos hα1
      nlinarith [h1, h2, sq_nonneg α]
    rw [show 2 * ((a j) ^ 2 * (Real.sin α) ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2)
        = (2 * (a j) ^ 2 * (Real.sin α) ^ 2) / (Real.cos (θ j) - Real.cos α) ^ 2 by ring]
    rw [show 8 * α ^ 4 * c ^ 2 * ((a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2)
        = (8 * α ^ 4 * c ^ 2 * (a j) ^ 2) / (1 - Real.cos (θ j)) ^ 2 by ring]
    rw [div_le_div_iff₀ hden1 hden2]
    have hL : 2 * (a j) ^ 2 * (Real.sin α) ^ 2 * (1 - Real.cos (θ j)) ^ 2
        ≤ 2 * (a j) ^ 2 * (α ^ 2 * (α ^ 2 * c ^ 2)) * (1 - Real.cos (θ j)) ^ 2 := by
      have hstep2 : 2 * (a j) ^ 2 * (Real.sin α) ^ 2
          ≤ 2 * (a j) ^ 2 * (α ^ 2 * (α ^ 2 * c ^ 2)) :=
        mul_le_mul_of_nonneg_left hsinα (by positivity)
      have hstep3 : (0 : ℝ) ≤ (1 - Real.cos (θ j)) ^ 2 := sq_nonneg _
      calc 2 * (a j) ^ 2 * (Real.sin α) ^ 2 * (1 - Real.cos (θ j)) ^ 2
          = (2 * (a j) ^ 2 * (Real.sin α) ^ 2) * (1 - Real.cos (θ j)) ^ 2 := by ring
        _ ≤ (2 * (a j) ^ 2 * (α ^ 2 * (α ^ 2 * c ^ 2))) * (1 - Real.cos (θ j)) ^ 2 :=
            mul_le_mul_of_nonneg_right hstep2 hstep3
        _ = 2 * (a j) ^ 2 * (α ^ 2 * (α ^ 2 * c ^ 2)) * (1 - Real.cos (θ j)) ^ 2 := by ring
    have hR : 2 * (a j) ^ 2 * (α ^ 2 * (α ^ 2 * c ^ 2)) * (1 - Real.cos (θ j)) ^ 2
        ≤ 8 * α ^ 4 * c ^ 2 * (a j) ^ 2 * (Real.cos (θ j) - Real.cos α) ^ 2 := by
      have hnn : (0 : ℝ) ≤ 8 * α ^ 4 * c ^ 2 * (a j) ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hkey hnn
      nlinarith [h]
    nlinarith [hL, hR]
  have hsum : 2 * T ≤ 8 * α ^ 4 * c ^ 2 * D := by
    rw [hT, hD, Finset.mul_sum]
    have hrhs : 8 * α ^ 4 * c ^ 2 * ∑ j, (a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2
        = ∑ j, 8 * α ^ 4 * c ^ 2 * ((a j) ^ 2 / (1 - Real.cos (θ j)) ^ 2) := by
      rw [Finset.mul_sum]
    rw [hrhs]
    exact Finset.sum_le_sum fun j _ => hterm j
  have hAδ : a0 ^ 2 * c ^ 2 * δ = 8 * α ^ 4 * c ^ 2 * D := by
    rw [hδ]
    field_simp
  have h2T : 2 * T ≤ a0 ^ 2 * c ^ 2 * δ := by
    rw [hAδ]
    exact hsum
  have hD0 : 0 ≤ D := by
    rw [hD]
    apply Finset.sum_nonneg
    intro j _
    positivity
  have hT0 : 0 ≤ T := by
    rw [hT]
    apply Finset.sum_nonneg
    intro j _
    apply div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have ha0sq : 0 < a0 ^ 2 := by
    rw [pow_two]
    exact mul_self_pos.mpr ha0
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact div_nonneg (mul_nonneg (by positivity) hD0) ha0sq.le
  have hδ1' : δ ≤ 1 := by
    rw [hδ, hD]
    exact hδ1
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg _
  have hA0 : 0 ≤ a0 ^ 2 * c ^ 2 := by positivity
  rw [hδstmt, normSq_wStart_eq θ a0 a α hb1 hb2 hb3]
  rw [show 2 * a0 ^ 2 * Real.cot (α / 2) ^ 2
        + 4 * ∑ j, (a j) ^ 2 * Real.sin α ^ 2 / (Real.cos (θ j) - Real.cos α) ^ 2
      = 2 * (a0 ^ 2 * c ^ 2) + 4 * T by rw [hc, hT]; ring]
  have hsq : (1 - δ) ^ 2 ≤ 1 - δ := by nlinarith [hδ0, hδ1']
  have h4T : 4 * T ≤ δ * (2 * (a0 ^ 2 * c ^ 2) + 4 * T) := by
    nlinarith [h2T, hδ0, hA0, hT0]
  nlinarith [hsq, h4T, hA0, hT0, hδ0, hδ1']

end Qatlib.Papers.QWalkAmbainis04.MainResults.AbstractSearch.Lemmas45
