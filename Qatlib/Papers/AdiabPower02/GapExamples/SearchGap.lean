/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
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
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.UnorderedInterval
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
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Real

namespace Qatlib.Papers.AdiabPower02.GapExamples

def searchGap (N s : ℝ) : ℝ :=
  Real.sqrt ((N + 4 * (N - 1) * (s ^ 2 - s)) / N)

lemma searchNum_eq (N s : ℝ) :
    N + 4 * (N - 1) * (s ^ 2 - s) = 1 + 4 * (N - 1) * (s - 1 / 2) ^ 2 := by
  ring

lemma searchNum_pos {N : ℝ} (hN : 1 ≤ N) (s : ℝ) :
    0 < N + 4 * (N - 1) * (s ^ 2 - s) := by
  rw [searchNum_eq]
  have h : 0 ≤ 4 * (N - 1) * (s - 1 / 2) ^ 2 := by positivity
  linarith

lemma searchGap_sq {N : ℝ} (hN : 1 ≤ N) (s : ℝ) :
    searchGap N s ^ 2 = (N + 4 * (N - 1) * (s ^ 2 - s)) / N := by
  rw [searchGap, Real.sq_sqrt
    (div_nonneg (le_of_lt (searchNum_pos hN s)) (by linarith))]

theorem searchGap_half {N : ℝ} (hN : 1 ≤ N) :
    searchGap N (1 / 2) = 1 / Real.sqrt N := by
  rw [searchGap]
  have hnum : (N + 4 * (N - 1) * ((1 / 2 : ℝ) ^ 2 - 1 / 2)) / N = 1 / N := by
    field_simp; ring
  rw [hnum, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  simp

theorem searchGap_ge_min {N s : ℝ} (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
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

def searchAnti (N s : ℝ) : ℝ :=
  N / (2 * Real.sqrt (N - 1)) * Real.arctan (2 * Real.sqrt (N - 1) * (s - 1 / 2))

lemma one_div_searchGap_sq {N : ℝ} (hN : 1 < N) (s : ℝ) :
    1 / (searchGap N s) ^ 2 = N / (N + 4 * (N - 1) * (s ^ 2 - s)) := by
  rw [searchGap_sq (le_of_lt hN)]
  have hnum : 0 < N + 4 * (N - 1) * (s ^ 2 - s) := searchNum_pos (le_of_lt hN) s
  have hNpos : 0 < N := by linarith
  field_simp

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
