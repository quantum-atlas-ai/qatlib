/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Qatlib.Papers.QSearchAdvice09.MainResults.Harmonic
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset

open scoped BigOperators

namespace Qatlib.Papers.QSearchAdvice09.MainResults

theorem rpow_antitone_of_nonpos {z : ℝ} (hz : z ≤ 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ z ≤ a ^ z := by
  rcases lt_or_eq_of_le hz with hz' | rfl
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    have hratio : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
    have hstep : (b / a) ^ z ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hratio hz
    calc b ^ z = (a * (b / a)) ^ z := by field_simp
      _ = a ^ z * (b / a) ^ z := Real.mul_rpow ha.le (by positivity)
      _ ≤ a ^ z * 1 := by gcongr
      _ = a ^ z := by ring
  · simp

theorem rpow_monotone_of_nonneg {z : ℝ} (hz : 0 ≤ z) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ z ≤ b ^ z :=
  Real.rpow_le_rpow ha hab hz

theorem rpow_succ_ge_two_mul {r : ℝ} (hr : r ≤ 0) {x : ℝ} (hx : 1 ≤ x) :
    2 ^ r * x ^ r ≤ (x + 1) ^ r := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h2 : (2 : ℝ) ≤ 2 * x := by linarith
  have hx1 : x + 1 ≤ 2 * x := by linarith
  calc 2 ^ r * x ^ r = (2 * x) ^ r := by
        rw [Real.mul_rpow (by norm_num) hx0.le]
    _ ≤ (x + 1) ^ r := rpow_antitone_of_nonpos hr (by linarith) hx1

theorem rpow_succ_le_two_mul {r : ℝ} (hr : 0 ≤ r) {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ r ≤ 2 ^ r * x ^ r := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : x + 1 ≤ 2 * x := by linarith
  calc (x + 1) ^ r ≤ (2 * x) ^ r := rpow_monotone_of_nonneg hr (by positivity) hx1
    _ = 2 ^ r * x ^ r := Real.mul_rpow (by norm_num) hx0.le

theorem rpow_slope_exists {s : ℝ} {x : ℝ} (hx : 1 ≤ x) :
    ∃ c ∈ Set.Ioo x (x + 1), (x + 1) ^ s - x ^ s = s * c ^ (s - 1) := by
  have hlt : x < x + 1 := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ s) (Set.Icc x (x + 1)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hx ht.1
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith : t ≠ 0))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => t ^ s) (Set.Ioo x (x + 1)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hx (le_of_lt ht.1)
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith : t ≠ 0))).differentiableAt
      |>.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun t : ℝ => t ^ s) hlt hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [Real.deriv_rpow_const] at hcd
  rw [show x + 1 - x = 1 by ring, div_one] at hcd
  linarith

theorem rpow_diff_bounds_convex {s : ℝ} (hs : s ≤ 0 ∨ 1 ≤ s) {x : ℝ} (hx : 1 ≤ x) :
    s * x ^ (s - 1) ≤ (x + 1) ^ s - x ^ s ∧
      (x + 1) ^ s - x ^ s ≤ s * (x + 1) ^ (s - 1) := by
  obtain ⟨c, hc, heq⟩ := rpow_slope_exists (s := s) (x := x) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hc0 : (0 : ℝ) < c := by linarith [hc.1]
  rcases hs with hs | hs
  · have hexp : s - 1 < 0 := by linarith
    have h1 : c ^ (s - 1) ≤ x ^ (s - 1) :=
      rpow_antitone_of_nonpos hexp.le hx0 (le_of_lt hc.1)
    have h2 : (x + 1) ^ (s - 1) ≤ c ^ (s - 1) :=
      rpow_antitone_of_nonpos hexp.le (by linarith) (le_of_lt hc.2)
    constructor
    · have := mul_le_mul_of_nonpos_left h1 hs
      linarith [heq]
    · have := mul_le_mul_of_nonpos_left h2 hs
      linarith [heq]
  · have hexp : 0 ≤ s - 1 := by linarith
    have h1 : x ^ (s - 1) ≤ c ^ (s - 1) :=
      rpow_monotone_of_nonneg hexp hx0.le (le_of_lt hc.1)
    have h2 : c ^ (s - 1) ≤ (x + 1) ^ (s - 1) :=
      rpow_monotone_of_nonneg hexp hc0.le (le_of_lt hc.2)
    constructor
    · have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ s)
      linarith [heq]
    · have := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ s)
      linarith [heq]

theorem rpow_diff_bounds_concave {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    s * (x + 1) ^ (s - 1) ≤ (x + 1) ^ s - x ^ s ∧
      (x + 1) ^ s - x ^ s ≤ s * x ^ (s - 1) := by
  obtain ⟨c, hc, heq⟩ := rpow_slope_exists (s := s) (x := x) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hc0 : (0 : ℝ) < c := by linarith [hc.1]
  have hnegexp : s - 1 ≤ 0 := by linarith
  have h1 : c ^ (s - 1) ≤ x ^ (s - 1) :=
    rpow_antitone_of_nonpos hnegexp hx0 (le_of_lt hc.1)
  have h2 : (x + 1) ^ (s - 1) ≤ c ^ (s - 1) :=
    rpow_antitone_of_nonpos hnegexp (by linarith) (le_of_lt hc.2)
  constructor
  · have := mul_le_mul_of_nonneg_left h2 hs0.le
    linarith [heq]
  · have := mul_le_mul_of_nonneg_left h1 hs0.le
    linarith [heq]

def sumPow (r : ℝ) (n : ℕ) : ℝ := ∑ k ∈ range n, ((k : ℝ) + 1) ^ r

theorem sumPow_nonneg (r : ℝ) (n : ℕ) : 0 ≤ sumPow r n := by
  unfold sumPow
  refine sum_nonneg ?_
  intro k _
  positivity

theorem sumPow_pos (r : ℝ) {n : ℕ} (hn : 1 ≤ n) : 0 < sumPow r n := by
  unfold sumPow
  refine sum_pos' ?_ ?_
  · intro k _
    positivity
  · exact ⟨0, by simp only [mem_range]; omega, by simp⟩

theorem sum_range_pow_succ_sub (s : ℝ) (n : ℕ) :
    ∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ s - ((k : ℝ) + 1) ^ s)
      = ((n : ℝ) + 1) ^ s - 1 := by
  have h := Finset.sum_range_sub (fun k : ℕ => ((k : ℝ) + 1) ^ s) n
  simpa using h

theorem sumPow_upper_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    sumPow r n ≤ ((n : ℝ) + 1) ^ (r + 1) / (r + 1) := by
  have hstep : ∀ k ∈ range n, ((k : ℝ) + 1) ^ r ≤
      ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) / (r + 1) := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_convex (s := r + 1) (Or.inr (by linarith)) hx).1
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < r + 1)]
    linarith
  calc sumPow r n = ∑ k ∈ range n, ((k : ℝ) + 1) ^ r := rfl
    _ ≤ ∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) / (r + 1) :=
        sum_le_sum hstep
    _ = (∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1))) / (r + 1) := by
        rw [sum_div]
    _ = (((n : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) := by
        rw [sum_range_pow_succ_sub]
    _ ≤ ((n : ℝ) + 1) ^ (r + 1) / (r + 1) := by
        apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ r + 1)
        linarith

theorem sumPow_lower_pos {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (((n : ℝ) + 1) ^ (r + 1) - 1) / ((r + 1) * 2 ^ r) ≤ sumPow r n := by
  have hstep : ∀ k ∈ range n,
      ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) / ((r + 1) * 2 ^ r)
        ≤ ((k : ℝ) + 1) ^ r := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_convex (s := r + 1) (Or.inr (by linarith)) hx).2
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    have h2 := rpow_succ_le_two_mul hr.le hx
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (r + 1) * 2 ^ r)]
    nlinarith [h, h2, hr]
  calc (((n : ℝ) + 1) ^ (r + 1) - 1) / ((r + 1) * 2 ^ r)
      = (∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1))) /
          ((r + 1) * 2 ^ r) := by rw [sum_range_pow_succ_sub]
    _ = ∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) /
          ((r + 1) * 2 ^ r) := by rw [sum_div]
    _ ≤ sumPow r n := by
        unfold sumPow
        exact sum_le_sum hstep

theorem sumPow_lower_neg {r : ℝ} (hr0 : -1 < r) (hr1 : r < 0) (n : ℕ) :
    (((n : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) ≤ sumPow r n := by
  have hs0 : (0 : ℝ) < r + 1 := by linarith
  have hs1 : r + 1 ≤ 1 := by linarith
  have hstep : ∀ k ∈ range n,
      ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) / (r + 1)
        ≤ ((k : ℝ) + 1) ^ r := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_concave hs0 hs1 hx).2
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    rw [div_le_iff₀ hs0]
    linarith
  calc (((n : ℝ) + 1) ^ (r + 1) - 1) / (r + 1)
      = (∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1))) /
          (r + 1) := by rw [sum_range_pow_succ_sub]
    _ = ∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) /
          (r + 1) := by rw [sum_div]
    _ ≤ sumPow r n := by
        unfold sumPow
        exact sum_le_sum hstep

theorem sumPow_upper_neg {r : ℝ} (hr0 : -1 < r) (hr1 : r < 0) (n : ℕ) :
    sumPow r n ≤ ((n : ℝ) + 1) ^ (r + 1) / ((r + 1) * 2 ^ r) := by
  have hs0 : (0 : ℝ) < r + 1 := by linarith
  have hs1 : r + 1 ≤ 1 := by linarith
  have hstep : ∀ k ∈ range n, ((k : ℝ) + 1) ^ r ≤
      ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) / ((r + 1) * 2 ^ r) := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_concave hs0 hs1 hx).1
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    have h2 := rpow_succ_ge_two_mul hr1.le hx
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (r + 1) * 2 ^ r)]
    nlinarith [h, h2, hs0]
  calc sumPow r n = ∑ k ∈ range n, ((k : ℝ) + 1) ^ r := rfl
    _ ≤ ∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1)) /
          ((r + 1) * 2 ^ r) := sum_le_sum hstep
    _ = (∑ k ∈ range n, ((((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1) - ((k : ℝ) + 1) ^ (r + 1))) /
          ((r + 1) * 2 ^ r) := by rw [sum_div]
    _ = (((n : ℝ) + 1) ^ (r + 1) - 1) / ((r + 1) * 2 ^ r) := by rw [sum_range_pow_succ_sub]
    _ ≤ ((n : ℝ) + 1) ^ (r + 1) / ((r + 1) * 2 ^ r) := by
        apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (r + 1) * 2 ^ r)
        linarith

theorem sum_range_pow_sub_succ (s : ℝ) (n : ℕ) :
    ∑ k ∈ range n, (((k : ℝ) + 1) ^ s - (((k + 1 : ℕ) : ℝ) + 1) ^ s)
      = 1 - ((n : ℝ) + 1) ^ s := by
  have h := Finset.sum_range_sub' (fun k : ℕ => ((k : ℝ) + 1) ^ s) n
  simpa using h

theorem sumPow_lower_lt {r : ℝ} (hr : r < -1) {n : ℕ} (hn : 1 ≤ n) :
    (1 - 2 ^ (r + 1)) / (-(r + 1)) ≤ sumPow r n := by
  have hs : r + 1 < 0 := by linarith
  have hstep : ∀ k ∈ range n,
      (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1)) / (-(r + 1))
        ≤ ((k : ℝ) + 1) ^ r := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_convex (s := r + 1) (Or.inl hs.le) hx).1
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < -(r + 1))]
    nlinarith [h]
  have hpow : ((n : ℝ) + 1) ^ (r + 1) ≤ 2 ^ (r + 1) :=
    rpow_antitone_of_nonpos hs.le (by norm_num) (by exact_mod_cast Nat.succ_le_succ hn)
  calc (1 - 2 ^ (r + 1)) / (-(r + 1))
      ≤ (1 - ((n : ℝ) + 1) ^ (r + 1)) / (-(r + 1)) := by
        apply div_le_div_of_nonneg_right _ (by linarith : (0 : ℝ) ≤ -(r + 1))
        linarith
    _ = (∑ k ∈ range n, (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1))) /
          (-(r + 1)) := by rw [sum_range_pow_sub_succ]
    _ = ∑ k ∈ range n, (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1)) /
          (-(r + 1)) := by rw [sum_div]
    _ ≤ sumPow r n := by
        unfold sumPow
        exact sum_le_sum hstep

theorem sumPow_upper_lt {r : ℝ} (hr : r < -1) (n : ℕ) :
    sumPow r n ≤ 1 / (-(r + 1) * 2 ^ r) := by
  have hs : r + 1 < 0 := by linarith
  have hstep : ∀ k ∈ range n, ((k : ℝ) + 1) ^ r ≤
      (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1)) / (-(r + 1) * 2 ^ r) := by
    intro k _
    have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h := (rpow_diff_bounds_convex (s := r + 1) (Or.inl hs.le) hx).2
    rw [show r + 1 - 1 = r by ring] at h
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast]
    have h2 := rpow_succ_ge_two_mul (by linarith : r ≤ 0) hx
    rw [le_div_iff₀ (mul_pos (by linarith : (0:ℝ) < -(r + 1))
      (Real.rpow_pos_of_pos (by norm_num) r))]
    nlinarith [h, h2]
  calc sumPow r n = ∑ k ∈ range n, ((k : ℝ) + 1) ^ r := rfl
    _ ≤ ∑ k ∈ range n, (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1)) /
          (-(r + 1) * 2 ^ r) := sum_le_sum hstep
    _ = (∑ k ∈ range n, (((k : ℝ) + 1) ^ (r + 1) - (((k + 1 : ℕ) : ℝ) + 1) ^ (r + 1))) /
          (-(r + 1) * 2 ^ r) := by rw [sum_div]
    _ = (1 - ((n : ℝ) + 1) ^ (r + 1)) / (-(r + 1) * 2 ^ r) := by
        rw [sum_range_pow_sub_succ]
    _ ≤ 1 / (-(r + 1) * 2 ^ r) := by
        apply div_le_div_of_nonneg_right _
          (le_of_lt (mul_pos (by linarith : (0:ℝ) < -(r + 1))
            (Real.rpow_pos_of_pos (by norm_num) r)))
        linarith [Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1) (r + 1)]

theorem sumPow_zero (n : ℕ) : sumPow 0 n = (n : ℝ) := by
  unfold sumPow
  simp

theorem sumPow_neg_one (n : ℕ) : sumPow (-1) n = harmSum n := by
  unfold sumPow harmSum
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.rpow_neg_one, one_div]

theorem eventually_two_le_rpow {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ ((n : ℝ) + 1) ^ s := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) ^ (1 / s))
  filter_upwards [Filter.eventually_atTop.2 ⟨N + 1, fun n hn => hn⟩] with n hn
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hNle : (2 : ℝ) ^ (1 / s) < (n : ℝ) + 1 := by
    have hlt : (N : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : N < n)
    linarith [hN]
  have hbase : (0 : ℝ) ≤ (2 : ℝ) ^ (1 / s) := le_of_lt (Real.rpow_pos_of_pos h2pos _)
  calc (2 : ℝ) = ((2 : ℝ) ^ (1 / s)) ^ s := by
        rw [← Real.rpow_mul h2pos.le (1 / s) s]
        have h1 : 1 / s * s = 1 := by field_simp
        rw [h1, Real.rpow_one]
    _ ≤ ((n : ℝ) + 1) ^ s := Real.rpow_le_rpow hbase (le_of_lt hNle) hs.le

theorem sumPow_isTheta_pos {r : ℝ} (hr : -1 < r) :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => sumPow r n)
      (fun n : ℕ => (n : ℝ) ^ (r + 1)) := by
  have hspos : (0 : ℝ) < r + 1 := by linarith
  rcases lt_trichotomy r 0 with hr0 | rfl | hr0
  · constructor
    · refine Asymptotics.IsBigO.of_bound (2 ^ (r + 1) / ((r + 1) * 2 ^ r)) ?_
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      rw [Real.norm_of_nonneg (sumPow_nonneg r n),
        Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)]
      have hb := sumPow_upper_neg hr hr0 n
      have hnp1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have hpow : ((n : ℝ) + 1) ^ (r + 1) ≤ 2 ^ (r + 1) * (n : ℝ) ^ (r + 1) := by
        calc ((n : ℝ) + 1) ^ (r + 1) ≤ (2 * (n : ℝ)) ^ (r + 1) :=
              Real.rpow_le_rpow (by linarith) hnp1 hspos.le
          _ = 2 ^ (r + 1) * (n : ℝ) ^ (r + 1) := Real.mul_rpow (by norm_num) hnpos.le
      have hcoef : (0 : ℝ) < (r + 1) * 2 ^ r :=
        mul_pos hspos (Real.rpow_pos_of_pos (by norm_num) r)
      calc sumPow r n ≤ ((n : ℝ) + 1) ^ (r + 1) / ((r + 1) * 2 ^ r) := hb
        _ ≤ (2 ^ (r + 1) * (n : ℝ) ^ (r + 1)) / ((r + 1) * 2 ^ r) := by
            apply div_le_div_of_nonneg_right hpow hcoef.le
        _ = (2 ^ (r + 1) / ((r + 1) * 2 ^ r)) * (n : ℝ) ^ (r + 1) := by ring
    · refine Asymptotics.IsBigO.of_bound (2 * (r + 1)) ?_
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩,
        eventually_two_le_rpow hspos] with n hn htwo
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _),
        Real.norm_of_nonneg (sumPow_nonneg r n)]
      have hb := sumPow_lower_neg hr hr0 n
      have hbase : (n : ℝ) ^ (r + 1) ≤ ((n : ℝ) + 1) ^ (r + 1) :=
        Real.rpow_le_rpow hnpos.le (by linarith) hspos.le
      have hstep : (n : ℝ) ^ (r + 1) / 2 ≤ ((n : ℝ) + 1) ^ (r + 1) - 1 := by linarith
      have hdiv : (n : ℝ) ^ (r + 1) / (2 * (r + 1)) ≤
          (((n : ℝ) + 1) ^ (r + 1) - 1) / (r + 1) := by
        have h := div_le_div_of_nonneg_right hstep hspos.le
        have heqc : (n : ℝ) ^ (r + 1) / (2 * (r + 1)) =
            ((n : ℝ) ^ (r + 1) / 2) / (r + 1) := by rw [div_div]
        rw [heqc]
        exact h
      have hsum : (n : ℝ) ^ (r + 1) / (2 * (r + 1)) ≤ sumPow r n := le_trans hdiv hb
      have hmul := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * (r + 1))
      have hleft : 2 * (r + 1) * ((n : ℝ) ^ (r + 1) / (2 * (r + 1))) = (n : ℝ) ^ (r + 1) := by
        have hne : (2 * (r + 1) : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      rw [hleft] at hmul
      exact hmul
  · have hfun : (fun n : ℕ => sumPow 0 n) =
        (fun n : ℕ => (n : ℝ) ^ ((0 : ℝ) + 1)) := by
      funext n
      rw [sumPow_zero]
      norm_num [Real.rpow_one]
    rw [hfun]
  · constructor
    · refine Asymptotics.IsBigO.of_bound (2 ^ (r + 1) / (r + 1)) ?_
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      rw [Real.norm_of_nonneg (sumPow_nonneg r n),
        Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)]
      have hb := sumPow_upper_pos hr0 n
      have hnp1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
      have hpow : ((n : ℝ) + 1) ^ (r + 1) ≤ 2 ^ (r + 1) * (n : ℝ) ^ (r + 1) := by
        calc ((n : ℝ) + 1) ^ (r + 1) ≤ (2 * (n : ℝ)) ^ (r + 1) :=
              Real.rpow_le_rpow (by linarith) hnp1 hspos.le
          _ = 2 ^ (r + 1) * (n : ℝ) ^ (r + 1) := Real.mul_rpow (by norm_num) hnpos.le
      calc sumPow r n ≤ ((n : ℝ) + 1) ^ (r + 1) / (r + 1) := hb
        _ ≤ (2 ^ (r + 1) * (n : ℝ) ^ (r + 1)) / (r + 1) := by
            apply div_le_div_of_nonneg_right hpow hspos.le
        _ = (2 ^ (r + 1) / (r + 1)) * (n : ℝ) ^ (r + 1) := by ring
    · refine Asymptotics.IsBigO.of_bound (2 * ((r + 1) * 2 ^ r)) ?_
      filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩,
        eventually_two_le_rpow hspos] with n hn htwo
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _),
        Real.norm_of_nonneg (sumPow_nonneg r n)]
      have hb := sumPow_lower_pos hr0 n
      have hbase : (n : ℝ) ^ (r + 1) ≤ ((n : ℝ) + 1) ^ (r + 1) :=
        Real.rpow_le_rpow hnpos.le (by linarith) hspos.le
      have hcoef : (0 : ℝ) < (r + 1) * 2 ^ r :=
        mul_pos hspos (Real.rpow_pos_of_pos (by norm_num) r)
      have hstep : (n : ℝ) ^ (r + 1) / 2 ≤ ((n : ℝ) + 1) ^ (r + 1) - 1 := by linarith
      have hdiv : (n : ℝ) ^ (r + 1) / (2 * ((r + 1) * 2 ^ r)) ≤
          (((n : ℝ) + 1) ^ (r + 1) - 1) / ((r + 1) * 2 ^ r) := by
        have h := div_le_div_of_nonneg_right hstep hcoef.le
        have heqc : (n : ℝ) ^ (r + 1) / (2 * ((r + 1) * 2 ^ r)) =
            ((n : ℝ) ^ (r + 1) / 2) / ((r + 1) * 2 ^ r) := by rw [div_div]
        rw [heqc]
        exact h
      have hsum : (n : ℝ) ^ (r + 1) / (2 * ((r + 1) * 2 ^ r)) ≤ sumPow r n :=
        le_trans hdiv hb
      have hmul := mul_le_mul_of_nonneg_left hsum
        (by positivity : (0 : ℝ) ≤ 2 * ((r + 1) * 2 ^ r))
      have hleft : 2 * ((r + 1) * 2 ^ r) *
          ((n : ℝ) ^ (r + 1) / (2 * ((r + 1) * 2 ^ r))) = (n : ℝ) ^ (r + 1) := by
        have hne : (2 * ((r + 1) * 2 ^ r) : ℝ) ≠ 0 := by positivity
        field_simp [hne]
      rw [hleft] at hmul
      exact hmul

theorem sumPow_isTheta_lt {r : ℝ} (hr : r < -1) :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => sumPow r n) (fun _ : ℕ => (1 : ℝ)) := by
  constructor
  · refine Asymptotics.IsBigO.of_bound (1 / (-(r + 1) * 2 ^ r)) ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [Real.norm_of_nonneg (sumPow_nonneg r n),
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    have hb := sumPow_upper_lt hr n
    rw [mul_one]
    exact hb
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1),
      Real.norm_of_nonneg (sumPow_nonneg r n)]
    rw [one_mul]
    have hmem : 0 ∈ Finset.range n := by
      rw [Finset.mem_range]; omega
    have hnonneg : ∀ k ∈ Finset.range n, 0 ≤ ((k : ℝ) + 1) ^ r := by
      intro k _
      positivity
    have hsingle : ((0 : ℝ) + 1) ^ r ≤ sumPow r n := by
      unfold sumPow
      simpa using (Finset.single_le_sum hnonneg hmem)
    simpa using hsingle

theorem sumPow_isTheta_neg_one :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => sumPow (-1) n)
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have hfun : (fun n : ℕ => sumPow (-1) n) = harmSum := by
    funext n
    exact sumPow_neg_one n
  rw [hfun]
  exact harmSum_isTheta

theorem sum_Icc_one_eq_sumPow (r : ℝ) (n : ℕ) :
    ∑ x ∈ Finset.Icc 1 n, (x : ℝ) ^ r = sumPow r n := by
  unfold sumPow
  have hI : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  ring

theorem isTheta_congr {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (h : Asymptotics.IsTheta Filter.atTop f₁ g₁)
    (hf : f₁ =ᶠ[Filter.atTop] f₂) (hg : g₁ =ᶠ[Filter.atTop] g₂) :
    Asymptotics.IsTheta Filter.atTop f₂ g₂ :=
  ⟨h.1.congr' hf hg, h.2.congr' hg hf⟩

theorem isTheta_rpow_div {a b c : ℝ} (hc : a - b = c) :
    Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  have heq : (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) =ᶠ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ c) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by omega
      exact_mod_cast this
    rw [← Real.rpow_sub hnpos a b, hc]
  have hq : (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) =ᶠ[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) := Filter.EventuallyEq.rfl
  exact isTheta_congr
    (f₁ := fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b)
    (g₁ := fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b)
    (f₂ := fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) (g₂ := fun n : ℕ => (n : ℝ) ^ c)
    ⟨Asymptotics.isBigO_refl _ Filter.atTop, Asymptotics.isBigO_refl _ Filter.atTop⟩
    hq heq

end Qatlib.Papers.QSearchAdvice09.MainResults
