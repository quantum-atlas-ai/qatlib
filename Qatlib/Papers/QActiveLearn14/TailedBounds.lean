/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
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
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QActiveLearn14.TailedBounds

open Finset
open scoped BigOperators

variable {X : Type*} [Fintype X]

def IsProbability (μ : X → ℝ) : Prop := (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

def l1Dist (μ ν : X → ℝ) : ℝ := ∑ x, |μ x - ν x|

def tvDist (μ ν : X → ℝ) : ℝ := (1 / 2) * ∑ x, |μ x - ν x|

lemma l1Dist_nonneg (μ ν : X → ℝ) : 0 ≤ l1Dist μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma tvDist_nonneg (μ ν : X → ℝ) : 0 ≤ tvDist μ ν := by
  unfold tvDist
  positivity

lemma tvDist_eq_half_l1 (μ ν : X → ℝ) : tvDist μ ν = l1Dist μ ν / 2 := by
  unfold tvDist l1Dist
  ring

lemma l1Dist_eq_two_mul_tvDist (μ ν : X → ℝ) : l1Dist μ ν = 2 * tvDist μ ν := by
  rw [tvDist_eq_half_l1]
  ring

lemma l1Dist_comm (μ ν : X → ℝ) : l1Dist μ ν = l1Dist ν μ := by
  unfold l1Dist
  congr 1
  funext x
  rw [abs_sub_comm]

lemma l1Dist_triangle (μ ν ρ : X → ℝ) :
    l1Dist μ ρ ≤ l1Dist μ ν + l1Dist ν ρ := by
  unfold l1Dist
  calc ∑ x, |μ x - ρ x|
      ≤ ∑ x, (|μ x - ν x| + |ν x - ρ x|) := by
        apply Finset.sum_le_sum
        intro x _
        have h := abs_add_le (μ x - ν x) (ν x - ρ x)
        have heq : (μ x - ν x) + (ν x - ρ x) = μ x - ρ x := by ring
        rwa [heq] at h
    _ = ∑ x, |μ x - ν x| + ∑ x, |ν x - ρ x| := Finset.sum_add_distrib

lemma tvDist_triangle (μ ν ρ : X → ℝ) :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  unfold tvDist
  have h := l1Dist_triangle μ ν ρ
  unfold l1Dist at h
  linarith

lemma tvDist_le_one {μ ν : X → ℝ} (hμ : IsProbability μ) (hν : IsProbability ν) :
    tvDist μ ν ≤ 1 := by
  have hterm : ∀ x, |μ x - ν x| ≤ μ x + ν x := by
    intro x
    calc |μ x - ν x| = |μ x + (-ν x)| := by ring_nf
      _ ≤ |μ x| + |-ν x| := abs_add_le _ _
      _ = μ x + ν x := by
          rw [abs_of_nonneg (hμ.1 x), abs_neg, abs_of_nonneg (hν.1 x)]
  unfold tvDist
  have hsum : ∑ x, |μ x - ν x| ≤ ∑ x, (μ x + ν x) := Finset.sum_le_sum fun x _ => hterm x
  have hsplit : ∑ x, (μ x + ν x) = 2 := by
    rw [Finset.sum_add_distrib, hμ.2, hν.2]
    norm_num
  rw [hsplit] at hsum
  linarith

lemma tvDist_convex_mix {κ ν σ πtilde : X → ℝ} {p : ℝ}
    (hmix : ∀ x, κ x = p * ν x + (1 - p) * σ x)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    tvDist κ πtilde ≤ p * tvDist ν πtilde + (1 - p) * tvDist σ πtilde := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hterm : ∀ x, |κ x - πtilde x| ≤
      p * |ν x - πtilde x| + (1 - p) * |σ x - πtilde x| := by
    intro x
    have h : κ x - πtilde x =
        p * (ν x - πtilde x) + (1 - p) * (σ x - πtilde x) := by
      rw [hmix x]; ring
    rw [h]
    calc |p * (ν x - πtilde x) + (1 - p) * (σ x - πtilde x)|
        ≤ |p * (ν x - πtilde x)| + |(1 - p) * (σ x - πtilde x)| := abs_add_le _ _
      _ = p * |ν x - πtilde x| + (1 - p) * |σ x - πtilde x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg h1p]
  unfold tvDist
  have hsum : ∑ x, |κ x - πtilde x| ≤
      ∑ x, (p * |ν x - πtilde x| + (1 - p) * |σ x - πtilde x|) :=
    Finset.sum_le_sum fun x _ => hterm x
  have hsplit : ∑ x, (p * |ν x - πtilde x| + (1 - p) * |σ x - πtilde x|)
      = p * ∑ x, |ν x - πtilde x| + (1 - p) * ∑ x, |σ x - πtilde x| := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [hsplit] at hsum
  nlinarith [hsum]

variable [DecidableEq X]

def flaggedMass (π : X → ℝ) (S : Finset X) : ℝ := ∑ x ∈ S, π x

def tailed (π : X → ℝ) (S : Finset X) : X → ℝ :=
  fun x => if x ∈ S then π x / flaggedMass π S else 0

lemma sum_tailed (π : X → ℝ) (S : Finset X) (hε : flaggedMass π S ≠ 0) :
    ∑ x, tailed π S x = 1 := by
  have h : ∀ x, tailed π S x = if x ∈ S then π x / flaggedMass π S else 0 := fun x => rfl
  simp only [h, Finset.sum_ite_mem]
  rw [Finset.univ_inter]
  rw [← Finset.sum_div]
  rw [show (∑ x ∈ S, π x) = flaggedMass π S from rfl]
  exact div_self hε

omit [Fintype X] in

lemma tailed_nonneg {π : X → ℝ} (hπ : ∀ x, 0 ≤ π x) {S : Finset X}
    (hε : 0 < flaggedMass π S) (x : X) : 0 ≤ tailed π S x := by
  unfold tailed
  split_ifs with hx
  · exact div_nonneg (hπ x) hε.le
  · exact le_rfl

lemma tailed_isProbability {π : X → ℝ} (hπ : ∀ x, 0 ≤ π x) {S : Finset X}
    (hε : 0 < flaggedMass π S) : IsProbability (tailed π S) :=
  ⟨tailed_nonneg hπ hε, sum_tailed π S (ne_of_gt hε)⟩

lemma tail_term_bound {a a' e e' : ℝ} (ha' : 0 ≤ a') (he : 0 < e) (he' : 0 < e') :
    |a' / e' - a / e| ≤ a' * |e - e'| / (e * e') + |a' - a| / e := by
  have hden : 0 < e * e' := mul_pos he he'
  have hdecomp : a' / e' - a / e = (a' * (e - e') + (a' - a) * e') / (e * e') := by
    field_simp
    ring
  rw [hdecomp, abs_div, abs_of_pos hden]
  have hnum : |a' * (e - e') + (a' - a) * e'| ≤ a' * |e - e'| + e' * |a' - a| := by
    calc |a' * (e - e') + (a' - a) * e'|
        ≤ |a' * (e - e')| + |(a' - a) * e'| := abs_add_le _ _
      _ = a' * |e - e'| + e' * |a' - a| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha', abs_of_pos he']
          ring
  calc |a' * (e - e') + (a' - a) * e'| / (e * e')
      ≤ (a' * |e - e'| + e' * |a' - a|) / (e * e') :=
        div_le_div_of_nonneg_right hnum hden.le
    _ = a' * |e - e'| / (e * e') + |a' - a| / e := by
        field_simp

lemma abs_sum_sub_le_sum_abs {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ x ∈ s, f x - ∑ x ∈ s, g x| ≤ ∑ x ∈ s, |f x - g x| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

lemma tail_l1_bound (π π' : X → ℝ) (S : Finset X)
    (hπ' : ∀ x, 0 ≤ π' x)
    (hε : 0 < flaggedMass π S) (hε' : 0 < flaggedMass π' S) :
    l1Dist (tailed π' S) (tailed π S) ≤
      (2 / flaggedMass π S) * ∑ x ∈ S, |π' x - π x| := by
  have hmassle : |flaggedMass π S - flaggedMass π' S| ≤ ∑ x ∈ S, |π x - π' x| := by
    unfold flaggedMass
    exact abs_sum_sub_le_sum_abs S π π'
  have hsum : ∑ x, |tailed π' S x - tailed π S x|
      = ∑ x ∈ S, |π' x / flaggedMass π' S - π x / flaggedMass π S| := by
    have hpt : ∀ x, tailed π' S x - tailed π S x =
        if x ∈ S then (π' x / flaggedMass π' S - π x / flaggedMass π S) else 0 := by
      intro x
      by_cases hx : x ∈ S <;> simp [tailed, hx]
    trans ∑ x, (if x ∈ S then
        |π' x / flaggedMass π' S - π x / flaggedMass π S| else 0)
    · apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S <;> simp [hpt x, hx]
    · rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hterm : ∑ x ∈ S, |π' x / flaggedMass π' S - π x / flaggedMass π S|
      ≤ ∑ x ∈ S, (π' x * |flaggedMass π S - flaggedMass π' S|
            / (flaggedMass π S * flaggedMass π' S)
          + |π' x - π x| / flaggedMass π S) := by
    apply Finset.sum_le_sum
    intro x _
    exact tail_term_bound (hπ' x) hε hε'
  have hsplit : ∑ x ∈ S, (π' x * |flaggedMass π S - flaggedMass π' S|
            / (flaggedMass π S * flaggedMass π' S)
          + |π' x - π x| / flaggedMass π S)
      = flaggedMass π' S * |flaggedMass π S - flaggedMass π' S|
            / (flaggedMass π S * flaggedMass π' S)
        + (∑ x ∈ S, |π' x - π x|) / flaggedMass π S := by
    rw [Finset.sum_add_distrib]
    simp only [← Finset.sum_div, ← Finset.sum_mul]
    rfl
  have habs : |flaggedMass π S - flaggedMass π' S| ≤ ∑ x ∈ S, |π' x - π x| := by
    have h := hmassle
    calc |flaggedMass π S - flaggedMass π' S| ≤ ∑ x ∈ S, |π x - π' x| := h
      _ = ∑ x ∈ S, |π' x - π x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_sub_comm]
  unfold l1Dist
  rw [hsum]
  calc ∑ x ∈ S, |π' x / flaggedMass π' S - π x / flaggedMass π S|
      ≤ ∑ x ∈ S, (π' x * |flaggedMass π S - flaggedMass π' S|
            / (flaggedMass π S * flaggedMass π' S)
          + |π' x - π x| / flaggedMass π S) := hterm
    _ = flaggedMass π' S * |flaggedMass π S - flaggedMass π' S|
            / (flaggedMass π S * flaggedMass π' S)
        + (∑ x ∈ S, |π' x - π x|) / flaggedMass π S := hsplit
    _ = |flaggedMass π S - flaggedMass π' S| / flaggedMass π S
        + (∑ x ∈ S, |π' x - π x|) / flaggedMass π S := by
          field_simp
    _ ≤ (∑ x ∈ S, |π' x - π x|) / flaggedMass π S
        + (∑ x ∈ S, |π' x - π x|) / flaggedMass π S := by
          have := div_le_div_of_nonneg_right habs hε.le
          linarith
    _ = (2 / flaggedMass π S) * ∑ x ∈ S, |π' x - π x| := by
          field_simp
          ring

theorem tailed_tv_bound (π π' : X → ℝ) (S : Finset X)
    (_hπ : ∀ x, 0 ≤ π x) (hπ' : ∀ x, 0 ≤ π' x)
    (hε : 0 < flaggedMass π S) (hε' : 0 < flaggedMass π' S) :
    tvDist (tailed π' S) (tailed π S) ≤ 2 * tvDist π' π / flaggedMass π S := by
  have h1 := tail_l1_bound π π' S hπ' hε hε'
  have hSle : ∑ x ∈ S, |π' x - π x| ≤ l1Dist π' π := by
    unfold l1Dist
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun x _ _ => abs_nonneg _)
  have h1' : l1Dist (tailed π' S) (tailed π S) ≤ (2 / flaggedMass π S) * l1Dist π' π := by
    calc l1Dist (tailed π' S) (tailed π S)
        ≤ (2 / flaggedMass π S) * ∑ x ∈ S, |π' x - π x| := h1
      _ ≤ (2 / flaggedMass π S) * l1Dist π' π := by
          apply mul_le_mul_of_nonneg_left hSle
          exact div_nonneg (by norm_num) hε.le
  calc tvDist (tailed π' S) (tailed π S)
      = l1Dist (tailed π' S) (tailed π S) / 2 := tvDist_eq_half_l1 _ _
    _ ≤ ((2 / flaggedMass π S) * l1Dist π' π) / 2 :=
        div_le_div_of_nonneg_right h1' (by norm_num)
    _ = ((2 / flaggedMass π S) * (2 * tvDist π' π)) / 2 := by
        rw [l1Dist_eq_two_mul_tvDist]
    _ = 2 * tvDist π' π / flaggedMass π S := by ring

theorem theorem4_classical_reflecting
    (π_s π₀ : X → ℝ) (S : Finset X) (k₁ : ℕ)
    (hπs : IsProbability π_s) (hπ0 : IsProbability π₀)
    (hε : 0 < flaggedMass π_s S) (hε' : 0 < flaggedMass π₀ S)
    (hmix : tvDist π₀ π_s ≤ Real.exp (-(k₁ : ℝ))) :
    tvDist (tailed π₀ S) (tailed π_s S) ≤
      2 * Real.exp (-(k₁ : ℝ)) / flaggedMass π_s S := by
  have h := tailed_tv_bound π_s π₀ S hπs.1 hπ0.1 hε hε'
  have hstep : 2 * tvDist π₀ π_s / flaggedMass π_s S ≤
      2 * Real.exp (-(k₁ : ℝ)) / flaggedMass π_s S := by
    apply div_le_div_of_nonneg_right _ hε.le
    linarith
  linarith

end Qatlib.Papers.QActiveLearn14.TailedBounds
