/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Lemma6Tigh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

open scoped BigOperators

noncomputable def QuerySuccess {C Y : Type*} [Fintype C] [DecidableEq C]
    [DecidableEq Y] (label : C → Option Y) (ψ : EuclideanSpace ℂ C) (y : Y) : ℝ :=
  ‖QueryProjection (Finset.univ.filter (fun c => label c = some y)) ψ‖ ^ 2

theorem average_failure_projection_bound {C Y : Type*}
    [Fintype C] [DecidableEq C] [Fintype Y]
    (A : Y → Finset C) (states : Y → EuclideanSpace ℂ C)
    (hnorm : ∀ y, ‖states y‖ = 1)
    (hsuccess : (Fintype.card Y : ℝ) / 2 ≤ ∑ y : Y, ‖QueryProjection (A y) (states y)‖ ^ 2) :
    (∑ y : Y, ‖QueryProjection (A y)ᶜ (states y)‖) ≤ Real.sqrt 2 / 2 * Fintype.card Y := by
  let b (y : Y) := ‖QueryProjection (A y)ᶜ (states y)‖
  have hsplit (y : Y) : ‖QueryProjection (A y) (states y)‖ ^ 2 + b y ^ 2 = 1 := by
    have h := queryProjection_complement_mass (A y) (states y)
    simpa only [hnorm, one_pow] using h
  have hmass : (∑ y : Y, b y ^ 2) ≤ (Fintype.card Y : ℝ) / 2 := by
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun y _ => hsplit y)
    rw [Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
    linarith
  have hnonneg : 0 ≤ ∑ y : Y, b y := Finset.sum_nonneg (fun y _ => norm_nonneg _)
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := b)
  simp only [Finset.card_univ] at hc
  have hm := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (Fintype.card Y) : (0 : ℝ) ≤ _)
  change (∑ y : Y, b y) ≤ _
  apply (sq_le_sq₀ hnonneg (by positivity)).mp
  calc
    (∑ y : Y, b y) ^ 2 ≤ (Fintype.card Y : ℝ) * ((Fintype.card Y : ℝ) / 2) := hc.trans hm
    _ = (Real.sqrt 2 / 2 * (Fintype.card Y : ℝ)) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem average_failure_amplitude_bound {C Y : Type*}
    [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (label : C → Option Y) (states : Y → EuclideanSpace ℂ C)
    (hnorm : ∀ y, ‖states y‖ = 1)
    (hsuccess : (Fintype.card Y : ℝ) / 2 ≤ ∑ y : Y, QuerySuccess label (states y) y) :
    (∑ y : Y, ‖QueryProjection (Finset.univ.filter (fun c => label c = some y))ᶜ
      (states y)‖) ≤ Real.sqrt 2 / 2 * Fintype.card Y :=
  average_failure_projection_bound _ states hnorm hsuccess

theorem fixed_query_quadratic_bound {C Y : Type*}
    [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : Y → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1) (r : ℕ)
    (hagree : ∀ y n, n < r → ∀ c, f n c ≠ some y →
      V y n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1))
    (hsuccess : (Fintype.card Y : ℝ) / 2 ≤
      ∑ y : Y, QuerySuccess (f r) (UnitaryEvolution (V y) ψ r) y) :
    (1 - Real.sqrt 2 / 2) * Fintype.card Y - Real.sqrt (Fintype.card Y) ≤
      2 * (r : ℝ) ^ 2 := by
  have hhybrid := (lemma6 U V f ψ hψ r hagree).2.2
  have hfailure := average_failure_amplitude_bound (f r)
    (fun y => UnitaryEvolution (V y) ψ r)
    (fun y => by rw [unitaryEvolution_norm, hψ]) hsuccess
  nlinarith

theorem zero_query_card_le_two {C Y : Type*}
    [Fintype C] [DecidableEq C] [Fintype Y] [DecidableEq Y]
    (label : C → Option Y) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1)
    (hsuccess : (Fintype.card Y : ℝ) / 2 ≤ ∑ y : Y, QuerySuccess label ψ y) :
    Fintype.card Y ≤ 2 := by
  have hm := query_fiber_mass label ψ
  rw [hψ, one_pow] at hm
  change (∑ y : Y, QuerySuccess label ψ y) ≤ 1 at hm
  have : (Fintype.card Y : ℝ) ≤ 2 := by linarith
  exact_mod_cast this

theorem sine_eighth_bounds :
    (3 / 8 : ℝ) < Real.sin (Real.pi / 8) ∧
    Real.sin (Real.pi / 8) < 1 / 2 ∧
    Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
  rw [Real.sin_pi_div_eight]
  have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hlo : 1 < Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 < (23 / 16 : ℝ) := by nlinarith
  have hn : 0 ≤ 2 - Real.sqrt 2 := by linarith
  have hs := Real.sq_sqrt hn
  have hsp := Real.sqrt_nonneg (2 - Real.sqrt 2)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem floor_bound_of_quadratic (N r : ℕ)
    (hquad : (1 - Real.sqrt 2 / 2) * (N : ℝ) - Real.sqrt N ≤ 2 * (r : ℝ) ^ 2)
    (hzero : r = 0 → N ≤ 2) :
    ⌊Real.sin (Real.pi / 8) * Real.sqrt N⌋ ≤ (r : ℤ) := by
  obtain ⟨haLow, haHigh, haSq⟩ := sine_eighth_bounds
  have haPos : 0 < Real.sin (Real.pi / 8) := by linarith
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hs2 := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ _)
  apply Int.floor_le_iff.mpr
  simp only [Int.cast_natCast]
  by_cases hr : r = 0
  · have hN := hzero hr
    have hNr : (N : ℝ) ≤ 2 := by exact_mod_cast hN
    have hs : Real.sqrt (N : ℝ) < 2 := by nlinarith
    have hprod := mul_lt_mul_of_pos_left hs haPos
    simp only [hr, Nat.cast_zero, zero_add]
    nlinarith
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    by_cases hN : N < 16
    · have hNr : (N : ℝ) < 16 := by exact_mod_cast hN
      have hs : Real.sqrt (N : ℝ) < 4 := by nlinarith
      have hprod := mul_lt_mul_of_pos_left hs haPos
      nlinarith
    · have hNr : (16 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_not_gt hN)
      have hs : (4 : ℝ) ≤ Real.sqrt N := by nlinarith
      have hmul := mul_lt_mul_of_pos_right haLow (by linarith : 0 < Real.sqrt (N : ℝ))
      have hk : (Real.sin (Real.pi / 8) * Real.sqrt N) ^ 2 =
          (2 - Real.sqrt 2) / 4 * N := by rw [mul_pow, haSq, hs2]
      have hquad' : 2 * (Real.sin (Real.pi / 8) * Real.sqrt N) ^ 2 - Real.sqrt N ≤
          2 * (r : ℝ) ^ 2 := by nlinarith
      by_contra h
      have hge : (r : ℝ) + 1 ≤ Real.sin (Real.pi / 8) * Real.sqrt N := le_of_not_gt h
      have hsq : (r : ℝ) ^ 2 ≤ (Real.sin (Real.pi / 8) * Real.sqrt N - 1) ^ 2 :=
        (sq_le_sq₀ (Nat.cast_nonneg r) (by linarith)).2 (by linarith)
      nlinarith

end Qatlib.Concepts.SearchStopping.QueryLowerBound
