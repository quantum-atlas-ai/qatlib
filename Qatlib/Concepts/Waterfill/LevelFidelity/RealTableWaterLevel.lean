/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs

/-!
# Real water-fill identities and monotonicity

This module connects rational water-fill computations with their real-valued counterparts and
proves coordinate, mass, support, and increment estimates. The cross-multiplied inequalities
`realFidelity_anti` and `realFidelity_anti_lt` describe decreasing fidelity without dividing by
the mass, supporting the rejection-sampling water-fill analysis of [OzolsRoettelerRoland2013].

## Main statements

* `realFidelity_anti`: Prove the weak cross-multiplied fidelity inequality.
* `realFidelity_anti_lt`: Prove strictness when saturated and unsaturated coordinates coexist.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel

/-- Casting rational source, target, and level to the reals commutes with each coordinate of the
water fill. -/
theorem realFill_cast_fill {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) (i : Fin m) :
    realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ) i
      = (waterFill π σ γ i : ℝ) := by
  by_cases h : π i ≤ γ * σ i
  · have h' : (π i : ℝ) ≤ (γ : ℝ) * (σ i : ℝ) := by exact_mod_cast h
    have L : realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ) i = (π i : ℝ) :=
      min_eq_left h'
    have R : (waterFill π σ γ i : ℝ) = (π i : ℝ) := by
      rw [show waterFill π σ γ i = π i from min_eq_left h]
    rw [L, R]
  · have h' : (γ : ℝ) * (σ i : ℝ) ≤ (π i : ℝ) := by exact_mod_cast (le_of_not_ge h)
    have L : realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ) i
        = (γ : ℝ) * (σ i : ℝ) :=
      min_eq_right h'
    have R : (waterFill π σ γ i : ℝ) = ((γ * σ i : ℚ) : ℝ) := by
      rw [show waterFill π σ γ i = γ * σ i from min_eq_right (le_of_not_ge h)]
    rw [L, R, Rat.cast_mul]

/-- Casting the rational computed mass to the reals gives `realMass` of the cast data. -/
theorem realMass_cast {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    realMass (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ)
      = (computedMass π σ γ : ℝ) := by
  show (∑ i, realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ) i ^ 2) = _
  simp only [realFill_cast_fill]
  show (∑ i, ((waterFill π σ γ i : ℚ) : ℝ) ^ 2) = ((computedWaterEnergy π σ γ : ℚ) : ℝ)
  simp only [computedWaterEnergy]
  push_cast
  rfl

/-- Casting the rational computed overlap to the reals gives `realDot` of the cast data. -/
theorem realDot_cast {m : ℕ} (π σ : Fin m → ℚ) (γ : ℚ) :
    realDot (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ)
      = (computedDot π σ γ : ℝ) := by
  show (∑ i, (σ i : ℝ) *
      realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) (γ : ℝ) i) = _
  simp only [realFill_cast_fill]
  show (∑ i, (σ i : ℝ) * ((waterFill π σ γ i : ℚ) : ℝ)) = ((computedDot π σ γ : ℚ) : ℝ)
  simp only [computedDot]
  push_cast
  rfl
variable {m : ℕ} (π σ : Fin m → ℝ)

/-- Each filled coordinate is nonnegative for nonnegative source, target, and level. -/
theorem realFill_nonneg (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) (i : Fin m) : 0 ≤ realFill π σ γ i :=
  le_min (hπ i) (mul_nonneg hγ (hσ i))

/-- For a nonnegative target, each filled coordinate is monotone in the level. -/
theorem realFill_mono (hσ : ∀ i, 0 ≤ σ i) {a b : ℝ} (hab : a ≤ b) (i : Fin m) :
    realFill π σ a i ≤ realFill π σ b i :=
  min_le_min (le_refl _) (mul_le_mul_of_nonneg_right hab (hσ i))

/-- The mass of a real water fill is nonnegative at every level. -/
theorem realMass_nonneg (γ : ℝ) : 0 ≤ realMass π σ γ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For nonnegative source and target, the fill mass is monotone between nonnegative levels. -/
theorem realMass_mono (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (hγ : 0 ≤ a) (hab : a ≤ b) :
    realMass π σ a ≤ realMass π σ b := by
  have per : ∀ i, realFill π σ a i ^ 2 ≤ realFill π σ b i ^ 2 := by
    intro i
    have h1 : 0 ≤ realFill π σ a i := realFill_nonneg π σ hπ hσ hγ i
    have h2 : realFill π σ a i ≤ realFill π σ b i := realFill_mono π σ hσ hab i
    nlinarith [h1, h2]
  exact Finset.sum_le_sum fun i _ => per i

/-- At a nonnegative level, each filled coordinate lies between zero and its source coordinate,
and its ratio lies in `[0, 1]` and reconstructs the fill. -/
theorem realFill_support_range (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) (i : Fin m) :
    0 ≤ realFill π σ γ i ∧ realFill π σ γ i ≤ π i ∧
      0 ≤ realRatio π σ γ i ∧ realRatio π σ γ i ≤ 1 ∧
      π i * realRatio π σ γ i = realFill π σ γ i := by
  have hfill : 0 ≤ realFill π σ γ i ∧ realFill π σ γ i ≤ π i :=
    ⟨le_min (hπ i) (mul_nonneg hγ (hσ i)), min_le_left _ _⟩
  refine ⟨hfill.1, hfill.2, ?_, ?_, ?_⟩
  · unfold realRatio
    split_ifs with hi
    · exact le_rfl
    · exact div_nonneg hfill.1 (hπ i)
  · unfold realRatio
    split_ifs with hi
    · exact zero_le_one
    · exact (div_le_one (lt_of_le_of_ne (hπ i) (Ne.symm hi))).mpr hfill.2
  · unfold realRatio
    split_ifs with hi
    · rw [hi, zero_mul]
      have : realFill π σ γ i = min (π i) (γ * σ i) := rfl
      rw [this, hi, min_eq_left (mul_nonneg hγ (hσ i))]
    · field_simp

/-- A zero source coordinate gives a zero filled coordinate when the target and level are
nonnegative. -/
theorem realFill_source_zero (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) {i : Fin m} (hi : π i = 0) :
    realFill π σ γ i = 0 := by
  have : realFill π σ γ i = min (π i) (γ * σ i) := rfl
  rw [this, hi, min_eq_left (mul_nonneg hγ (hσ i))]

/-- For a nonnegative source, the fill at level zero vanishes coordinatewise. -/
theorem realFill_zero (hπ : ∀ i, 0 ≤ π i) (i : Fin m) : realFill π σ 0 i = 0 := by
  show min (π i) ((0 : ℝ) * σ i) = 0
  rw [zero_mul, min_eq_right (hπ i)]

/-- For a nonnegative source, both mass and overlap vanish at level zero. -/
theorem realMass_realDot_zero (hπ : ∀ i, 0 ≤ π i) :
    realMass π σ 0 = 0 ∧ realDot π σ 0 = 0 := by
  refine ⟨Finset.sum_eq_zero fun i _ => by rw [realFill_zero π σ hπ i]; ring,
    Finset.sum_eq_zero fun i _ => by rw [realFill_zero π σ hπ i]; ring⟩

/-- For nonnegative data and level, mass and overlap are nonnegative and the mass is at most the
level times the overlap. -/
theorem realMass_le_level_dot (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ realMass π σ γ ∧ 0 ≤ realDot π σ γ ∧ realMass π σ γ ≤ γ * realDot π σ γ := by
  have per : ∀ i, realFill π σ γ i ^ 2 ≤ γ * (σ i * realFill π σ γ i) := by
    intro i
    have hπ' : 0 ≤ π i := hπ i
    by_cases hs : π i ≤ γ * σ i
    · rw [show realFill π σ γ i = π i from min_eq_left hs]
      nlinarith [mul_nonneg hπ' (show 0 ≤ γ * σ i - π i by linarith)]
    · rw [show realFill π σ γ i = γ * σ i from min_eq_right (le_of_not_ge hs)]
      exact le_of_eq (by ring)
  have hmass : 0 ≤ realMass π σ γ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdot : 0 ≤ realDot π σ γ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hσ i) (realFill_nonneg π σ hπ hσ hγ i)
  refine ⟨hmass, hdot, ?_⟩
  calc realMass π σ γ ≤ ∑ i, γ * (σ i * realFill π σ γ i) :=
        Finset.sum_le_sum fun i _ => per i
    _ = γ * realDot π σ γ := by rw [realDot, Finset.mul_sum]

/-- The finite real Cauchy–Schwarz inequality bounds the square of a dot product by the product
of the squared norms. -/
private theorem sum_mul_sq_le (f g : Fin m → ℝ) :
    (∑ i, f i * g i) ^ 2 ≤ (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
  have h1 : |∑ i, f i * g i| ≤
      (‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖) := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, WithLp.ofLp_toLp,
      Pi.star_apply, star_trivial, mul_comm] using!
      abs_real_inner_le_norm (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))
        (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))
  have h2 : (‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
      ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖) ^ 2 =
      (∑ i, f i ^ 2) * (∑ i, g i ^ 2) := by
    have hf : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, f i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have hg : ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖ ^ 2 = ∑ i, g i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    nlinarith [norm_nonneg (WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m)),
      norm_nonneg (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))]
  rw [← h2]
  refine sq_le_sq.mpr ?_
  rw [abs_of_nonneg (show 0 ≤ ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin m))‖ *
    ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin m))‖ by positivity)]
  exact h1

/-- Multiplying a fill increment by the earlier filled coordinate is the same as multiplying it
by the earlier level times the target coordinate. -/
private theorem realFill_increment_mul (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (hab : a ≤ b) (i : Fin m) :
    realFill π σ a i * (realFill π σ b i - realFill π σ a i) =
      a * σ i * (realFill π σ b i - realFill π σ a i) := by
  by_cases hs : π i ≤ a * σ i
  · have hb : π i ≤ b * σ i :=
      hs.trans (mul_le_mul_of_nonneg_right hab (hσ i))
    rw [show realFill π σ a i = π i from min_eq_left hs,
      show realFill π σ b i = π i from min_eq_left hb]
    ring
  · rw [show realFill π σ a i = a * σ i from min_eq_right (le_of_not_ge hs)]

/-- The mass increment is twice the earlier level times the overlap increment plus the squared
norm of the fill increment. -/
private theorem realMass_increment (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    realMass π σ b = realMass π σ a + 2 * a * (realDot π σ b - realDot π σ a) +
      ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := by
  have per : ∀ i, (realFill π σ b i) ^ 2 - (realFill π σ a i) ^ 2 =
      2 * a * (σ i * realFill π σ b i - σ i * realFill π σ a i) +
        (realFill π σ b i - realFill π σ a i) ^ 2 := by
    intro i
    linear_combination 2 * realFill_increment_mul π σ hσ hab i
  have hsum : (∑ i, (realFill π σ b i) ^ 2) - (∑ i, (realFill π σ a i) ^ 2) =
      2 * a * ((∑ i, σ i * realFill π σ b i) -
        (∑ i, σ i * realFill π σ a i)) +
        (∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) := by
    have e1 : (∑ i, (realFill π σ b i) ^ 2) - (∑ i, (realFill π σ a i) ^ 2) =
        ∑ i, ((realFill π σ b i) ^ 2 - (realFill π σ a i) ^ 2) := by
      rw [Finset.sum_sub_distrib]
    have e2 : (∑ i, σ i * realFill π σ b i) - (∑ i, σ i * realFill π σ a i) =
        ∑ i, (σ i * realFill π σ b i - σ i * realFill π σ a i) := by
      rw [Finset.sum_sub_distrib]
    have e3 : 2 * a * ∑ i, (σ i * realFill π σ b i - σ i * realFill π σ a i) =
        ∑ i, (2 * a * (σ i * realFill π σ b i - σ i * realFill π σ a i)) := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => per i
  unfold realMass realDot
  linarith [hsum]

/-- For positive earlier level `a`, the squared overlap increment times `a` is bounded by the
earlier overlap times the squared norm of the fill increment. -/
private theorem realDot_increment_bound (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * (realDot π σ b - realDot π σ a) ^ 2 ≤
      realDot π σ a * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := by
  have key : ∀ i, a * (σ i * (realFill π σ b i - realFill π σ a i)) =
      realFill π σ a i * (realFill π σ b i - realFill π σ a i) := by
    intro i
    linear_combination (-(realFill_increment_mul π σ hσ hab i))
  have hinner : a * (realDot π σ b - realDot π σ a) =
      ∑ i, realFill π σ a i * (realFill π σ b i - realFill π σ a i) := by
    unfold realDot
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by linear_combination (key i)
  have hcs := sum_mul_sq_le (m := m) (fun i => realFill π σ a i)
    (fun i => realFill π σ b i - realFill π σ a i)
  have hf3 := (realMass_le_level_dot π σ hπ hσ ha.le).2.2
  have hS : (0 : ℝ) ≤ ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB : (∑ i, (realFill π σ a i) ^ 2) = realMass π σ a := rfl
  have c1 : (a * (realDot π σ b - realDot π σ a)) ^ 2 ≤
      (∑ i, (realFill π σ a i) ^ 2) *
        (∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) := by
    rw [hinner]
    exact hcs
  have c2 : (∑ i, (realFill π σ a i) ^ 2) *
      (∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) ≤
      (a * realDot π σ a) * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := by
    nlinarith [hf3, hS, hB]
  have c3 : a * (a * (realDot π σ b - realDot π σ a) ^ 2) ≤
      a * (realDot π σ a * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) := by
    nlinarith [c1, c2]
  nlinarith [c3, ha]

/-- For nonnegative data and ordered nonnegative levels, the squared overlaps and masses satisfy
the cross-multiplied inequality expressing decreasing fidelity. -/
theorem realFidelity_anti (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    realDot π σ b ^ 2 * realMass π σ a ≤ realDot π σ a ^ 2 * realMass π σ b := by
  rcases ha.eq_or_lt with ha0 | ha
  · subst ha0
    rw [(realMass_realDot_zero π σ hπ).1, mul_zero]
    exact mul_nonneg (sq_nonneg _) (realMass_nonneg π σ b)
  have hinc := realMass_increment π σ hσ ha.le hab
  have hf3 := (realMass_le_level_dot π σ hπ hσ ha.le).2.2
  have hcs := realDot_increment_bound π σ hπ hσ ha hab
  have hS : (0 : ℝ) ≤ ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hΔ : (0 : ℝ) ≤ realDot π σ b - realDot π σ a := by
    have hsum : (0 : ℝ) ≤ ∑ i, σ i * (realFill π σ b i - realFill π σ a i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hσ i)
        (sub_nonneg.mpr (realFill_mono π σ hσ hab i))
    have heq : ∑ i, σ i * (realFill π σ b i - realFill π σ a i) =
        realDot π σ b - realDot π σ a := by
      unfold realDot
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hA : (0 : ℝ) ≤ realDot π σ a :=
    (realMass_le_level_dot π σ hπ hσ ha.le).2.1
  have hB : (0 : ℝ) ≤ realMass π σ a :=
    (realMass_le_level_dot π σ hπ hσ ha.le).1
  have key1 : (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a ≤
      realDot π σ a ^ 2 * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := by
    have step1 : a * ((realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a) ≤
        (realDot π σ a * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) *
          realMass π σ a := by
      nlinarith [hcs, hB]
    have hAS : (0 : ℝ) ≤ realDot π σ a *
        ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := mul_nonneg hA hS
    have step2 : (realDot π σ a * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) *
        realMass π σ a ≤
        a * (realDot π σ a ^ 2 * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2) := by
      nlinarith [hf3, hAS]
    nlinarith [step1, step2, ha]
  have t1 : (0 : ℝ) ≤ 2 * realDot π σ a * (realDot π σ b - realDot π σ a) :=
    mul_nonneg (by linarith) hΔ
  have t2 : (0 : ℝ) ≤ a * realDot π σ a - realMass π σ a := by linarith
  have term1 : (0 : ℝ) ≤ 2 * realDot π σ a * (realDot π σ b - realDot π σ a) *
      (a * realDot π σ a - realMass π σ a) := mul_nonneg t1 t2
  have term2 : (0 : ℝ) ≤ realDot π σ a ^ 2 *
      ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 -
      (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a := by linarith
  have diff : realDot π σ a ^ 2 * realMass π σ b - realDot π σ b ^ 2 * realMass π σ a =
      2 * realDot π σ a * (realDot π σ b - realDot π σ a) *
        (a * realDot π σ a - realMass π σ a) +
      (realDot π σ a ^ 2 * ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 -
        (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a) := by
    have hBb : realMass π σ b = realMass π σ a +
        2 * a * (realDot π σ b - realDot π σ a) +
        ∑ i, (realFill π σ b i - realFill π σ a i) ^ 2 := hinc
    have hAb : realDot π σ b =
        realDot π σ a + (realDot π σ b - realDot π σ a) := by ring
    rw [hBb, hAb]
    ring
  linarith [diff, term1, term2]

/-- The cross-multiplied fidelity inequality is strict between increasing positive levels when
the earlier level has both a positive strictly saturated coordinate and a positive-target
unsaturated coordinate. -/
theorem realFidelity_anti_lt (hπ : ∀ i, 0 ≤ π i) (hσ : ∀ i, 0 ≤ σ i)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hlo : ∃ j, 0 < π j ∧ π j < a * σ j)
    (hhi : ∃ i, 0 < σ i ∧ a * σ i < π i) :
    realDot π σ b ^ 2 * realMass π σ a < realDot π σ a ^ 2 * realMass π σ b := by
  obtain ⟨j, hjπ, hjlt⟩ := hlo
  obtain ⟨i, hiσ, hilt⟩ := hhi
  have hab' : a ≤ b := le_of_lt hab
  have hdotpos : 0 < realDot π σ a := by
    unfold realDot
    have hterm : 0 < σ i * realFill π σ a i := by
      have hfi : realFill π σ a i = a * σ i := min_eq_right (le_of_lt hilt)
      have h1 : 0 < a * σ i := mul_pos ha hiσ
      rw [hfi]
      exact mul_pos hiσ h1
    have hle : σ i * realFill π σ a i ≤ ∑ x, σ x * realFill π σ a x :=
      Finset.single_le_sum
        (fun x _ => mul_nonneg (hσ x) (realFill_nonneg π σ hπ hσ ha.le x))
        (Finset.mem_univ i)
    exact lt_of_lt_of_le hterm hle
  have hdef : 0 < a * realDot π σ a - realMass π σ a := by
    unfold realDot realMass
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hsum : (∑ k, (a * (σ k * realFill π σ a k) - realFill π σ a k ^ 2)) =
        ∑ k, realFill π σ a k * (a * σ k - realFill π σ a k) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    have hterm : 0 < realFill π σ a j * (a * σ j - realFill π σ a j) := by
      have hfj : realFill π σ a j = π j := min_eq_left (le_of_lt hjlt)
      have h2 : 0 < a * σ j - π j := by linarith
      rw [hfj]
      exact mul_pos hjπ h2
    have hle : realFill π σ a j * (a * σ j - realFill π σ a j) ≤
        ∑ k, realFill π σ a k * (a * σ k - realFill π σ a k) :=
      Finset.single_le_sum (fun k _ => by
        apply mul_nonneg (realFill_nonneg π σ hπ hσ ha.le k)
        apply sub_nonneg.mpr
        show realFill π σ a k ≤ a * σ k
        exact min_le_right (π k) (a * σ k)) (Finset.mem_univ j)
    exact lt_of_lt_of_le hterm hle
  have hΔ : 0 < realDot π σ b - realDot π σ a := by
    unfold realDot
    rw [← Finset.sum_sub_distrib]
    have hterm : 0 < σ i * realFill π σ b i - σ i * realFill π σ a i := by
      rw [← mul_sub]
      have hfi : realFill π σ a i = a * σ i := min_eq_right (le_of_lt hilt)
      have hlt : realFill π σ a i < realFill π σ b i := by
        rw [hfi]
        have h2 : a * σ i < b * σ i := by
          have : (0:ℝ) < (b - a) * σ i := mul_pos (by linarith) hiσ
          linarith
        exact lt_min hilt h2
      exact mul_pos hiσ (sub_pos.mpr hlt)
    have hnonneg : ∀ k, 0 ≤ σ k * realFill π σ b k - σ k * realFill π σ a k := by
      intro k
      rw [← mul_sub]
      exact mul_nonneg (hσ k) (sub_nonneg.mpr (realFill_mono π σ hσ hab' k))
    have hle : σ i * realFill π σ b i - σ i * realFill π σ a i ≤
        ∑ k, (σ k * realFill π σ b k - σ k * realFill π σ a k) :=
      Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
    exact lt_of_lt_of_le hterm hle
  have hinc := realMass_increment π σ hσ ha.le hab'
  have hcs := realDot_increment_bound π σ hπ hσ ha hab'
  have hS : (0 : ℝ) ≤ ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hA : (0 : ℝ) ≤ realDot π σ a := le_of_lt hdotpos
  have hB : (0 : ℝ) ≤ realMass π σ a :=
    (realMass_le_level_dot π σ hπ hσ ha.le).1
  have hf3 := (realMass_le_level_dot π σ hπ hσ ha.le).2.2
  have key1 : (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a ≤
      realDot π σ a ^ 2 * ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 := by
    have step1 : a * ((realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a) ≤
        (realDot π σ a * ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2) *
          realMass π σ a := by
      nlinarith [hcs, hB]
    have hAS : (0 : ℝ) ≤ realDot π σ a *
        ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 := mul_nonneg hA hS
    have step2 : (realDot π σ a * ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2) *
        realMass π σ a ≤
        a * (realDot π σ a ^ 2 * ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2) := by
      nlinarith [hf3, hAS]
    nlinarith [step1, step2, ha]
  have term2 : (0 : ℝ) ≤ realDot π σ a ^ 2 *
      ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 -
      (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a := by linarith
  have term1 : (0 : ℝ) < 2 * realDot π σ a * (realDot π σ b - realDot π σ a) *
      (a * realDot π σ a - realMass π σ a) := by
    have h1 : (0:ℝ) < 2 * realDot π σ a * (realDot π σ b - realDot π σ a) :=
      mul_pos (mul_pos (by norm_num) hdotpos) hΔ
    exact mul_pos h1 hdef
  have diff : realDot π σ a ^ 2 * realMass π σ b - realDot π σ b ^ 2 * realMass π σ a =
      2 * realDot π σ a * (realDot π σ b - realDot π σ a) *
        (a * realDot π σ a - realMass π σ a) +
      (realDot π σ a ^ 2 * ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 -
        (realDot π σ b - realDot π σ a) ^ 2 * realMass π σ a) := by
    have hBb : realMass π σ b = realMass π σ a +
        2 * a * (realDot π σ b - realDot π σ a) +
        ∑ k, (realFill π σ b k - realFill π σ a k) ^ 2 := hinc
    have hAb : realDot π σ b =
        realDot π σ a + (realDot π σ b - realDot π σ a) := by ring
    rw [hBb, hAb]
    ring
  linarith [diff, term1, term2]
end Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
