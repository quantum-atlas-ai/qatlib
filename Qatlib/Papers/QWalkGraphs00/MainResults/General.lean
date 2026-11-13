/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkGraphs00.MainResults.Core
import Qatlib.Papers.QWalkGraphs00.MainResults.Distribution
import Qatlib.Papers.QWalkGraphs00.MainResults.Times
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Norm

/-!
# Quantitative convergence to spectral limits

The spectral expression `limitingDist` retains pairs with equal eigenvalues. Bounds on geometric
averages give pointwise, ℓ¹, and total variation estimates for convergence to this expression,
with inverse eigenvalue separations controlling the error as in [AharonovEtAl2001Walks].

## Main statements

* `abs_avgNodeProb_sub_limitingDist_le`: bounds each vertex error by spectral terms.
* `sum_v_abs_avgNodeProb_sub_limitingDist_le`: sums the error using normalized eigenvectors.
* `lemma_4_3`: gives the total variation estimate in terms of squared coefficient norms.

## References

* [Aharonov et al., 2001][AharonovEtAl2001Walks]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.General

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Times
open Qatlib.Papers.QWalkGraphs00.MainResults.Distribution

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

/-- The ℓ¹ distance between two real functions on the vertex set. -/
def l1Dist (p q : V → ℝ) : ℝ := ∑ v, |p v - q v|

omit [DecidableEq V] in

/-- Total variation distance is bounded above by ℓ¹ distance. -/
theorem tvDistance_le_l1Dist (p q : V → ℝ) : tvDistance p q ≤ l1Dist p q := by
  unfold tvDistance l1Dist
  have h0 : (0 : ℝ) ≤ ∑ v, |p v - q v| :=
    Finset.sum_nonneg (fun v _ => abs_nonneg _)
  nlinarith

/-- The real spectral expression summing coefficient overlaps over pairs with equal eigenvalues. -/
def limitingDist (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (v : V) : ℝ :=
  (∑ i, ∑ j, if lam i = lam j then
      a i * star (a j) * (∑ c : Coin, φ i (c, v) * star (φ j (c, v)))
    else 0).re

omit [DecidableEq Coin] [DecidableEq V] in

/-- For a positive averaging length, the geometric average of one is one. -/
theorem geomAvg_one (T : ℕ) (hT : 0 < T) : geomAvg (1 : ℂ) T = 1 := by
  have hT0 : (T : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hT)
  simp only [geomAvg, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp

/-- The equal-eigenvalue formula for `limitingDist` can be written as a coin-coordinate triple
sum with an equality indicator. -/
theorem limitingDist_eq_spectral
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (v : V) :
    limitingDist φ lam a v
      = (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          a i * star (a j) * (φ i (c, v) * star (φ j (c, v))) *
            (if lam i = lam j then (1 : ℂ) else 0)).re := by
  unfold limitingDist
  congr 1
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hP : lam i = lam j
  · simp only [if_pos hP, mul_one]
    rw [Finset.mul_sum]
  · simp only [if_neg hP, mul_zero, Finset.sum_const, Finset.card_univ, nsmul_zero]

omit [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V] in

/-- For unit-modulus eigenvalues, their conjugate product has norm one and equals one exactly
when the eigenvalues coincide. -/
theorem norm_mul_star_eq_one_iff (lam : (Coin × V) → ℂ) (hlam : ∀ j, ‖lam j‖ = 1)
    (i j : Coin × V) :
    ‖lam i * star (lam j)‖ = 1 ∧ (lam i * star (lam j) = 1 ↔ lam i = lam j) := by
  have hnormSq : ∀ j, Complex.normSq (lam j) = 1 := by
    intro j
    rw [Complex.normSq_eq_norm_sq, hlam j]
    norm_num
  have hj : lam j * star (lam j) = 1 := by
    calc lam j * star (lam j) = (Complex.normSq (lam j) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj]
      _ = 1 := by rw [hnormSq j]; norm_num
  have hj' : star (lam j) * lam j = 1 := by
    calc star (lam j) * lam j = (Complex.normSq (lam j) : ℂ) := by
          rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
      _ = 1 := by rw [hnormSq j]; norm_num
  refine ⟨?_, ?_⟩
  · rw [norm_mul, hlam i, norm_star, hlam j]; norm_num
  · constructor
    · intro h
      calc lam i = lam i * (star (lam j) * lam j) := by rw [hj', mul_one]
        _ = (lam i * star (lam j)) * lam j := by ring
        _ = 1 * lam j := by rw [h]
        _ = lam j := one_mul _
    · intro h
      rw [h, hj]

/-- For a state expanded in eigenvectors with unit-modulus eigenvalues and `T > 0`, the vertex
error is bounded by weighted inverse eigenvalue gaps with factors `2 / T`, omitting
equal-eigenvalue pairs. -/
theorem abs_avgNodeProb_sub_limitingDist_le
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (T : ℕ) (hT : 0 < T) (v : V) :
    |avgNodeProb U ψ T v - limitingDist φ lam a v|
      ≤ ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
  set C : Coin → (Coin × V) → (Coin × V) → ℂ :=
    fun c i j => a i * star (a j) * (φ i (c, v) * star (φ j (c, v))) with hC
  set G : (Coin × V) → (Coin × V) → ℂ :=
    fun i j => geomAvg (lam i * star (lam j)) T with hG
  set K : (Coin × V) → (Coin × V) → ℂ :=
    fun i j => if lam i = lam j then (1 : ℂ) else 0 with hK
  have hpv : avgNodeProb U ψ T v = (∑ c, ∑ i, ∑ j, C c i j * G i j).re :=
    avgNodeProb_eq_spectral U φ lam a ψ hφ hψ T v
  have hqv : limitingDist φ lam a v = (∑ c, ∑ i, ∑ j, C c i j * K i j).re :=
    limitingDist_eq_spectral φ lam a v

  have hdiff : avgNodeProb U ψ T v - limitingDist φ lam a v
      = (∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          C c i j * (G i j - K i j)).re := by
    rw [hpv, hqv, ← Complex.sub_re]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

  have hGK : ∀ i j : Coin × V, G i j - K i j
      = if lam i = lam j then 0 else G i j := by
    intro i j
    by_cases hP : lam i = lam j
    · have hz : lam i * star (lam j) = 1 :=
        ((norm_mul_star_eq_one_iff lam hlam i j).2).mpr hP
      have hGij : G i j = 1 := by
        simp only [hG, hz, geomAvg_one T hT]
      have hKij : K i j = 1 := by simp only [hK, if_pos hP]
      rw [hGij, hKij, if_pos hP, sub_self]
    · have hKij : K i j = 0 := by simp only [hK, if_neg hP]
      rw [hKij, if_neg hP, sub_zero]

  have hterm : ∀ (c : Coin) (i j : Coin × V), ‖G i j - K i j‖
      ≤ if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖) := by
    intro c i j
    by_cases hP : lam i = lam j
    · rw [hGK i j, if_pos hP, norm_zero, if_pos hP]
    · have hne : lam i * star (lam j) ≠ 1 :=
        fun h => hP (((norm_mul_star_eq_one_iff lam hlam i j).2).mp h)
      have hzn : ‖lam i * star (lam j)‖ = 1 :=
        (norm_mul_star_eq_one_iff lam hlam i j).1
      have hb := norm_geomAvg_le (lam i * star (lam j)) hzn hne T
      have hz1 : ‖lam i * star (lam j) - 1‖ = ‖lam i - lam j‖ := by
        have hfac : lam i * star (lam j) - 1 = (lam i - lam j) * star (lam j) := by
          have hjl : lam j * star (lam j) = 1 := by
            calc lam j * star (lam j) = (Complex.normSq (lam j) : ℂ) := by
                  rw [Complex.star_def, Complex.mul_conj]
              _ = 1 := by
                  rw [Complex.normSq_eq_norm_sq, hlam j]; norm_num
          rw [← hjl, sub_mul]
        rw [hfac, norm_mul, norm_star, hlam j, mul_one]
      have hGij : G i j = geomAvg (lam i * star (lam j)) T := by simp only [hG]
      have hKij : K i j = 0 := by simp only [hK, if_neg hP]
      rw [hGij, hKij, sub_zero, if_neg hP]
      rw [hz1] at hb
      exact hb
  have hstep1 : |avgNodeProb U ψ T v - limitingDist φ lam a v|
      ≤ ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          ‖C c i j‖ * (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
    rw [hdiff]
    calc |(∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V, C c i j * (G i j - K i j)).re|
        ≤ ‖∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
              C c i j * (G i j - K i j)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ c : Coin, ‖∑ i : Coin × V, ∑ j : Coin × V,
              C c i j * (G i j - K i j)‖ := norm_sum_le _ _
      _ ≤ ∑ c : Coin, ∑ i : Coin × V, ‖∑ j : Coin × V,
              C c i j * (G i j - K i j)‖ := by
          apply Finset.sum_le_sum; intro c _
          exact norm_sum_le _ _
      _ ≤ ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
            ‖C c i j * (G i j - K i j)‖ := by
          apply Finset.sum_le_sum; intro c _
          apply Finset.sum_le_sum; intro i _
          exact norm_sum_le _ _
      _ ≤ ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
            ‖C c i j‖ * (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
          apply Finset.sum_le_sum; intro c _
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hterm c i j) (norm_nonneg _)

  have hnormC : ∀ (c : Coin) (i j : Coin × V),
      ‖C c i j‖ = ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) := by
    intro c i j
    simp only [hC, norm_mul, norm_star]
  simpa only [hnormC] using hstep1

/-- The finite sums over vertices, coin coordinates, and two spectral indices can be reordered
to put the spectral indices first. -/
private theorem sum_swap_vcij {α : Type*} [Fintype α]
    (G : V → Coin → α → α → ℝ) :
    ∑ v, ∑ c, ∑ i : α, ∑ j : α, G v c i j = ∑ i, ∑ j, ∑ v, ∑ c, G v c i j := by
  calc ∑ v, ∑ c, ∑ i : α, ∑ j : α, G v c i j
      = ∑ v, ∑ i : α, ∑ c, ∑ j : α, G v c i j := by
        apply Finset.sum_congr rfl; intro v _
        rw [Finset.sum_comm]
    _ = ∑ v, ∑ i : α, ∑ j : α, ∑ c, G v c i j := by
        apply Finset.sum_congr rfl; intro v _
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]
    _ = ∑ i : α, ∑ v, ∑ j : α, ∑ c, G v c i j := by
        rw [Finset.sum_comm]
    _ = ∑ i : α, ∑ j : α, ∑ v, ∑ c, G v c i j := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_comm]

/-- For normalized eigenvectors with unit-modulus eigenvalues and `T > 0`, the ℓ¹ error is at
most the sum over unequal-eigenvalue pairs of `2 * ‖a i‖ * ‖a j‖ / (T * ‖lam i - lam j‖)`. -/
theorem sum_v_abs_avgNodeProb_sub_limitingDist_le
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (hunit : ∀ i : Coin × V, ∑ c : Coin, ∑ v : V, Complex.normSq (φ i (c, v)) = 1)
    (T : ℕ) (hT : 0 < T) :
    l1Dist (fun v => avgNodeProb U ψ T v) (fun v => limitingDist φ lam a v)
      ≤ ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ * ‖a j‖ *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
  unfold l1Dist

  have hsum : ∑ v : V, |avgNodeProb U ψ T v - limitingDist φ lam a v|
      ≤ ∑ v : V, ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) :=
    Finset.sum_le_sum (fun v _ => abs_avgNodeProb_sub_limitingDist_le U φ lam a ψ hφ hlam hψ T hT v)
  refine hsum.trans ?_

  have hinner : ∀ i j : Coin × V,
      ∑ v : V, ∑ c : Coin, (‖φ i (c, v)‖ * ‖φ j (c, v)‖) ≤ 1 := by
    intro i j
    have hbound : ∀ v : V, ∀ c : Coin,
        ‖φ i (c, v)‖ * ‖φ j (c, v)‖
          ≤ (Complex.normSq (φ i (c, v)) + Complex.normSq (φ j (c, v))) / 2 := by
      intro v c
      have h2 := two_mul_le_add_sq (‖φ i (c, v)‖) (‖φ j (c, v)‖)
      have hns : Complex.normSq (φ i (c, v)) = ‖φ i (c, v)‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      have hns' : Complex.normSq (φ j (c, v)) = ‖φ j (c, v)‖ ^ 2 :=
        Complex.normSq_eq_norm_sq _
      rw [hns, hns']
      linarith
    have hsplit : ∑ v : V, ∑ c : Coin,
          (Complex.normSq (φ i (c, v)) + Complex.normSq (φ j (c, v))) / 2
        = (∑ v : V, ∑ c : Coin, Complex.normSq (φ i (c, v))) / 2
            + (∑ v : V, ∑ c : Coin, Complex.normSq (φ j (c, v))) / 2 := by
      have hpt : ∀ v c, (Complex.normSq (φ i (c, v)) + Complex.normSq (φ j (c, v))) / 2
          = Complex.normSq (φ i (c, v)) / 2 + Complex.normSq (φ j (c, v)) / 2 :=
        fun _ _ => by ring
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_div]
    calc ∑ v : V, ∑ c : Coin, (‖φ i (c, v)‖ * ‖φ j (c, v)‖)
        ≤ ∑ v : V, ∑ c : Coin,
            (Complex.normSq (φ i (c, v)) + Complex.normSq (φ j (c, v))) / 2 :=
          Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun c _ => hbound v c))
      _ = _ := hsplit
      _ = 1 := by
          rw [Finset.sum_comm (f := fun v (c : Coin) => Complex.normSq (φ i (c, v))),
            Finset.sum_comm (f := fun v (c : Coin) => Complex.normSq (φ j (c, v))),
            hunit i, hunit j]
          norm_num

  have hswap : ∑ v : V, ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
        ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      ≤ ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ * ‖a j‖ *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
    have hkey : ∑ v : V, ∑ c : Coin, ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
        = ∑ i : Coin × V, ∑ j : Coin × V,
            (‖a i‖ * ‖a j‖ *
              (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))) *
              ∑ v : V, ∑ c : Coin, (‖φ i (c, v)‖ * ‖φ j (c, v)‖) := by
      rw [sum_swap_vcij (fun (v : V) (c : Coin) (i j : Coin × V) =>
        ‖a i‖ * ‖a j‖ * (‖φ i (c, v)‖ * ‖φ j (c, v)‖) *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)))]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro c _
      ring
    rw [hkey]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hb0 : (0 : ℝ) ≤ (if lam i = lam j then (0 : ℝ)
        else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
      by_cases hP : lam i = lam j
      · rw [if_pos hP]
      · rw [if_neg hP]
        positivity
    have haa0 : (0 : ℝ) ≤ ‖a i‖ * ‖a j‖ := by positivity
    calc (‖a i‖ * ‖a j‖ *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))) *
            ∑ v : V, ∑ c : Coin, (‖φ i (c, v)‖ * ‖φ j (c, v)‖)
        ≤ (‖a i‖ * ‖a j‖ *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))) * 1 := by
          apply mul_le_mul_of_nonneg_left (hinner i j)
          exact mul_nonneg haa0 hb0
      _ = ‖a i‖ * ‖a j‖ *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by ring
  exact hswap

/-- For normalized eigenvectors with unit-modulus eigenvalues and `T > 0`, total variation error
is at most twice the sum of `normSq (a i) / (T * ‖lam i - lam j‖)` over unequal-eigenvalue
pairs. See [Aharonov et al., Lemma 4.3][AharonovEtAl2001Walks]. -/
theorem lemma_4_3
    (U : Matrix (Coin × V) (Coin × V) ℂ)
    (φ : (Coin × V) → ((Coin × V) → ℂ)) (lam : (Coin × V) → ℂ)
    (a : (Coin × V) → ℂ) (ψ : (Coin × V) → ℂ)
    (hφ : ∀ j, U *ᵥ φ j = lam j • φ j)
    (hlam : ∀ j, ‖lam j‖ = 1)
    (hψ : ψ = ∑ j, a j • φ j)
    (hunit : ∀ i : Coin × V, ∑ c : Coin, ∑ v : V, Complex.normSq (φ i (c, v)) = 1)
    (T : ℕ) (hT : 0 < T) :
    tvDistance (fun v => avgNodeProb U ψ T v) (fun v => limitingDist φ lam a v)
      ≤ 2 * ∑ i : Coin × V, ∑ j : Coin × V,
          if lam i = lam j then 0
          else Complex.normSq (a i) / ((T : ℝ) * ‖lam i - lam j‖) := by
  refine (tvDistance_le_l1Dist _ _).trans ?_
  have hmain := sum_v_abs_avgNodeProb_sub_limitingDist_le U φ lam a ψ hφ hlam hψ hunit T hT
  refine hmain.trans ?_

  have hsymm : ∀ i j : Coin × V,
      (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
        = (if lam j = lam i then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam j - lam i‖)) := by
    intro i j
    by_cases hP : lam i = lam j
    · rw [if_pos hP, if_pos hP.symm]
    · rw [if_neg hP, if_neg (fun h => hP h.symm), norm_sub_rev]
  have hpair : ∀ i j : Coin × V,
      ‖a i‖ * ‖a j‖ * (if lam i = lam j then (0 : ℝ)
        else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      = (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      - (‖a i‖ - ‖a j‖) ^ 2 / 2 *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
    intro i j; ring

  have hstep : ∑ i : Coin × V, ∑ j : Coin × V,
        ‖a i‖ * ‖a j‖ *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      ≤ ∑ i : Coin × V, ∑ j : Coin × V,
          (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hb0 : (0 : ℝ) ≤ (if lam i = lam j then (0 : ℝ)
        else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
      by_cases hP : lam i = lam j
      · rw [if_pos hP]
      · rw [if_neg hP]; positivity
    have hsq : 0 ≤ (‖a i‖ - ‖a j‖) ^ 2 / 2 * (if lam i = lam j then (0 : ℝ)
        else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
      apply mul_nonneg _ hb0
      positivity
    rw [hpair i j]
    linarith
  refine hstep.trans ?_

  have hcollapse : ∑ i : Coin × V, ∑ j : Coin × V,
        (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      = ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ ^ 2 *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
    have hsplit1 : ∑ i : Coin × V, ∑ j : Coin × V,
          (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
        = (∑ i : Coin × V, ∑ j : Coin × V,
              ‖a i‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
                else 2 / ((T : ℝ) * ‖lam i - lam j‖))) / 2
          + (∑ i : Coin × V, ∑ j : Coin × V,
              ‖a j‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
                else 2 / ((T : ℝ) * ‖lam i - lam j‖))) / 2 := by
      have hpt : ∀ i j, (‖a i‖ ^ 2 + ‖a j‖ ^ 2) / 2 *
            (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
          = ‖a i‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
                else 2 / ((T : ℝ) * ‖lam i - lam j‖)) / 2
            + ‖a j‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
                else 2 / ((T : ℝ) * ‖lam i - lam j‖)) / 2 := fun _ _ => by ring
      simp only [hpt, Finset.sum_add_distrib, Finset.sum_div]
    rw [hsplit1]

    have hswapij : ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a j‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
            else 2 / ((T : ℝ) * ‖lam i - lam j‖))
        = ∑ i : Coin × V, ∑ j : Coin × V,
          ‖a i‖ ^ 2 * (if lam i = lam j then (0 : ℝ)
            else 2 / ((T : ℝ) * ‖lam i - lam j‖)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [hsymm j i]
    rw [hswapij]
    ring
  rw [hcollapse]

  have hns : ∀ i : Coin × V, ‖a i‖ ^ 2 = Complex.normSq (a i) := by
    intro i
    rw [Complex.normSq_eq_norm_sq]
  have hfin : ∑ i : Coin × V, ∑ j : Coin × V,
        ‖a i‖ ^ 2 *
          (if lam i = lam j then (0 : ℝ) else 2 / ((T : ℝ) * ‖lam i - lam j‖))
      = 2 * ∑ i : Coin × V, ∑ j : Coin × V,
          if lam i = lam j then 0
          else Complex.normSq (a i) / ((T : ℝ) * ‖lam i - lam j‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    have hi := hns i
    by_cases hP : lam i = lam j
    · rw [if_pos hP, if_pos hP, mul_zero, mul_zero]
    · rw [if_neg hP, if_neg hP, hi]
      have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
      have hd : 0 < ‖lam i - lam j‖ := by
        apply norm_pos_iff.mpr
        exact sub_ne_zero.mpr hP
      field_simp
  rw [hfin]

end Qatlib.Papers.QWalkGraphs00.MainResults.General
