/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Ridge minimizers with explicit paper premises

Fixed arXiv:2110.13086v2 (19 Jul 2022), Section 5, pp. 25–26.

Theorem 5.1 compares losses only on the unit Euclidean ball. Theorem 5.2 assumes
positive dimension, excluding the totalized-division counterexample at dimension zero.
Theorem 5.3 bounds sign errors using the squared Euclidean distance to the reference.
The norms and inner product are explicit Euclidean sums from SourceModel.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.RidgeLoss
open Qatlib.Papers.QRegression21.MainResults

open Qatlib.Papers.QRegression21.MainResults Qatlib.Papers.QRegression21.MainResults

variable {d : ℕ}

/-- The reference vector has unit squared Euclidean norm in positive dimension. -/
private theorem star_norm (W : Finset (Fin d)) (hd : 0 < d) :
    l2NormSq (thetaStarRidge d W) = 1 := by
  classical
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs := Real.sq_sqrt hdpos.le
  have hstar (j : Fin d) : thetaStarRidge d W j ^ 2 = 1 / (d : ℝ) := by
    unfold thetaStarRidge
    split_ifs <;> field_simp <;> nlinarith
  unfold l2NormSq
  simp_rw [hstar]
  simp [Nat.ne_of_gt hd]

/-- Bounds on the reciprocal floor used in the Ridge parameter regime. -/
private theorem param_bounds (ε p : ℝ) (he : 0 < ε) (he' : ε < 1 / 10000)
    (hp : p = 1 / (Nat.floor (1 / ε) : ℝ)) :
    ε ≤ p ∧ p ≤ 2 * ε ∧ 0 < p ∧ p < 1 / 5000 := by
  have hrec : 0 ≤ 1 / ε := by positivity
  have hf := Nat.floor_le hrec
  have hf' := Nat.lt_floor_add_one (1 / ε)
  have heinv : ε * (1 / ε) = 1 := by field_simp
  have hfpos : (0 : ℝ) < (Nat.floor (1 / ε) : ℝ) := by
    by_contra h
    have hzero : (Nat.floor (1 / ε) : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hzero] at hf'
    have := (div_lt_iff₀ he).mp hf'
    linarith
  have hprod : p * (Nat.floor (1 / ε) : ℝ) = 1 := by rw [hp]; field_simp
  have hppos : 0 < p := by rw [hp]; positivity
  have hlow : ε ≤ p := by
    have hh := mul_le_mul_of_nonneg_left hf he.le
    have hh' := mul_le_mul_of_nonneg_left hh hppos.le
    nlinarith
  have hupp : p ≤ 2 * ε := by
    have hh := mul_lt_mul_of_pos_left hf' he
    have hh' := mul_lt_mul_of_pos_left hh hppos
    nlinarith
  exact ⟨hlow, hupp, hppos, by linarith⟩

/-- Theorem 5.1 on the feasible unit Euclidean ball, as in the fixed source. -/
theorem theorem_5_1 (W : Finset (Fin d))
    (ε p : ℝ) (hε0 : 1000 / (d : ℝ) < ε) (hε1 : ε < 1 / 10000)
    (hp : p = 1 / (Nat.floor (1 / ε) : ℝ)) :
    l2Ball (thetaStarRidge d W) ∧
      ∀ θ : Fin d → ℝ, l2Ball θ → ridgeLoss d p W (thetaStarRidge d W) ≤ ridgeLoss d p W θ := by
  classical
  by_cases hd : d = 0
  · subst d
    simp [l2Ball, l2NormSq, ridgeLoss, dot]
  · have hd' := Nat.pos_of_ne_zero hd
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd'
    have he : 0 < ε := lt_trans (by positivity : 0 < 1000 / (d : ℝ)) hε0
    obtain ⟨hep, hpe, hp0, hp1⟩ := param_bounds ε p he hε1 hp
    have hn := star_norm W hd'
    have ha0 : 0 ≤ (1 - 4 * p ^ 2) / (d : ℝ) := by
      apply div_nonneg _ hdpos.le
      simp only [div_eq_mul_inv] at *
      nlinarith
    have ha1 : (1 - 4 * p ^ 2) / (d : ℝ) ≤ ε / 1000 := by
      apply (div_le_iff₀ hdpos).mpr
      have hh := (div_lt_iff₀ hdpos).mp hε0
      nlinarith [sq_nonneg p]
    constructor
    · exact hn.le
    · intro θ hθ
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ (thetaStarRidge d W)
      change (dot θ (thetaStarRidge d W)) ^ 2 ≤
        l2NormSq θ * l2NormSq (thetaStarRidge d W) at hcs
      rw [hn, mul_one] at hcs
      have hu : dot θ (thetaStarRidge d W) ≤ 1 := by
        unfold l2Ball at hθ
        nlinarith [sq_nonneg (dot θ (thetaStarRidge d W) - 1)]
      have hdots : dot (thetaStarRidge d W) (thetaStarRidge d W) = 1 := by
        simpa [dot, l2NormSq, pow_two] using hn
      unfold ridgeLoss
      rw [hn, hdots]
      have hh := mul_nonneg ha0 (sub_nonneg.mpr hcs)
      have hh' := mul_nonneg (sub_nonneg.mpr hu)
        (show 0 ≤ 4 * p - ((1 - 4 * p ^ 2) / (d : ℝ) + 4 * p ^ 2) *
            (dot θ (thetaStarRidge d W) + 1) by
          have hcoef : 0 ≤ (1 - 4 * p ^ 2) / (d : ℝ) + 4 * p ^ 2 := by positivity
          have hx := mul_le_mul_of_nonneg_left (show dot θ (thetaStarRidge d W) + 1 ≤ 2 by linarith) hcoef
          nlinarith)
      simp only [div_eq_mul_inv] at *
      nlinarith


/-- Theorem 5.2 with the implicit positive dimension made explicit. -/
theorem theorem_5_2 (W : Finset (Fin d)) (hd : 0 < d)
    (ε p : ℝ) (hε0 : 1000 / (d : ℝ) < ε) (hε1 : ε < 1 / 10000)
    (hp : p = 1 / (Nat.floor (1 / ε) : ℝ))
    (θ : Fin d → ℝ)
    (hmin : IsEpsilonMinimizer (ridgeLoss d p W) {θ | l2Ball θ} (ε / 1000) θ) :
    dot θ (thetaStarRidge d W) ≥ 0.999 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have he : 0 < ε := lt_trans (by positivity : 0 < 1000 / (d : ℝ)) hε0
  obtain ⟨hep, hpe, hp0, hp1⟩ := param_bounds ε p he hε1 hp
  have hn := star_norm W hd
  have hdots : dot (thetaStarRidge d W) (thetaStarRidge d W) = 1 := by
    simpa [dot, l2NormSq, pow_two] using hn
  have hm := hmin.2 (thetaStarRidge d W) hn.le
  unfold ridgeLoss at hm
  rw [hn, hdots] at hm
  have ha0 : 0 ≤ (1 - 4 * p ^ 2) / (d : ℝ) := by
    apply div_nonneg _ hdpos.le
    nlinarith
  have ha1 : (1 - 4 * p ^ 2) / (d : ℝ) ≤ ε / 1000 := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (div_lt_iff₀ hdpos).mp hε0
    nlinarith [sq_nonneg p]
  have hnn : 0 ≤ l2NormSq θ := Finset.sum_nonneg (fun j _ => sq_nonneg (θ j))
  have hh := mul_nonneg hnn ha0
  have hsq : (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2 ≤
      (2 * p - 1) ^ 2 + ε / 500 := by
    simp only [div_eq_mul_inv] at *
    nlinarith
  by_contra hu
  have hu' : dot θ (thetaStarRidge d W) < 999 / 1000 := by
    norm_num at hu ⊢
    exact hu
  have hx : 1 - 2 * p * (999 / 1000) ≤
      1 - 2 * p * dot θ (thetaStarRidge d W) := by nlinarith
  have hx0 : 0 ≤ 1 - 2 * p * (999 / 1000) := by linarith
  have hs := mul_nonneg (sub_nonneg.mpr hx)
    (show 0 ≤ (1 - 2 * p * dot θ (thetaStarRidge d W)) +
        (1 - 2 * p * (999 / 1000)) by linarith)
  nlinarith

/-- Theorem 5.3: near-unit alignment bounds the number of incorrect coordinate signs. -/
theorem theorem_5_3 (W : Finset (Fin d))
    (θ : Fin d → ℝ) (hθ : l2Ball θ)
    (h : dot θ (thetaStarRidge d W) ≥ 1 - 0.001) :
    (((Finset.univ.filter (fun j => θ j * thetaStarRidge d W j ≤ 0)).card : ℝ) ≤
      (d : ℝ) / 500) := by
  classical
  by_cases hd : d = 0
  · subst d
    simp
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hn := star_norm W (Nat.pos_of_ne_zero hd)
  have hstar (j : Fin d) : thetaStarRidge d W j ^ 2 = 1 / (d : ℝ) := by
    have hs := Real.sq_sqrt hdpos.le
    unfold thetaStarRidge
    split_ifs <;> field_simp <;> nlinarith
  let B := Finset.univ.filter (fun j => θ j * thetaStarRidge d W j ≤ 0)
  have hpoint (j : Fin d) (hj : j ∈ B) :
      1 / (d : ℝ) ≤ (θ j - thetaStarRidge d W j) ^ 2 := by
    have hb := (Finset.mem_filter.mp hj).2
    nlinarith [hstar j, sq_nonneg (θ j)]
  have hsum : (B.card : ℝ) / d ≤ ∑ j, (θ j - thetaStarRidge d W j) ^ 2 := by
    calc
      (B.card : ℝ) / d = ∑ _j ∈ B, 1 / (d : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ B, (θ j - thetaStarRidge d W j) ^ 2 :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ j, (θ j - thetaStarRidge d W j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => sq_nonneg _)
  have hexpand : (∑ j, (θ j - thetaStarRidge d W j) ^ 2) =
      l2NormSq θ + l2NormSq (thetaStarRidge d W) - 2 * dot θ (thetaStarRidge d W) := by
    unfold l2NormSq dot
    calc
      _ = ∑ j, (θ j ^ 2 + thetaStarRidge d W j ^ 2 -
          2 * (θ j * thetaStarRidge d W j)) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  have hupper : (B.card : ℝ) / d ≤ 1 / 500 := by
    rw [hexpand, hn] at hsum
    unfold l2Ball at hθ
    nlinarith
  have hb := (div_le_iff₀ hdpos).mp hupper
  change (B.card : ℝ) ≤ (d : ℝ) / 500
  nlinarith


end Qatlib.Papers.QRegression21.MainResults.RidgeLoss
