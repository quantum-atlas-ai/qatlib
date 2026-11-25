/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegression21.MainResults.RidgeLoss.SourceRidgeLoss
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Uniqueness of the Ridge minimizer

Theorem 5.1 of the fixed source says that `θ*_j = (-1)^{[j ∈ W]} / √d` minimizes the Ridge loss on
the unit Euclidean ball and speaks of "the minimizer". The public statement
`Qatlib.Papers.QRegression21.MainResults.RidgeLoss.theorem_5_1` records only the minimality half.
This module adds the uniqueness half: in the paper's parameter regime
`1000 / d < ε < 1/10000` and `p = 1 / ⌊1/ε⌋`, every feasible `θ` with the same loss as `θ*` is
equal to `θ*`.

With `c = ‖θ‖²`, `u = ⟨θ, θ*⟩` and `a = (1 - 4p²)/d`, the loss is `a c + (2 p u - 1)²`. Equality
with the loss `a + (2p - 1)²` of `θ*` gives `(2 p u - 1)² - (2 p - 1)² = a (1 - c)`. The left side
is `4 p (1 - u) (1 - p (1 + u))`: at least `p (1 - c)`, because Cauchy--Schwarz forces
`1 - c ≤ 2 (1 - u)` and `p ≤ 1/4`. Hence `p ≤ a ≤ 1/d`, contradicting `p > 1000/d` unless
`c = 1`; then the equality of the losses forces `u = 1`, and `‖θ - θ*‖` vanishes.

Boundary: the paper's parameter regime enters only through `0 < p < 1/4` and `1000/d < p`. Nothing
is claimed for other parameter ranges, and the minimality half remains in the public library.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QRegression21.MainResults.RidgeUniqueness

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.QRegression21.MainResults

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

/-- The arithmetic core: a feasible point whose Ridge loss equals that of `θ*` has squared norm
one. The proof compares `(2 p u - 1)²` with `(2 p - 1)²` using `u² ≤ c` and `p ≤ 1/4`. -/
private theorem norm_sq_eq_one_of_loss_eq (hd : 0 < d) {p c u : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1 / 4) (hpbig : 1000 / (d : ℝ) < p)
    (hc1 : c ≤ 1) (hu : u ^ 2 ≤ c) (hu1 : u ≤ 1)
    (heq : (2 * p * u - 1) ^ 2 - (2 * p - 1) ^ 2 = ((1 - 4 * p ^ 2) / (d : ℝ)) * (1 - c)) :
    c = 1 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  by_contra hcne
  have hclt : c < 1 := lt_of_le_of_ne hc1 hcne
  have h1c : 0 < 1 - c := by linarith
  have hfac : (2 * p * u - 1) ^ 2 - (2 * p - 1) ^ 2
      = 4 * p * (1 - u) * (1 - p * (1 + u)) := by ring
  have heq' : 4 * p * (1 - u) * (1 - p * (1 + u)) = ((1 - 4 * p ^ 2) / (d : ℝ)) * (1 - c) := by
    rw [← hfac]
    exact heq
  have hA : 0 ≤ 1 - u := by linarith
  have hB : (1 / 2 : ℝ) ≤ 1 - p * (1 + u) := by nlinarith
  have hAC : (1 - c) / 2 ≤ 1 - u := by nlinarith
  have hstep1 : p * (1 - c) ≤ 2 * p * (1 - u) := by nlinarith
  have hstep2 : 2 * p * (1 - u) ≤ 4 * p * (1 - u) * (1 - p * (1 + u)) := by
    have hnonneg : 0 ≤ 2 * p * (1 - u) * (2 * (1 - p * (1 + u)) - 1) :=
      mul_nonneg (mul_nonneg (by linarith) hA) (by linarith)
    nlinarith [hnonneg]
  have hmain : p * (1 - c) ≤ ((1 - 4 * p ^ 2) / (d : ℝ)) * (1 - c) := by
    rw [← heq']
    linarith
  have hpA : p ≤ (1 - 4 * p ^ 2) / (d : ℝ) := by
    rcases lt_trichotomy p ((1 - 4 * p ^ 2) / (d : ℝ)) with h | h | h
    · exact h.le
    · exact h.le
    · exfalso
      have hm := mul_lt_mul_of_pos_right h h1c
      nlinarith [hmain, hm]
  have hAub : (1 - 4 * p ^ 2) / (d : ℝ) ≤ 1 / (d : ℝ) := by
    apply div_le_div_of_nonneg_right _ hdpos.le
    nlinarith [sq_nonneg p]
  have hpd : p ≤ 1 / (d : ℝ) := le_trans hpA hAub
  have hpd1 : p * (d : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hpd hdpos.le
    have h1 : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := by field_simp
    rwa [h1] at h
  have hbig : 1000 < p * (d : ℝ) := by
    have h := mul_lt_mul_of_pos_right hpbig hdpos
    have h1 : 1000 / (d : ℝ) * (d : ℝ) = 1000 := by field_simp
    rwa [h1] at h
  linarith

/-- Theorem 5.1, uniqueness half: in the paper's parameter regime a feasible point with the loss
of `θ*` is `θ*` itself. -/
theorem theorem_5_1_unique (W : Finset (Fin d)) (hd : 0 < d) (ε p : ℝ)
    (hε0 : 1000 / (d : ℝ) < ε) (hε1 : ε < 1 / 10000)
    (hp : p = 1 / (Nat.floor (1 / ε) : ℝ)) :
    ∀ θ : Fin d → ℝ, l2Ball θ → ridgeLoss d p W θ = ridgeLoss d p W (thetaStarRidge d W) →
      θ = thetaStarRidge d W := by
  classical
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have he : 0 < ε := lt_trans (by positivity) hε0
  obtain ⟨hep, -, hp0, hp1⟩ := param_bounds ε p he hε1 hp
  have hpbig : 1000 / (d : ℝ) < p := lt_of_lt_of_le hε0 hep
  have hsqpos : 0 < 1 - 4 * p ^ 2 := by nlinarith
  have hstar : l2NormSq (thetaStarRidge d W) = 1 := star_norm W hd
  have hdots : dot (thetaStarRidge d W) (thetaStarRidge d W) = 1 := by
    simpa [dot, l2NormSq, pow_two] using hstar
  intro θ hθ hEq
  have hc1 : l2NormSq θ ≤ 1 := hθ
  have hcs : (dot θ (thetaStarRidge d W)) ^ 2 ≤ l2NormSq θ := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ θ (thetaStarRidge d W)
    change (dot θ (thetaStarRidge d W)) ^ 2 ≤ l2NormSq θ * l2NormSq (thetaStarRidge d W) at h
    rw [hstar, mul_one] at h
    exact h
  have hu1 : dot θ (thetaStarRidge d W) ≤ 1 := by
    nlinarith [hcs, hc1, sq_nonneg (dot θ (thetaStarRidge d W) - 1)]
  have hexp : ridgeLoss d p W θ
      = l2NormSq θ * (1 - 4 * p ^ 2) / (d : ℝ)
        + (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2 := rfl
  have hexp' : ridgeLoss d p W (thetaStarRidge d W)
      = (1 - 4 * p ^ 2) / (d : ℝ) + (2 * p - 1) ^ 2 := by
    unfold ridgeLoss
    rw [hstar, hdots, mul_one, one_mul]
  have hsplit : l2NormSq θ * (1 - 4 * p ^ 2) / (d : ℝ)
      + (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2
      = (1 - 4 * p ^ 2) / (d : ℝ) + (2 * p - 1) ^ 2 := by
    rw [← hexp, ← hexp']
    exact hEq
  have hXY : (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2 - (2 * p - 1) ^ 2
      = ((1 - 4 * p ^ 2) / (d : ℝ)) * (1 - l2NormSq θ) := by
    have h := hsplit
    rw [show l2NormSq θ * (1 - 4 * p ^ 2) / (d : ℝ)
        = ((1 - 4 * p ^ 2) / (d : ℝ)) * l2NormSq θ from by ring] at h
    nlinarith [h]
  have hceq : l2NormSq θ = 1 :=
    norm_sq_eq_one_of_loss_eq hd hp0 (by linarith) hpbig hc1 hcs hu1 hXY
  have hXeq : (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2 = (2 * p - 1) ^ 2 := by
    have h := hsplit
    rw [hceq, one_mul] at h
    linarith
  have hueq : dot θ (thetaStarRidge d W) = 1 := by
    have hfac : (2 * p * (dot θ (thetaStarRidge d W) - 1))
        * (2 * p * (dot θ (thetaStarRidge d W) + 1) - 2) = 0 := by
      have h : (2 * p * (dot θ (thetaStarRidge d W) - 1))
          * (2 * p * (dot θ (thetaStarRidge d W) + 1) - 2)
          = (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2 - (2 * p - 1) ^ 2 := by ring
      rw [h, hXeq]
      ring
    rcases mul_eq_zero.mp hfac with h1 | h2
    · nlinarith
    · exfalso
      have hup : 2 * p * dot θ (thetaStarRidge d W) ≤ 2 * p := by nlinarith
      nlinarith [hup]
  have hnorm : (∑ j, (θ j - thetaStarRidge d W j) ^ 2) = 0 := by
    have hexpand : (∑ j, (θ j - thetaStarRidge d W j) ^ 2)
        = l2NormSq θ + l2NormSq (thetaStarRidge d W)
          - 2 * dot θ (thetaStarRidge d W) := by
      unfold l2NormSq dot
      calc (∑ j, (θ j - thetaStarRidge d W j) ^ 2)
          = ∑ j, (θ j ^ 2 + thetaStarRidge d W j ^ 2
              - 2 * (θ j * thetaStarRidge d W j)) :=
            Finset.sum_congr rfl fun j _ => by ring
        _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hexpand, hstar, hceq, hueq]
    ring
  funext j
  have hterm : (θ j - thetaStarRidge d W j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (θ k - thetaStarRidge d W k))).mp
      hnorm j (Finset.mem_univ j)
  have hzj : θ j - thetaStarRidge d W j = 0 := sq_eq_zero_iff.mp hterm
  linarith

end Qatlib.Papers.QRegression21.MainResults.RidgeUniqueness
