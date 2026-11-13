/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.QEigenProc24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# `ℓ^2` Norm Bounds and State Distance for Rescaled Chebyshev Polynomials

This module formalizes Lemma 17 (Eq. (179), p. 47) and Corollary 20 (Eq. (209),
p. 52) of Low and Su on the `ℓ^2` energy of regular and rescaled Chebyshev
polynomial evaluations `T_j(x)` and `T̃_j(x)` on `[-1/2, 1/2]` and the resulting
`O(1 / √n)` Euclidean distance bound between the normalized Chebyshev states.

## Main definitions

* `chebState`, `chebTildeState`: unnormalized regular and rescaled Chebyshev
  amplitude states in `ℂ^n`.

## Main statements

* `chebyshev_T_l2_sum_bounds`, `chebyshev_l2_sum_bounds`: Lemma 17, Eq. (179),
  `n / 2 - √3 / 3 ≤ ∑_{j < n} T_j(x)^2 ≤ n / 2 + √3 / 3` and shifted `T̃_j` bounds.
* `rescaled_chebyshev_state_distance`: Corollary 20, Eq. (209), normalized state
  distance bound between `chebTildeState` and `chebState`.

## References

* [Low and Su, 2024][LowSu2024QEigenProc], Lemma 17, Eq. (179), p. 47, and
  Corollary 20, Eq. (209), p. 52.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.QEigenProc24.MainResults.ChebyshevSum
open Qatlib.Papers.QEigenProc24.MainResults


/- ## Lemma 17, first pair of bounds (Eq. (179), p. 47) -/

/-- **Lemma 17, `T`-part (Eq. (179), p. 47).** (Fixed source: arXiv:2401.06240v3.)

For any `x ∈ [-1/2, 1/2]`,
`n/2 - √3/3 ≤ Σ_{j=0}^{n-1} T_j(x)^2 ≤ n/2 + √3/3`.

Source proof (pp. 47–48): write `x = cos θ` with `θ ∈ [π/3, 2π/3]`; the product-to-sum formula
gives `T_j(x)^2 = (1 + cos 2jθ)/2`, so the sum equals `n/2 + (1/2) Σ_j cos 2jθ`, and the
remaining cosine sum is bounded by `|Σ_j cos 2jθ| ≤ 2√3/3` because `2θ` avoids a neighbourhood
of `0` modulo `2π` (Eqs. (180)–(185)).

The formal proof telescopes the sine differences
`sin ((2j + 1)θ) - sin ((2j - 1)θ) = 2 sin θ cos (2jθ)` and uses
`sin θ ≥ √3/2`. -/
theorem chebyshev_T_l2_sum_bounds (n : ℕ) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    (n : ℝ) / 2 - Real.sqrt 3 / 3 ≤ ∑ j ∈ Finset.range n, (chebT j x) ^ 2 ∧
      ∑ j ∈ Finset.range n, (chebT j x) ^ 2 ≤ (n : ℝ) / 2 + Real.sqrt 3 / 3 := by
  let θ := Real.arccos x
  let C := ∑ j ∈ Finset.range n, Real.cos (2 * (j : ℝ) * θ)
  have hx' := abs_le.mp hx
  have hx2 : x ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 2 - x)
      (by linarith : 0 ≤ x + 1 / 2)]
  have hs0 : 0 ≤ Real.sin θ := by
    dsimp [θ]
    rw [Real.sin_arccos]
    exact Real.sqrt_nonneg _
  have hs2 : Real.sin θ ^ 2 = 1 - x ^ 2 := by
    dsimp [θ]
    rw [Real.sin_arccos, Real.sq_sqrt (by linarith)]
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hr2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ≤ 2 * Real.sin θ := by nlinarith
  let F : ℕ → ℝ := fun k => Real.sin ((2 * (k : ℝ) - 1) * θ)
  have hstep (j : ℕ) : F (j + 1) - F j =
      (2 * Real.sin θ) * Real.cos (2 * (j : ℝ) * θ) := by
    dsimp [F]
    rw [show (2 * ((j + 1 : ℕ) : ℝ) - 1) * θ =
        2 * (j : ℝ) * θ + θ by push_cast; ring,
      show (2 * (j : ℝ) - 1) * θ = 2 * (j : ℝ) * θ - θ by ring,
      Real.sin_add, Real.sin_sub]
    ring
  have htel : (2 * Real.sin θ) * C = F n + Real.sin θ := by
    dsimp [C]
    rw [Finset.mul_sum]
    simp_rw [← hstep]
    rw [Finset.sum_range_sub]
    simp [F]
  have hbound : (2 * Real.sin θ) * |C| ≤ 2 := by
    rw [← abs_of_nonneg (mul_nonneg (by norm_num) hs0), ← abs_mul, htel]
    exact (abs_add_le _ _).trans (by
      dsimp [F]
      linarith [Real.abs_sin_le_one ((2 * (n : ℝ) - 1) * θ),
        Real.abs_sin_le_one θ])
  have hC : Real.sqrt 3 * |C| ≤ 2 :=
    (mul_le_mul_of_nonneg_right hs (abs_nonneg C)).trans hbound
  have hC' : |C| ≤ 2 * Real.sqrt 3 / 3 := by
    have h := mul_le_mul_of_nonneg_left hC hr0
    rw [← mul_assoc, ← pow_two, hr2] at h
    linarith
  have hsum : ∑ j ∈ Finset.range n, (chebT j x) ^ 2 =
      (n : ℝ) / 2 + C / 2 := by
    have hterm (j : ℕ) : (chebT j x) ^ 2 =
        (1 + Real.cos (2 * (j : ℝ) * θ)) / 2 := by
      have h := Real.cos_two_mul ((j : ℝ) * θ)
      dsimp [chebT, θ] at *
      rw [mul_assoc]
      linarith
    simp_rw [hterm]
    dsimp [C]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp
    ring
  rw [hsum]
  have hCab := abs_le.mp hC'
  constructor <;> linarith

/- ## Lemma 17, second pair of bounds (Eq. (179), p. 47) -/

/-- **Lemma 17 (ℓ²-norm bounds for Chebyshev polynomials), Eq. (179), p. 47.**

For any `x ∈ [-1/2, 1/2]` and `n ≥ 1`,
`n/2 - √3/3 ≤ Σ_{j<n} T_j(x)^2 ≤ n/2 + √3/3` and
`n/2 - √3/3 - 3/4 ≤ Σ_{j<n} T̃_j(x)^2 ≤ n/2 + √3/3 - 3/4`.

The rescaled bounds follow from the first pair through `T̃_0 = T_0/2`, `T̃_j = T_j (j ≥ 1)`,
which gives `Σ T̃_j(x)^2 = Σ T_j(x)^2 - 3/4` (the `j = 0` term changes from `1` to `1/4`). -/
theorem chebyshev_l2_sum_bounds (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ((n : ℝ) / 2 - Real.sqrt 3 / 3 ≤ ∑ j ∈ Finset.range n, (chebT j x) ^ 2 ∧
        ∑ j ∈ Finset.range n, (chebT j x) ^ 2 ≤ (n : ℝ) / 2 + Real.sqrt 3 / 3) ∧
      ((n : ℝ) / 2 - Real.sqrt 3 / 3 - 3 / 4 ≤
          ∑ j ∈ Finset.range n, (chebTilde j x) ^ 2 ∧
        ∑ j ∈ Finset.range n, (chebTilde j x) ^ 2 ≤
          (n : ℝ) / 2 + Real.sqrt 3 / 3 - 3 / 4) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  subst hm
  simp only [Nat.succ_eq_add_one]
  have hT := chebyshev_T_l2_sum_bounds (m + 1) x hx
  have h0 : chebTilde 0 x = 1 / 2 := by simp [chebTilde]
  have hstep : ∀ j : ℕ, chebTilde (j + 1) x = chebT (j + 1) x := by
    intro j; simp [chebTilde]
  -- `Σ_{j<n} T_j(x)^2 = 1 + Σ_{j<m} T_{j+1}(x)^2`
  have hsplitT : ∑ j ∈ Finset.range (m + 1), (chebT j x) ^ 2
      = 1 + ∑ j ∈ Finset.range m, (chebT (j + 1) x) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp [chebT, Real.cos_zero, add_comm]
  -- `Σ_{j<n} T̃_j(x)^2 = 1/4 + Σ_{j<m} T_{j+1}(x)^2` (only the `j = 0` term changes)
  have hsplitTilde : ∑ j ∈ Finset.range (m + 1), (chebTilde j x) ^ 2
      = 1 / 4 + ∑ j ∈ Finset.range m, (chebT (j + 1) x) ^ 2 := by
    rw [Finset.sum_range_succ', h0]
    have hsq : (1 / 2 : ℝ) ^ 2 = 1 / 4 := by norm_num
    rw [hsq]
    rw [show ∑ j ∈ Finset.range m, (chebTilde (j + 1) x) ^ 2
        = ∑ j ∈ Finset.range m, (chebT (j + 1) x) ^ 2 from
      Finset.sum_congr rfl fun j _ => by rw [hstep j]]
    exact add_comm _ _
  -- Bounds for the shifted sum, transferred from the `T`-part bounds
  have hS1 : (((m : ℕ) + 1 : ℕ) : ℝ) / 2 - Real.sqrt 3 / 3 - 1 ≤
      ∑ j ∈ Finset.range m, (chebT (j + 1) x) ^ 2 := by linarith [hT.1, hsplitT]
  have hS2 : ∑ j ∈ Finset.range m, (chebT (j + 1) x) ^ 2 ≤
      (((m : ℕ) + 1 : ℕ) : ℝ) / 2 + Real.sqrt 3 / 3 - 1 := by linarith [hT.2, hsplitT]
  refine ⟨hT, ?_, ?_⟩
  · rw [hsplitTilde]
    linarith
  · rw [hsplitTilde]
    linarith

/- ## Corollary 20 (Eq. (209), p. 52) -/

/-- The regular Chebyshev state `Σ_{j<n} T_j(x)|j⟩`. -/
def chebState (n : ℕ) (x : ℝ) : VecI (Fin n) :=
  ofFun fun j => ((chebT j x : ℝ) : ℂ)

/-- The rescaled Chebyshev state `Σ_{j<n} T̃_j(x)|j⟩`. -/
def chebTildeState (n : ℕ) (x : ℝ) : VecI (Fin n) :=
  ofFun fun j => ((chebTilde j x : ℝ) : ℂ)

private theorem real_state_norm_sq {n : ℕ} (f : Fin n → ℝ) :
    ‖ofFun (fun j => (f j : ℂ))‖ ^ 2 = ∑ j, (f j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [ofFun, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem real_normalized_distance_sq {n : ℕ} (f g : Fin n → ℝ) :
    ‖normalize (ofFun (fun j => (f j : ℂ))) -
        normalize (ofFun (fun j => (g j : ℂ)))‖ ^ 2 =
      ∑ j, (f j / ‖ofFun (fun j => (f j : ℂ))‖ -
        g j / ‖ofFun (fun j => (g j : ℂ))‖) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j hj
  change ‖(‖ofFun (fun j => (f j : ℂ))‖ : ℂ)⁻¹ * (f j : ℂ) -
      (‖ofFun (fun j => (g j : ℂ))‖ : ℂ)⁻¹ * (g j : ℂ)‖ ^ 2 = _
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  congr 1
  ring

/-- **Corollary 20 (Distance between rescaled and regular Chebyshev states), Eq. (209), p. 52.**
(Fixed source: arXiv:2401.06240v3.)

For any `x ∈ [-1/2, 1/2]` and `n ≥ 1`,
`‖ Σ T̃_j(x)|j⟩ / √(Σ T̃_k(x)²) - Σ T_j(x)|j⟩ / √(Σ T_k(x)²) ‖
   ≤ (3/8)/√(n/2 - √3/3) · √(n/2 - √3/3 - 3/4) + (1/2)/√(n/2 - √3/3) = O(1/√n)`.

Source proof (p. 52): direct computation from Lemma 17; the two state vectors differ only in
their `j = 0` component (`T̃_0 = T_0/2`), and the two normalisation factors are bounded below
by the Lemma 17 lower bounds.

The formal proof computes the squared distance componentwise. For `n ≥ 2` it proves
the stronger bound `1 / (2 ‖chebState n x‖)` and applies the regular-state energy
lower bound; for `n = 1` the normalized states coincide. -/
theorem rescaled_chebyshev_state_distance (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ‖normalize (chebTildeState n x) - normalize (chebState n x)‖ ≤
      (3 / 8) / Real.sqrt ((n : ℝ) / 2 - Real.sqrt 3 / 3) *
          Real.sqrt ((n : ℝ) / 2 - Real.sqrt 3 / 3 - 3 / 4) +
        (1 / 2) / Real.sqrt ((n : ℝ) / 2 - Real.sqrt 3 / 3) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let u := chebTildeState (m + 1) x
  let v := chebState (m + 1) x
  let S := ∑ j : Fin m, (chebT (j.val + 1) x) ^ 2
  let a := ‖u‖
  let b := ‖v‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have ha2 : a ^ 2 = 1 / 4 + S := by
    dsimp [a, u, chebTildeState]
    rw [real_state_norm_sq, Fin.sum_univ_succ]
    norm_num [chebTilde, S]
  have hb2 : b ^ 2 = 1 + S := by
    dsimp [b, v, chebState]
    rw [real_state_norm_sq, Fin.sum_univ_succ]
    simp [chebT, S]
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have ha : 0 < a := by nlinarith
  have hb : 0 < b := by nlinarith
  have hd2 : ‖normalize u - normalize v‖ ^ 2 =
      ((1 / 2) / a - 1 / b) ^ 2 + S * (1 / a - 1 / b) ^ 2 := by
    change ‖normalize (ofFun (fun j : Fin (m + 1) => (chebTilde j x : ℂ))) -
      normalize (ofFun (fun j : Fin (m + 1) => (chebT j x : ℂ)))‖ ^ 2 = _
    rw [real_normalized_distance_sq, Fin.sum_univ_succ]
    change ((chebTilde 0 x) / a - (chebT 0 x) / b) ^ 2 +
      ∑ j : Fin m, ((chebTilde (j.val + 1) x) / a -
        (chebT (j.val + 1) x) / b) ^ 2 = _
    simp only [chebTilde, Nat.add_one_ne_zero, ↓reduceIte,
      chebT, Nat.cast_zero, zero_mul, Real.cos_zero]
    dsimp [S, chebT]
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdexact : ‖normalize u - normalize v‖ ^ 2 = 2 - (1 + 2 * S) / (a * b) := by
    rw [hd2]
    field_simp
    nlinarith [ha2, hb2]
  by_cases hm : m = 0
  · subst m
    have hS0 : S = 0 := by simp [S]
    have ha' : a = 1 / 2 := by nlinarith
    have hb' : b = 1 := by nlinarith
    have hd0 : ‖normalize u - normalize v‖ = 0 := by
      rw [ha', hb', hS0] at hd2
      nlinarith [norm_nonneg (normalize u - normalize v)]
    change ‖normalize u - normalize v‖ ≤ _
    rw [hd0]
    positivity
  · let A := ((m + 1 : ℕ) : ℝ) / 2 - Real.sqrt 3 / 3
    have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hr2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hr : Real.sqrt 3 < 7 / 4 := by nlinarith
    have hA : 0 < A := by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      dsimp [A]
      push_cast
      linarith
    have hq : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hfirst : 0 ≤ (3 / 8) / Real.sqrt A * Real.sqrt (A - 3 / 4) := by positivity
    change ‖normalize u - normalize v‖ ≤
      (3 / 8) / Real.sqrt A * Real.sqrt (A - 3 / 4) + (1 / 2) / Real.sqrt A
    have hpoly : ((1 + 2 * S) * b) ^ 2 - (a * (2 * b ^ 2 - 1 / 4)) ^ 2 =
        3 / 16 * S + 15 / 64 := by
      rw [mul_pow, mul_pow, ha2, hb2]
      ring
    have hlin : a * (2 * b ^ 2 - 1 / 4) ≤ (1 + 2 * S) * b := by
      have hleft : 0 ≤ a * (2 * b ^ 2 - 1 / 4) :=
        mul_nonneg ha0 (by nlinarith)
      have hright : 0 ≤ (1 + 2 * S) * b := by positivity
      apply (sq_le_sq₀ hleft hright).mp
      linarith
    have hdstrong : ‖normalize u - normalize v‖ ^ 2 ≤ ((1 / 2) / b) ^ 2 := by
      rw [hdexact, div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
      have heq : (2 - (1 + 2 * S) / (a * b)) * b ^ 2 =
          (2 * a * b ^ 2 - (1 + 2 * S) * b) / a := by
        field_simp
      rw [heq]
      apply (div_le_iff₀ ha).mpr
      nlinarith only [hlin]
    have hd : ‖normalize u - normalize v‖ ≤ (1 / 2) / b := by
      have hnonneg : 0 ≤ (1 / 2) / b := by positivity
      nlinarith [norm_nonneg (normalize u - normalize v)]
    have hbound := (chebyshev_l2_sum_bounds (m + 1) (by omega) x hx).1.1
    have hb2' : b ^ 2 = ∑ j ∈ Finset.range (m + 1), (chebT j x) ^ 2 := by
      dsimp [b, v, chebState]
      rw [real_state_norm_sq, ← Fin.sum_univ_eq_sum_range]
    have hqb : Real.sqrt A ≤ b := by
      rw [← hb2'] at hbound
      exact (Real.sqrt_le_left hb0).mpr hbound
    have hdiv : (1 / 2 : ℝ) / b ≤ (1 / 2) / Real.sqrt A :=
      div_le_div_of_nonneg_left (by norm_num) hq hqb
    linarith

end Qatlib.Papers.QEigenProc24.MainResults.ChebyshevSum
