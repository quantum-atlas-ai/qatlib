/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.KrausCompile.BornMoments.IndependentShots
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

/-! Spectral statistics for
"A quantum algorithm for estimating the determinant"
(arXiv:2504.11049, 2025), Appendix A (Notation).

An `n × n` positive matrix `A` with spectrum rescaled to
`1 / (2κ) ≤ lam_j ≤ 1 / 2` has log-determinant
`α = ∑ log lam_j`, spectral log-mean `μ = α / n` and spectral
log-variance `Δ² = (1/n) ∑ (log lam_j - μ)²`. This block proves the three
spectral bounds of Eq. (UPMU):

- `mu_neg_log2_le : μ ≤ -log 2`, hence `|μ| ≥ log 2`;
- `neg_log2kappa_le_mu : -log (2κ) ≤ μ`, hence `|μ| ≤ log (2κ)`;
- `delta_le : Δ ≤ (log κ) / 2` (Popoviciu's inequality for values in an
  interval of length `log κ`).

Everything is elementary finite real arithmetic on the eigenvalue list;
the matrix itself enters only through the spectrum bounds.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DetEstimate25.MainResults
open scoped BigOperators

/-! ## The Popoviciu range bound on a finite variance -/

/-- The centered sum of squares around the mean equals the sum of
squares around any other center `c` minus `n (c - mean)²`: the mean
minimizes the sum of squared deviations. -/
theorem sum_sq_sub_mean_eq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (c : ℝ) :
    ∑ j, (x j - (∑ i, x i) / n) ^ 2
      = ∑ j, (x j - c) ^ 2 - n * (c - (∑ i, x i) / n) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : ∑ j, x j = n * ((∑ i, x i) / n) := by
    field_simp
  have hcross : ∑ j, (x j - c) = -n * (c - (∑ i, x i) / n) := by
    have hsplit : ∑ j, (x j - c) = ∑ j, x j - ∑ j : Fin n, (c : ℝ) :=
      show (∑ j, (x j - c)) = (∑ j, x j) - ∑ j : Fin n, (c : ℝ) from
        Finset.sum_sub_distrib (fun j : Fin n => x j) (fun _ : Fin n => (c : ℝ))
    have hconst : ∑ j : Fin n, (c : ℝ) = n * c := by simp
    rw [hsplit, hconst, hsum]
    field_simp
    ring
  have hexp : ∀ j, x j - (∑ i, x i) / n = (x j - c) + (c - (∑ i, x i) / n) := by
    intro j; ring
  have hsplit1 : ∑ j, ((x j - c) + (c - (∑ i, x i) / n)) ^ 2
      = ∑ j, ((x j - c) ^ 2 + (2 * (x j - c) * (c - (∑ i, x i) / n)
        + (c - (∑ i, x i) / n) ^ 2)) :=
    Finset.sum_congr rfl (fun j _ => by ring)
  have hsplit2 : ∑ j, ((x j - c) ^ 2 + (2 * (x j - c) * (c - (∑ i, x i) / n)
        + (c - (∑ i, x i) / n) ^ 2))
      = ∑ j, (x j - c) ^ 2 + ∑ j, 2 * (x j - c) * (c - (∑ i, x i) / n)
        + ∑ j : Fin n, (c - (∑ i, x i) / n) ^ 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    abel
  have hconst : ∑ j : Fin n, ((c - (∑ i, x i) / n) : ℝ) ^ 2
      = n * (c - (∑ i, x i) / n) ^ 2 := by simp
  have hmul : ∑ j, 2 * (x j - c) * (c - (∑ i, x i) / n)
      = 2 * (c - (∑ i, x i) / n) * ∑ j, (x j - c) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hstart : ∑ j, (x j - (∑ i, x i) / n) ^ 2
      = ∑ j, ((x j - c) + (c - (∑ i, x i) / n)) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by rw [hexp j])
  rw [hstart, hsplit1, hsplit2, hconst, hmul, hcross]
  ring

/-- **Popoviciu's inequality** for an `n`-point sample in an interval
`[a, b]`: the empirical variance is at most a quarter of the squared
interval length. -/
theorem popoviciu {n : ℕ} (hn : 0 < n) {a b : ℝ} (hab : a ≤ b)
    (x : Fin n → ℝ) (hx : ∀ j, a ≤ x j ∧ x j ≤ b) :
    (∑ j, (x j - (∑ i, x i) / n) ^ 2) / n ≤ ((b - a) / 2) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnn : (0 : ℝ) ≤ (b - a) / 2 := by linarith
  have hbc : ∀ j, |x j - (a + b) / 2| ≤ (b - a) / 2 := by
    intro j
    exact abs_le.2 ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩
  have hbound : ∀ j, (x j - (a + b) / 2) ^ 2 ≤ ((b - a) / 2) ^ 2 := by
    intro j
    exact (sq_le_sq).2 (by rw [abs_of_nonneg hnn]; exact hbc j)
  have hle : ∑ j, (x j - (a + b) / 2) ^ 2 ≤ n * ((b - a) / 2) ^ 2 := by
    calc ∑ j, (x j - (a + b) / 2) ^ 2 ≤ ∑ j, ((b - a) / 2) ^ 2 :=
          Finset.sum_le_sum (fun j _ => hbound j)
      _ = n * ((b - a) / 2) ^ 2 := by simp
  rw [div_le_iff₀ (Nat.cast_pos.mpr hn), sum_sq_sub_mean_eq hn x ((a + b) / 2)]
  have hsub : (0 : ℝ) ≤ n * (((a + b) / 2) - (∑ i, x i) / n) ^ 2 := by positivity
  linarith

/-! ## The spectral statistics of the log-determinant problem -/

/-- The log-determinant of a matrix with eigenvalue list `lam`:
`α = log det A = ∑_j log lam_j`. -/
def alpha {n : ℕ} (lam : Fin n → ℝ) : ℝ := ∑ j, Real.log (lam j)

/-- The mean of the log-spectrum: `μ = α / n`. -/
def mu {n : ℕ} (lam : Fin n → ℝ) : ℝ := alpha lam / n

/-- The variance of the log-spectrum:
`Δ² = (1/n) ∑_j (log lam_j - μ)²`. -/
def deltaSq {n : ℕ} (lam : Fin n → ℝ) : ℝ := (∑ j, (Real.log (lam j) - mu lam) ^ 2) / n

/-- The spectral log-deviation `Δ = √Δ²`. -/
def delta {n : ℕ} (lam : Fin n → ℝ) : ℝ := Real.sqrt (deltaSq lam)

/-- Rescaled spectrum upper bound `lam_j ≤ 1/2` forces every `log lam_j`
below `-log 2`, hence `μ ≤ -log 2 < 0`. -/
theorem mu_neg_log2_le {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ)
    (hpos : ∀ j, 0 < lam j) (hhi : ∀ j, lam j ≤ 1 / 2) :
    mu lam ≤ -Real.log 2 := by
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub]
  have h1 : ∀ j, Real.log (lam j) ≤ -Real.log 2 := by
    intro j
    have h2 := Real.log_le_log (hpos j) (hhi j)
    rwa [hloghalf] at h2
  have h3 : alpha lam ≤ -n * Real.log 2 := by
    rw [alpha]
    calc ∑ j, Real.log (lam j) ≤ ∑ j : Fin n, (-Real.log 2) :=
          Finset.sum_le_sum (fun j _ => h1 j)
      _ = -n * Real.log 2 := by simp
  rw [mu, div_le_iff₀ (Nat.cast_pos.mpr hn)]
  linarith

/-- Since `μ ≤ -log 2 < 0`, its modulus obeys `|μ| ≥ log 2`. -/
theorem mu_abs_ge_log2 {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ)
    (hpos : ∀ j, 0 < lam j) (hhi : ∀ j, lam j ≤ 1 / 2) :
    Real.log 2 ≤ |mu lam| := by
  have h := mu_neg_log2_le hn lam hpos hhi
  have hposlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- Rescaled spectrum lower bound `lam_j ≥ 1/(2κ)` gives
`μ ≥ -log (2κ)`. -/
theorem neg_log2kappa_le_mu {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {κ : ℝ}
    (hκ : 1 ≤ κ) (hlo : ∀ j, 1 / (2 * κ) ≤ lam j) :
    -Real.log (2 * κ) ≤ mu lam := by
  have hpos2κ : 0 < 2 * κ := by linarith
  have hlow : Real.log (1 / (2 * κ) : ℝ) = -Real.log (2 * κ) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hpos2κ), Real.log_one, zero_sub]
  have h1 : ∀ j, -Real.log (2 * κ) ≤ Real.log (lam j) := by
    intro j
    have h2κ : 0 < 1 / (2 * κ) := by positivity
    have h2 := Real.log_le_log h2κ (hlo j)
    rwa [hlow] at h2
  have h3 : -n * Real.log (2 * κ) ≤ alpha lam := by
    rw [alpha]
    calc -n * Real.log (2 * κ) ≤ ∑ j : Fin n, (-Real.log (2 * κ)) := by simp
      _ ≤ ∑ j, Real.log (lam j) := Finset.sum_le_sum (fun j _ => h1 j)
  rw [mu, le_div_iff₀ (Nat.cast_pos.mpr hn)]
  linarith

/-- Combining both sides: `|μ| ≤ log (2κ)` (Eq. UPMU). -/
theorem mu_abs_le_log2kappa {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {κ : ℝ}
    (hκ : 1 ≤ κ) (hlo : ∀ j, 1 / (2 * κ) ≤ lam j)
    (hpos : ∀ j, 0 < lam j) (hhi : ∀ j, lam j ≤ 1 / 2) :
    |mu lam| ≤ Real.log (2 * κ) := by
  have h1 := mu_neg_log2_le hn lam hpos hhi
  have h2 := neg_log2kappa_le_mu hn lam hκ hlo
  rw [abs_of_nonpos (by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])]
  linarith

/-- The log-spectrum lies in an interval of length
`log κ = log (2κ) - log 2`, so Popoviciu gives
`Δ² ≤ (log κ / 2)²`. -/
theorem deltaSq_le {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hlo : ∀ j, 1 / (2 * κ) ≤ lam j) (hpos : ∀ j, 0 < lam j)
    (hhi : ∀ j, lam j ≤ 1 / 2) :
    deltaSq lam ≤ (Real.log κ / 2) ^ 2 := by
  have hpos2κ : 0 < 2 * κ := by linarith
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub]
  have hlow : Real.log (1 / (2 * κ) : ℝ) = -Real.log (2 * κ) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hpos2κ), Real.log_one, zero_sub]
  have hrange : ∀ j, -Real.log (2 * κ) ≤ Real.log (lam j)
      ∧ Real.log (lam j) ≤ -Real.log 2 := by
    intro j
    have h2κ : 0 < 1 / (2 * κ) := by positivity
    have hA := Real.log_le_log h2κ (hlo j)
    rw [hlow] at hA
    have hB := Real.log_le_log (hpos j) (hhi j)
    rw [hloghalf] at hB
    exact ⟨hA, hB⟩
  have hhab : (-Real.log (2 * κ) : ℝ) ≤ -Real.log 2 := by
    rw [neg_le_neg_iff]
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith)
  have hpop := popoviciu hn (a := -Real.log (2 * κ)) (b := -Real.log 2)
    hhab (fun j => Real.log (lam j)) hrange
  have hlen : ((-Real.log 2) - (-Real.log (2 * κ))) / 2 = Real.log κ / 2 := by
    have e : (-Real.log 2) - (-Real.log (2 * κ)) = Real.log κ := by
      rw [neg_sub_neg, ← Real.log_div (ne_of_gt hpos2κ) two_ne_zero]
      congr 1
      field_simp
    rw [e]
  rw [hlen] at hpop
  have hmu : mu lam = (∑ i, Real.log (lam i)) / n := by rw [mu, alpha]
  rw [deltaSq, hmu]
  exact hpop

/-- `Δ ≤ log κ / 2`, the Popoviciu deviation bound of Eq. (UPMU). -/
theorem delta_le {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hlo : ∀ j, 1 / (2 * κ) ≤ lam j) (hpos : ∀ j, 0 < lam j)
    (hhi : ∀ j, lam j ≤ 1 / 2) :
    delta lam ≤ Real.log κ / 2 := by
  have h := deltaSq_le hn lam hκ hlo hpos hhi
  have h0 : (0 : ℝ) ≤ Real.log κ := Real.log_nonneg (by linarith)
  rw [delta]
  calc Real.sqrt (deltaSq lam) ≤ Real.sqrt ((Real.log κ / 2) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.log κ / 2 := Real.sqrt_sq (by linarith)

end Qatlib.Papers.DetEstimate25.MainResults
