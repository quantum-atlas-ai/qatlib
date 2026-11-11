/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Model
import Qatlib.Papers.HeatEquation20.MainResults.ConditionNumber

/-!
# HeatEquation20 — spectral appendix (pp. 27–34)

Fixed source: arXiv:2004.06516v2.

* **Lemma 23** (p. 27, eqs. (A3)–(A6)): the eigenvalues of the heat-equation
  matrix `A` are the sums `λ_{j₁} + ⋯ + λ_{j_d}` of the one-dimensional
  eigenvalues `λ_j = −4 sin²(jπ/n)`, and the eigenvectors are the tensor
  products of Fourier modes.
* **Proposition 24** (p. 29, eqs. (B8)–(B9)): the eigenvalues of `A_j A_j†`
  are `(1−γ_j)² + 2(1−γ_j) cos θ + 1 = (sin θ / sin mθ)²`, where `θ` satisfies
  `(1−γ_j) sin mθ + sin(m+1)θ = 0`.
* **Proposition 25** (p. 29): in `d = 1` the condition number of (38) is
  `Θ(m)`, with `‖A‖ = Θ(1)` and `‖A⁻¹‖ = Θ(m)`.
* **Lemma 26** (pp. 30–31, eqs. (B20)–(B22)): closed form of the tridiagonal
  determinant `f_m` and of `det(Q_j + λI)` in terms of
  `x₁,₂ = (λ ± √(λ²−4))/2`.
* **Lemma 27** (p. 32): if `x₁ ∈ ℝ`, `|x₁| ≥ 1` and
  `x₁^{2m+1}(1 + x₁(1+β_j)) = x₁ + 1 + β_j`, then `x₁ = ±1`.

The identity of Proposition 24 and the reciprocal identities for the roots
`x₁, x₂` of Lemma 26 are proved.  The statements of Lemma 23, Proposition 25
and Lemma 26 were not carried into this port: their earlier formalisations
contained unproven gaps and were dropped, and they remain registered as claims
in `metadata/papers/HeatEquation20.json`.  Note on Lemma 27: as printed the
statement is false for arbitrary `β` (e.g. `x₁ = 2`, `m = 1`, `β = −14/10`:
both sides equal `8/5`); the hypothesis needed by the paper's proof, and
satisfied by the application where `β_j = γ_j/(1−γ_j)` with `0 ≤ γ_j ≤ 2`, is
`0 ≤ β` or `β ≤ −2`, and it is included below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators
open Matrix

/-! ## Lemma 23 (p. 27, eqs. (A3)–(A6)) -/

/-- **Proposition 24** (arXiv:2004.06516v2, p. 29, eqs. (B8)–(B9)).  If `θ` is
nonzero, `sin mθ ≠ 0`, and `(1−γ) sin mθ + sin(m+1)θ = 0` (equation (B9)),
then the eigenvalue expression (B8) of `A_j A_j†` equals `(sinθ/sin mθ)²`. -/
theorem proposition24_block_eigenvalue_identity (m : ℕ) (γ θ : ℝ)
    (hsin : Real.sin ((m : ℝ) * θ) ≠ 0)
    (hB9 : (1 - γ) * Real.sin ((m : ℝ) * θ) + Real.sin (((m : ℝ) + 1) * θ) = 0) :
    (1 - γ) ^ 2 + 2 * (1 - γ) * Real.cos θ + 1
      = (Real.sin θ / Real.sin ((m : ℝ) * θ)) ^ 2 := by
  -- Expand sin(m+1)θ and solve (B9) for cos mθ · sin θ.
  have hsinadd : Real.sin (((m : ℝ) + 1) * θ)
      = Real.sin ((m : ℝ) * θ) * Real.cos θ
        + Real.cos ((m : ℝ) * θ) * Real.sin θ := by
    rw [show ((m : ℝ) + 1) * θ = (m : ℝ) * θ + θ by ring, Real.sin_add]
  have hrel : Real.cos ((m : ℝ) * θ) * Real.sin θ
      = -(((1 - γ) + Real.cos θ) * Real.sin ((m : ℝ) * θ)) := by
    rw [hsinadd] at hB9
    linear_combination hB9
  have hsq : (Real.cos ((m : ℝ) * θ) * Real.sin θ) ^ 2
      = (((1 - γ) + Real.cos θ) * Real.sin ((m : ℝ) * θ)) ^ 2 := by
    rw [hrel]
    ring
  have hs1 : Real.sin ((m : ℝ) * θ) ^ 2 + Real.cos ((m : ℝ) * θ) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hs2 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hmul : ((1 - γ) ^ 2 + 2 * (1 - γ) * Real.cos θ + 1)
        * Real.sin ((m : ℝ) * θ) ^ 2 = Real.sin θ ^ 2 := by
    have hsin2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by linarith
    have hcos2 : Real.cos ((m : ℝ) * θ) ^ 2 + Real.sin ((m : ℝ) * θ) ^ 2 = 1 := by
      linarith
    calc ((1 - γ) ^ 2 + 2 * (1 - γ) * Real.cos θ + 1) * Real.sin ((m : ℝ) * θ) ^ 2
        = (((1 - γ) + Real.cos θ) ^ 2 + Real.sin θ ^ 2)
            * Real.sin ((m : ℝ) * θ) ^ 2 := by
          rw [hsin2]; ring
      _ = (((1 - γ) + Real.cos θ) ^ 2 * Real.sin ((m : ℝ) * θ) ^ 2
            + Real.sin θ ^ 2 * Real.sin ((m : ℝ) * θ) ^ 2) := by ring
      _ = (Real.cos ((m : ℝ) * θ) * Real.sin θ) ^ 2
            + Real.sin θ ^ 2 * Real.sin ((m : ℝ) * θ) ^ 2 := by rw [hsq]; ring
      _ = Real.sin θ ^ 2 * (Real.cos ((m : ℝ) * θ) ^ 2
            + Real.sin ((m : ℝ) * θ) ^ 2) := by ring
      _ = Real.sin θ ^ 2 := by rw [hcos2]; ring
  rw [div_pow, eq_div_iff (pow_ne_zero 2 hsin)]
  exact hmul

/-! ## Proposition 25 (p. 29) -/

/-- The larger root `x₁ = ½(λ + √(λ²−4))` of `x² − λx + 1 = 0`, Lemma 26, p. 30. -/
def triX1 (lam : ℝ) : ℝ := (lam + Real.sqrt (lam ^ 2 - 4)) / 2

/-- The smaller root `x₂ = ½(λ − √(λ²−4))` of `x² − λx + 1 = 0`, Lemma 26, p. 30. -/
def triX2 (lam : ℝ) : ℝ := (lam - Real.sqrt (lam ^ 2 - 4)) / 2

/-- The two roots of Lemma 26 sum to `λ`. -/
lemma triX1_add_triX2 (lam : ℝ) : triX1 lam + triX2 lam = lam := by
  unfold triX1 triX2
  ring

/-- The two roots of Lemma 26 satisfy `x₁ x₂ = 1`, i.e. `x₂ = 1/x₁`. -/
lemma triX1_mul_triX2 (lam : ℝ) (hlam : 2 ≤ |lam|) : triX1 lam * triX2 lam = 1 := by
  have h4 : 0 ≤ lam ^ 2 - 4 := by
    have hsq : |lam| ^ 2 = lam ^ 2 := sq_abs lam
    nlinarith [abs_nonneg lam]
  have hs : Real.sqrt (lam ^ 2 - 4) ^ 2 = lam ^ 2 - 4 := Real.sq_sqrt h4
  unfold triX1 triX2
  nlinarith [hs]

/-- For `|λ| > 2` the two roots of Lemma 26 are distinct (the `x₁ ≠ x₂`
hypothesis of (B21)–(B22)). -/
lemma triX1_ne_triX2 (lam : ℝ) (hlam : 2 < |lam|) : triX1 lam ≠ triX2 lam := by
  have h4 : 0 < lam ^ 2 - 4 := by
    have hsq : |lam| ^ 2 = lam ^ 2 := sq_abs lam
    nlinarith [abs_nonneg lam]
  have hs : Real.sqrt (lam ^ 2 - 4) ≠ 0 := by
    intro h0
    have hsq := Real.sq_sqrt h4.le
    rw [h0] at hsq
    norm_num at hsq
    linarith
  unfold triX1 triX2
  intro h
  exact hs (by linarith)

/-! ## Lemma 27 (p. 32) -/

/-- Auxiliary form of Lemma 27: for `x > 1` and `c ≥ 1` the equation
`x^{2n+1}(1 + xc) = x + c` has no solution. -/
private lemma lemma27_no_root_pos (n : ℕ) (x c : ℝ) (hx : 1 < x) (hc : 1 ≤ c)
    (h : x ^ (2 * n + 1) * (1 + x * c) = x + c) : False := by
  have hA : 1 < x ^ (2 * n + 1) := one_lt_pow₀ hx (by omega)
  have hfac : 0 < 1 + x * c := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < x) (by linarith : (0 : ℝ) < c)]
  have h1 : x + c ≤ 1 + x * c := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ x - 1) (by linarith : (0 : ℝ) ≤ c - 1)
    nlinarith
  have h2 : 1 + x * c < x ^ (2 * n + 1) * (1 + x * c) := by
    simpa using mul_lt_mul_of_pos_right hA hfac
  linarith

/-- Auxiliary form of Lemma 27: for `x > 1` and `c ≥ 1` the equation
`x^{2n+1}(xc − 1) = c − x` has no solution. -/
private lemma lemma27_no_root_mirror (n : ℕ) (x c : ℝ) (hx : 1 < x) (hc : 1 ≤ c)
    (h : x ^ (2 * n + 1) * (x * c - 1) = c - x) : False := by
  have hxc : 0 ≤ x * c - 1 := by
    have hmul : (1 : ℝ) ≤ x * c := by
      have := mul_le_mul hx.le hc zero_le_one (by linarith : (0 : ℝ) ≤ x)
      simpa using this
    linarith
  have hpow : 1 ≤ x ^ (2 * n + 1) := one_le_pow₀ hx.le
  have hge : x * c - 1 ≤ x ^ (2 * n + 1) * (x * c - 1) := by
    calc x * c - 1 = 1 * (x * c - 1) := by ring
      _ ≤ x ^ (2 * n + 1) * (x * c - 1) := mul_le_mul_of_nonneg_right hpow hxc
  rw [h] at hge
  have hpos : 0 < (x - 1) * (c + 1) := mul_pos (by linarith) (by linarith)
  nlinarith [hge, hpos]

/-- Auxiliary form of Lemma 27: for `x > 1` and `c ≥ 1` the equation
`x^{2n+1}(1 − xc) = x − c` has no solution. -/
private lemma lemma27_no_root_negfac (n : ℕ) (x c : ℝ) (hx : 1 < x) (hc : 1 ≤ c)
    (h : x ^ (2 * n + 1) * (1 - x * c) = x - c) : False := by
  have hA : 1 ≤ x ^ (2 * n + 1) := one_le_pow₀ hx.le
  have hAx : 1 < x * x ^ (2 * n + 1) := by
    have := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ x)
    linarith
  have h2 : x ^ (2 * n + 1) - x = c * (x * x ^ (2 * n + 1) - 1) := by
    nlinarith [h]
  have hcA : x * x ^ (2 * n + 1) - 1 ≤ c * (x * x ^ (2 * n + 1) - 1) := by
    simpa using mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ x * x ^ (2 * n + 1) - 1)
  have hpos : 0 < (x - 1) * (x ^ (2 * n + 1) + 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [h2, hcA, hpos]

/-- **Lemma 27** (arXiv:2004.06516v2, p. 32).  If `x₁ ∈ ℝ`, `|x₁| ≥ 1`, and
`x₁^{2m+1}(1 + x₁(1+β_j)) = x₁ + 1 + β_j`, then `x₁ = ±1`.

The printed statement omits a hypothesis on `β_j` and is false without one
(`x₁ = 2`, `m = 1`, `β_j = −14/10` satisfies the equation).  The proof in the
paper uses the range `β_j = γ_j/(1−γ_j)` with `0 ≤ γ_j ≤ 2`, i.e.
`β_j ≥ 0` or `β_j ≤ −2`, which is the disjunction assumed below. -/
theorem lemma27_real_root_rigidity (m : ℕ) (hm : 0 < m) (x1 β : ℝ)
    (hx : 1 ≤ |x1|) (hβ : 0 ≤ β ∨ β ≤ -2)
    (heq : x1 ^ (2 * m + 1) * (1 + x1 * (1 + β)) = x1 + 1 + β) :
    x1 = 1 ∨ x1 = -1 := by
  have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
  by_cases hgt : 1 < x1
  · -- Case `x₁ > 1`: the paper's first contradiction.
    rcases hβ with hβ | hβ
    · have hc : 1 ≤ 1 + β := by linarith
      have h : x1 ^ (2 * m + 1) * (1 + x1 * (1 + β)) = x1 + (1 + β) := by linarith
      exact (lemma27_no_root_pos m x1 (1 + β) hgt hc h).elim
    · have hc : 1 ≤ -(1 + β) := by linarith
      have h : x1 ^ (2 * m + 1) * (1 - x1 * (-(1 + β))) = x1 - (-(1 + β)) := by
        nlinarith [heq]
      exact (lemma27_no_root_negfac m x1 (-(1 + β)) hgt hc h).elim
  · -- Case `x₁ ≤ 1`.
    have hxle : x1 ≤ 1 := le_of_not_gt hgt
    rcases le_or_gt 0 x1 with h0 | h0
    · left
      have habs : |x1| = x1 := abs_of_nonneg h0
      linarith
    · have habs : |x1| = -x1 := abs_of_neg h0
      have hxle1 : x1 ≤ -1 := by linarith
      rcases lt_or_eq_of_le hxle1 with hlt | heq1
      · exfalso
        have hposx : 1 < -x1 := by linarith
        rcases hβ with hβ | hβ
        · -- `β ≥ 0`, `x₁ < −1`: the paper's second contradiction.
          have hc : 1 ≤ 1 + β := by linarith
          have h : (-x1) ^ (2 * m + 1) * ((-x1) * (1 + β) - 1) = (1 + β) - (-x1) := by
            rw [hodd.neg_pow]
            nlinarith [heq]
          exact (lemma27_no_root_mirror m (-x1) (1 + β) hposx hc h).elim
        · -- `β ≤ −2`, `x₁ < −1`.
          have hc : 1 ≤ -(1 + β) := by linarith
          have h : (-x1) ^ (2 * m + 1) * (1 + (-x1) * (-(1 + β))) = (-x1) + (-(1 + β)) := by
            rw [hodd.neg_pow]
            nlinarith [heq]
          exact (lemma27_no_root_pos m (-x1) (-(1 + β)) hposx hc h).elim
      · right
        exact heq1

end Qatlib.Papers.HeatEquation20.MainResults
