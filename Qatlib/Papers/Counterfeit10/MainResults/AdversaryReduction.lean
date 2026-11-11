/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

/-!
# Reduction of adversary bounds to quartic lower bounds (Counterfeit10, §3)

Formal companion to Iwama–Nishimura–Raymond–Teruyama,
*Quantum Counterfeit Coin Problems*, arXiv:1009.0416v1, Section 3.

The paper derives its lower bounds by instantiating Zhang's strong weighted adversary theorem
(Lemma 3, imported from [20]) with an explicit weight scheme.  The *combinatorial* content of each
scheme is the computation of `μ(x) = Σ_y w(x,y)` and `ν(x,q) = Σ_y w'(x,y,q)` together with the
resulting ratio `μ(x)μ(y) / (ν(x,q)ν(y,q))`; the *analytic* content is the estimate of that ratio
(the paper's Lemma 4 and Lemma 6) and the final algebraic step from the estimate to the stated
`Ω` bound.

This file formalises the analytic/algebraic step for Theorem 2.  Write `C` for the number of coin
configurations `\binom{N}{k}` and `γ` for the number of those configurations that balance a fixed
pan pair.  The scheme has `μ(x) = C - 1`, `ν(x,q) = γ` (tilted `x`) and `ν(y,q) = C - γ`
(balanced `y`), so the squared adversary ratio is `(C-1)^2 / (γ (C-γ))` (the paper's Eq. (1)).
We prove that this dominates `(1/4) · C/γ`, and then that Lemma 4's estimate
`γ/C ≤ K √(c/k)` yields the quartic bound `(k/d)^{1/4}` with a constant `1/√K`, where `d = N/l`.
-/

namespace Qatlib.Papers.Counterfeit10.MainResults

/-- Theorem 2, squared adversary ratio: when `0 < γ ≤ C` and `C ≥ 2`, the squared ratio
`(C-1)^2 / (γ (C-γ))` is at least `(1/4) · C/γ`.  This is the numerical heart of Eq. (1): the
factor `(C-1)^2` and the tilt count `C - γ` lose at most the constant `1/4`. -/
theorem adversary_ratio_sq_lower {C g : ℝ} (hg0 : 0 < g) (hgC : g < C) (hC2 : 2 ≤ C) :
    (1 / 4) * (C / g) ≤ (C - 1) ^ 2 / (g * (C - g)) := by
  have hCpos : (0 : ℝ) < C := by linarith
  have hCg : (0 : ℝ) < C - g := by linarith
  have hkey : (1 / 4) * C * (C - g) ≤ (C - 1) ^ 2 := by nlinarith [hg0, hgC, hC2]
  rw [show (1 / 4) * (C / g) = ((1 / 4) * C) / g by ring]
  rw [div_le_div_iff₀ hg0 (mul_pos hg0 hCg)]
  have h2 : ((1 / 4) * C * (C - g)) * g ≤ (C - 1) ^ 2 * g :=
    mul_le_mul_of_nonneg_right hkey (le_of_lt hg0)
  nlinarith [h2]

/-- The same comparison after taking square roots: the adversary bound `√((C-1)^2/(γ(C-γ)))`
is at least `(1/2)·√(C/γ)`. -/
theorem adversary_ratio_sqrt_lower {C g : ℝ} (hg0 : 0 < g) (hgC : g < C) (hC2 : 2 ≤ C) :
    (1 / 2) * Real.sqrt (C / g) ≤ Real.sqrt ((C - 1) ^ 2 / (g * (C - g))) := by
  have hba := adversary_ratio_sq_lower hg0 hgC hC2
  have hroot : Real.sqrt ((1 / 4) * (C / g)) = (1 / 2) * Real.sqrt (C / g) := by
    rw [show (1 / 4 : ℝ) * (C / g) = ((1 / 2 : ℝ) ^ 2) * (C / g) by ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ 2)]
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]
  rw [← hroot]
  exact Real.sqrt_le_sqrt hba

/-- Theorem 2, quartic extraction in squared form.  Suppose Lemma 4 gives the estimate
`γ/C ≤ K √(c/k)` with `0 < c ≤ d` and `0 < k`.  Then the squared adversary bound `C/γ` is at
least `(1/K)·√(k/d)`; equivalently the bound itself is at least `(1/√K)·(k/d)^{1/4}`. -/
theorem quartic_reduction_sq {C g k c d K : ℝ}
    (hg : 0 < g) (hC : 0 < C) (hK : 0 < K) (hk : 0 < k)
    (hc : 0 < c) (hcd : c ≤ d)
    (hest : g / C ≤ K * Real.sqrt (c / k)) :
    (1 / K) * Real.sqrt (k / d) ≤ C / g := by
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le hc hcd
  have hSpos : (0 : ℝ) < Real.sqrt (c / k) := Real.sqrt_pos.mpr (div_pos hc hk)
  have hgc : (0 : ℝ) < g / C := div_pos hg hC
  have hinv : 1 / (K * Real.sqrt (c / k)) ≤ C / g := by
    calc 1 / (K * Real.sqrt (c / k)) ≤ 1 / (g / C) :=
          one_div_le_one_div_of_le hgc hest
      _ = C / g := by rw [one_div_div]
  have hident : Real.sqrt (k / c) = 1 / Real.sqrt (c / k) := by
    rw [show k / c = (c / k)⁻¹ by rw [inv_div], Real.sqrt_inv, one_div]
  have hkc : Real.sqrt (k / d) ≤ Real.sqrt (k / c) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hdpos hc]
    nlinarith [hk, hcd]
  rw [hident] at hkc
  have hstep : (1 / K) * Real.sqrt (k / d) ≤ 1 / (K * Real.sqrt (c / k)) := by
    calc (1 / K) * Real.sqrt (k / d) ≤ (1 / K) * (1 / Real.sqrt (c / k)) :=
          mul_le_mul_of_nonneg_left hkc (le_of_lt (one_div_pos.mpr hK))
      _ = 1 / (K * Real.sqrt (c / k)) := by rw [div_mul_div_comm]; simp
  exact le_trans hstep hinv

/-- Theorem 2, quartic extraction in the paper's form: under the Lemma 4 estimate, the adversary
bound `√(C/γ)` is at least `(1/√K)·(k/d)^{1/4}`, written as a nested square root. -/
theorem quartic_reduction {C g k c d K : ℝ}
    (hg : 0 < g) (hC : 0 < C) (hK : 0 < K) (hk : 0 < k)
    (hc : 0 < c) (hcd : c ≤ d)
    (hest : g / C ≤ K * Real.sqrt (c / k)) :
    (1 / Real.sqrt K) * Real.sqrt (Real.sqrt (k / d)) ≤ Real.sqrt (C / g) := by
  have hsq := quartic_reduction_sq hg hC hK hk hc hcd hest
  have hroot : Real.sqrt ((1 / K) * Real.sqrt (k / d))
      = (1 / Real.sqrt K) * Real.sqrt (Real.sqrt (k / d)) := by
    rw [Real.sqrt_mul (le_of_lt (one_div_pos.mpr hK))]
    congr 1
    rw [show (1 : ℝ) / K = K⁻¹ by ring, Real.sqrt_inv, one_div]
  rw [← hroot]
  exact Real.sqrt_le_sqrt hsq

/-- With the pan size `l = N/d` (`d = N/l`), the fourth root `(k/d)^{1/4}` is exactly the
Theorem 2 bound `(l k / N)^{1/4}`.  This is the purely arithmetic substitution `d = N/l`. -/
theorem fourth_root_pan_substitution {k l N : ℝ} (hN : 0 < N) (hl : 0 < l) :
    Real.sqrt (Real.sqrt (k / (N / l))) = Real.sqrt (Real.sqrt (l * k / N)) := by
  have h : k / (N / l) = l * k / N := by
    field_simp [ne_of_gt hN, ne_of_gt hl]
  rw [h]

end Qatlib.Papers.Counterfeit10.MainResults
