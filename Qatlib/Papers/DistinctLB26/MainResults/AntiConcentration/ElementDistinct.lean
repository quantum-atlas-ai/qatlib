/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DistinctLB26.MainResults.Framework.KnowledgeBound

/-!
# Anti-Concentration Bounds for Element Distinctness and k-Distinctness

This module formalizes the norm-level anti-concentration bounds for the polynomial-method
transfer space, the strict-versus-relaxed equal-element reduction, and the local-alteration
anti-concentration estimates for element distinctness and $k$-distinctness with singletons.

## Main statements

* `claim3_13`: Half-norm mask balancing implies $1/\sqrt{2}$-anti-concentration.
* `prop4_4`: Strict success probability bound $p_{\mathrm{strict}} \le (1 + 2 c n^2 / q) p_{\mathrm{relaxed}}$
  when collision probability is at most $1/2$.
* `theorem5_2`: Norm-level $O(1/n)$-anti-concentration for element distinctness.
* `theorem5_4`: Norm-level $O(1/\sqrt{n})$-anti-concentration with singletons when $K'/K \le 1/n$.

## References

* [Belovs, 2026][Belovs2026]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.AntiConcentration

open Qatlib.Papers.DistinctLB26.MainResults.Model
open Qatlib.Papers.DistinctLB26.MainResults.Framework

variable {ι : Type*}

/-! ## Claim 3.13: the polynomial-method transfer space is `1/√2`-anti-concentrated -/

/-- **Claim 3.13** [Belovs2026]: if the masked projection `projMask P ψ` carries half of the
squared norm of `ψ`, then `‖projMask P ψ‖ ≤ √(1 / 2) * ‖ψ‖`. -/
theorem claim3_13 [Fintype ι] (ψ : State ι) (P : ι → Prop) [DecidablePred P]
    (h : ‖Qatlib.Papers.DistinctLB26.MainResults.Core.State.projMask P ψ‖ ^ 2 = ‖ψ‖ ^ 2 / 2) :
    ‖Qatlib.Papers.DistinctLB26.MainResults.Core.State.projMask P ψ‖ ≤
      Real.sqrt (1 / 2) * ‖ψ‖ := by
  have hsq :
      ‖Qatlib.Papers.DistinctLB26.MainResults.Core.State.projMask P ψ‖ ^ 2 =
        (Real.sqrt (1 / 2) * ‖ψ‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), h]
    ring
  have hb : 0 ≤ Real.sqrt (1 / 2) * ‖ψ‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h1 := (sq_le_sq).mp (le_of_eq hsq)
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hb] at h1
  exact h1

/-! ## Proposition 4.4: strict versus relaxed Equal Element Problem -/

/-- **Proposition 4.4** [Belovs2026]: if `ps ≤ pr / (1 - ε)` with `0 ≤ ε ≤ 1 / 2` and
`ε ≤ c * n ^ 2 / q`, then `ps ≤ (1 + 2 * c * n ^ 2 / q) * pr`. -/
theorem prop4_4 (ps pr ε n q c : ℝ) (hpr : 0 ≤ pr) (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hεq : ε ≤ c * n ^ 2 / q) (_hc : 0 ≤ c)
    (hstrict : ps ≤ pr / (1 - ε)) :
    ps ≤ (1 + 2 * c * n ^ 2 / q) * pr := by
  have hden : 0 < 1 - ε := by linarith
  have hfull : 1 ≤ (1 + 2 * ε) * (1 - ε) := by nlinarith
  have h1 : pr / (1 - ε) ≤ (1 + 2 * ε) * pr := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hfull hpr]
  have hmul : ε * pr ≤ (c * n ^ 2 / q) * pr :=
    mul_le_mul_of_nonneg_right hεq hpr
  have h2 : (1 + 2 * ε) * pr ≤ (1 + 2 * (c * n ^ 2 / q)) * pr := by nlinarith
  calc ps ≤ pr / (1 - ε) := hstrict
    _ ≤ (1 + 2 * ε) * pr := h1
    _ ≤ (1 + 2 * (c * n ^ 2 / q)) * pr := h2
    _ = (1 + 2 * c * n ^ 2 / q) * pr := by ring

/-! ## Theorem 5.2: Element Distinctness is `O(1/n)`-anti-concentrated -/

/-- **Theorem 5.2 (Element Distinctness, anti-concentration)** [Belovs2026]: from the squared
norm bound `βρ ^ 2 ≤ c / n ^ 2 * β ^ 2`, deduce `βρ ≤ √(c / n ^ 2) * β`. -/
theorem theorem5_2 (βρ β c n : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hβρ : 0 ≤ βρ)
    (hβ : 0 ≤ β)
    (hanti : βρ ^ 2 ≤ c / n ^ 2 * β ^ 2) :
    βρ ≤ Real.sqrt (c / n ^ 2) * β :=
  lemma6_6 βρ β c (n ^ 2) (pow_pos hn 2) hc hβρ hβ hanti

/-! ## Theorem 5.4: anti-concentration with singletons -/

/-- **Theorem 5.4 (Anti-concentration with Singletons)** [Belovs2026]: combining the
local-alteration inequality `βρ ^ 2 ≤ C * K' / K * β ^ 2` with `K' / K ≤ 1 / n` yields
`βρ ≤ √(C / n) * β`. -/
theorem theorem5_4 (βρ β C K K' n : ℝ) (hn : 0 < n) (_hK : 0 < K) (hC : 0 ≤ C)
    (hβρ : 0 ≤ βρ) (hβ : 0 ≤ β)
    (h53 : βρ ^ 2 ≤ C * K' / K * β ^ 2) (hr : K' / K ≤ 1 / n) :
    βρ ≤ Real.sqrt (C / n) * β := by
  have hr' : C * K' / K ≤ C / n := by
    have h := mul_le_mul_of_nonneg_left hr hC
    calc C * K' / K = C * (K' / K) := by ring
      _ ≤ C * (1 / n) := h
      _ = C / n := by ring
  have h2 : C * K' / K * β ^ 2 ≤ C / n * β ^ 2 :=
    mul_le_mul_of_nonneg_right hr' (sq_nonneg β)
  exact lemma6_6 βρ β C n hn hC hβρ hβ (le_trans h53 h2)

end Qatlib.Papers.DistinctLB26.MainResults.AntiConcentration
