/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma S13 — likelihood ratio of the thermal-drift sampler

Source: arXiv:2602.05912v2, Lemma S13, Eq. (C.60), page 21.

If `N = Ω(n λ² β²)` then, for `H = H(N)`,
`log L_N(P) = log( (1/2^n) Tr[e^{−βH}] ) + O(λ² β² / N)`.

The proof is a two-step reduction:
* Eq. (C.63): from the measurement law of Theorem S7 and
  `log(1+y) = y + O(y²)`, `tanh τ = τ + O(τ³)`, one gets
  `log L_N(P) = −τ ∑_t m_t M_{j_t}(x(t−1)) + O(N τ²)`;
* Eqs. (C.64)–(C.67): with `Z(x) = Tr exp(−τ ∑_j x_j σ_j)` and
  `∂_{x_j} log Z = −τ M_j(x)`, telescoping along the walk
  `x(t) − x(t−1) = m_t e_{j_t}` gives
  `−τ ∑_t m_t M_t = log Z(x(N)) − log Z(0) + O(N τ²)`,
  where `x(0) = 0` so `Z(0) = 2^n` and `Z(x(N)) = Tr[e^{−βH}]`.

Here both expansion steps are taken as the two hypotheses `h63` and `h67`
(they are exactly the statements derivable from Theorem S7 and the telescoping
identity, which are outside this claim); the theorem then performs the
triangle-inequality combination and rewrites `N τ² = λ²β²/N` using
`τ = λβ/N`, which is the remaining algebraic content of Eq. (C.60).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.ThermalDrift26.ThermalSampling

/-- Lemma S13 (arXiv:2602.05912v2, Eq. (C.60), p. 21): under the two expansion
steps (C.63) and (C.67), the log-likelihood ratio equals
`log(Tr e^{−βH}) − n log 2` up to `O(λ²β²/N)`.

This is the algebraic combination in the proof of Lemma S13; `logTr` is
`log Tr[e^{−βH}]` and `Q` is the magnetization sum `∑_t m_t M_t`. -/
theorem lemmaS13_likelihood_ratio
    (n N : ℕ) (lam beta tau : ℝ) (hlam : 0 < lam) (hbeta : 0 < beta)
    (hN : 0 < N) (htau : tau = lam * beta / (N : ℝ))
    (logTr LN Q : ℝ)
    (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h63 : |Real.log LN + tau * Q| ≤ C1 * ((N : ℝ) * tau ^ 2))
    (h67 : |-(tau * Q) - (logTr - (n : ℝ) * Real.log 2)| ≤
        C2 * ((N : ℝ) * tau ^ 2)) :
    |Real.log LN - (logTr - (n : ℝ) * Real.log 2)| ≤
      (C1 + C2) * (lam ^ 2 * beta ^ 2 / (N : ℝ)) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hsplit :
      Real.log LN - (logTr - (n : ℝ) * Real.log 2)
        = (Real.log LN + tau * Q) +
            (-(tau * Q) - (logTr - (n : ℝ) * Real.log 2)) := by
    ring
  have hEq : (N : ℝ) * tau ^ 2 = lam ^ 2 * beta ^ 2 / (N : ℝ) := by
    rw [htau]
    field_simp
  have hsum : |Real.log LN - (logTr - (n : ℝ) * Real.log 2)| ≤
      C1 * ((N : ℝ) * tau ^ 2) + C2 * ((N : ℝ) * tau ^ 2) := by
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add h63 h67)
  calc
    |Real.log LN - (logTr - (n : ℝ) * Real.log 2)|
        ≤ C1 * ((N : ℝ) * tau ^ 2) + C2 * ((N : ℝ) * tau ^ 2) := hsum
    _ = (C1 + C2) * ((N : ℝ) * tau ^ 2) := by ring
    _ = (C1 + C2) * (lam ^ 2 * beta ^ 2 / (N : ℝ)) := by rw [hEq]

end Qatlib.Papers.ThermalDrift26.ThermalSampling
