/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 14: threshold consequences of the gap lemma

Formalises Corollary 14 of Liu--Shaydulin--Niroula et al., *Certified
randomness using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1,
Corollary 14 and Eq. I.41, p. 6.

After Lemma 13 produces a threshold `t` with (Eq. I.41)

  `Pr[Y_τ > t+δ/2] ≥ (1+ε/8)·Pr[Y_{τ-1/T} > t] + (ε/16)·E[Y_τ]`,

Corollary 14 extracts two conclusions:

1. `ν1 = Pr[Y_τ > t+δ/2] ≥ Ω(ε²k/N)`, using
   `E[Y_τ] ≥ bk(p(τ)+q-1)/N ≥ εk/N` (Lemma 11 and Eq. I.27);
2. `ν0 = Pr[Y_{τ-1/T} > t] ≤ (1+ε/8)^{-1}·ν1`.

Both are pure real-arithmetic consequences of (I.41); we prove them outright
with the explicit constant `ε²k/(16N)` in the first conclusion (`Ω` made
explicit).  The construction of `t` itself is Lemma 13 (`SetGapLemma`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.RandCertLiu25.MainResults.ThresholdCorollary

/-- **Corollary 14, first conclusion** (explicit `Ω`): from Eq. I.41 and the
lower bound `E[Y_τ] ≥ εk/N`, the yes-case acceptance probability satisfies
`ν1 ≥ ε²k/(16N)`. -/
theorem corollary14_yes_probability (eps k N nu1 nu0 EY : ℝ)
    (heps : 0 ≤ eps) (hk : 0 < k) (hN : 0 < N) (hnu0 : 0 ≤ nu0)
    (hEY : eps * k / N ≤ EY)
    (hI41 : (1 + eps / 8) * nu0 + (eps / 16) * EY ≤ nu1) :
    eps ^ 2 * k / (16 * N) ≤ nu1 := by
  have hterm : 0 ≤ (1 + eps / 8) * nu0 := mul_nonneg (by linarith) hnu0
  have h1 : (eps / 16) * EY ≤ nu1 := by linarith
  have h2 : (eps / 16) * (eps * k / N) ≤ (eps / 16) * EY :=
    mul_le_mul_of_nonneg_left hEY (by linarith)
  have h3 : (eps / 16) * (eps * k / N) = eps ^ 2 * k / (16 * N) := by
    field_simp [hN.ne']
  linarith

/-- **Corollary 14, second conclusion**: the no-case acceptance probability is
at most `(1+ε/8)^{-1}·ν1`. -/
theorem corollary14_no_probability (eps nu1 nu0 : ℝ)
    (heps : 0 ≤ eps)
    (hI41 : (1 + eps / 8) * nu0 ≤ nu1) :
    nu0 ≤ (1 + eps / 8)⁻¹ * nu1 := by
  have hpos : 0 < 1 + eps / 8 := by linarith
  have h := mul_le_mul_of_nonneg_left hI41 (inv_nonneg.mpr hpos.le)
  rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at h

end Qatlib.Papers.RandCertLiu25.MainResults.ThresholdCorollary
