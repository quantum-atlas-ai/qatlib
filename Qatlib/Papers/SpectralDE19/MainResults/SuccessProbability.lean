/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Success probability of the QLSA readout

Fixed source: arXiv:1901.00961, *Quantum spectral methods for differential
equations*, Lemma 5 (§6, p. 15, eq. (6.1)), proof pp. 15–17.

The QLSA is applied to the collocation system `L|X⟩ = |B⟩`.  Measuring the
first and third registers splits the output into the "bad" part
`|X_bad⟩ = Σ_{h<m} Σ_l c_{i,l}(Γ_{h+1})|h,i,l⟩` (eq. (6.4)) and the "good" part
`|X_good⟩ = Σ_{h≥m} Σ_l x_i|h,i,l⟩` (eq. (6.5)).  The paper proves

* `‖X_good‖² = (p+1)(n+1)‖x(T)‖²`                        (eq. (6.9)),
* `‖X_bad‖² ≤ π m q² ‖x(T)‖²`                            (eq. (6.12)),

with `q := max_t ‖x̂(t)‖/‖x(T)‖` (eq. (6.2)).  The success probability of the
readout is `P = ‖X_good‖²/(‖X_good‖² + ‖X_bad‖²)`, and substituting the two
bounds gives (6.1)/(6.14)

  `P_measure ≥ (p+1)(n+1) / (π m q² + (p+1)(n+1))`.

This file proves the final order step (6.13)–(6.14) exactly.  The two norm
identities (6.9) and (6.12) — the paper's Chebyshev-orthogonality computation
(eqs. (6.10)–(6.12)) — enter as hypotheses with their equation numbers.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralDE19.MainResults

/-- **SpectralDE19, Lemma 5, eq. (6.1)/(6.14).**  If the good and bad masses of
the QLSA output satisfy `‖X_good‖² = (p+1)(n+1)‖x(T)‖²` (6.9) and
`‖X_bad‖² ≤ π m q² ‖x(T)‖²` (6.12), then the measurement success probability
`‖X_good‖²/(‖X_good‖²+‖X_bad‖²)` is at least the paper's bound. -/
theorem lemma5_success_probability
    (m p n : ℕ) (q xT good bad : ℝ)
    (hxT : 0 < xT) (hq : 0 ≤ q)
    (hgood : 0 ≤ good) (hbad : 0 ≤ bad)
    (hgood_eq : good = ((p + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * xT ^ 2)
    (hbad_le : bad ≤ Real.pi * (m : ℝ) * q ^ 2 * xT ^ 2) :
    ((p + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) /
        (Real.pi * (m : ℝ) * q ^ 2 + ((p + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
      ≤ good / (good + bad) := by
  set A : ℝ := ((p + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hC0 : 0 ≤ Real.pi * (m : ℝ) * q ^ 2 := by positivity
  have hden1 : 0 < A + Real.pi * (m : ℝ) * q ^ 2 := by positivity
  have hgoodpos : 0 < good := by
    rw [hgood_eq]; exact mul_pos hApos (by positivity)
  have hden2 : 0 < good + bad := by linarith
  -- Rewrite the two sides so that the comparison is `A/(A+πmq²) ≤ A xT²/(A xT² + bad)`.
  have hleft : A / (Real.pi * (m : ℝ) * q ^ 2 + A)
      = A / (A + Real.pi * (m : ℝ) * q ^ 2) := by ring_nf
  have hright : good / (good + bad) = A * xT ^ 2 / (A * xT ^ 2 + bad) := by
    rw [hgood_eq]
  rw [hleft, hright, div_le_div_iff₀ (by positivity) (by positivity)]
  -- `A * (A xT² + bad) ≤ A xT² * (A + πmq²)` follows from `bad ≤ πmq²xT²`.
  nlinarith [hbad_le, hApos, hxT, sq_nonneg xT]

end Qatlib.Papers.SpectralDE19.MainResults
