/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceTruncationTime — Lemma 9 (dissipative truncation time)

Fixed source: arXiv:2508.15170 (DissipDESolve25), Lemma 9, Equations (69)-(73), page 19.

Statement (paper). Let `ε_truncate > 0` and let `T` be sufficiently large so that
`T ≥ (1/η) log (4 ‖u(0)‖ / (ε_truncate ‖u(T)‖))`. Then, to guarantee Equation (69)
(the truncation at time `T₀ < T` changes the final state by at most `ε_truncate`), it
suffices to choose
`T₀ = O((1/η) log (max_t ‖b(t)‖ / (η ε_truncate ‖u(T)‖)))`.  Eq. (70).

The paper's proof (their Eq. (71)) bounds the Equation-(69) error `E` by the sum of a
transient and a truncation term,
```
E ≤ (2 ‖u(0)‖ / ‖u(T)‖) e^{-ηT}  +  (2 max_t ‖b(t)‖ / (‖u(T)‖ η)) e^{-ηT₀} .
```
This flow-norm reduction is the standard dissipativity estimate on `T e^{∫ A}` and is
supplied here as the hypothesis `hE`.  The remaining content — the two term bounds
(their Eqs. (71)-(72)) and the resulting `E ≤ ε_truncate` — is proved from the explicit
choice of `T` and `T₀`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DissipDESolve25.MainResults.SourceTruncationTime

/-- Lemma 9, p.19, first term of Eq. (71): the transient `2‖u(0)‖/‖u(T)‖·e^{-ηT}` is at
most `ε/2` whenever `(1/η) log (4‖u(0)‖/(ε‖u(T)‖)) ≤ T`. -/
theorem lemma9_first_term
    {η ε u0 uT T : ℝ} (hε : 0 < ε) (huT : 0 < uT) (hu0 : 0 ≤ u0)
    (hT : Real.log (4 * u0 / (ε * uT)) ≤ η * T) :
    2 * u0 * Real.exp (-(η * T)) / uT ≤ ε / 2 := by
  rcases eq_or_lt_of_le hu0 with hu0eq | hu0pos
  · -- Degenerate case `‖u(0)‖ = 0`.
    rw [← hu0eq]
    simp only [mul_zero, zero_mul, zero_div]
    positivity
  · -- Genuine case: invert the logarithm and use `exp` monotonicity.
    set A : ℝ := 4 * u0 / (ε * uT) with hAdef
    have hA : 0 < A := by
      rw [hAdef]; positivity
    have hexp_le : Real.exp (-(η * T)) ≤ ε * uT / (4 * u0) := by
      have hstep : Real.exp (-(η * T)) ≤ Real.exp (-(Real.log A)) :=
        Real.exp_le_exp.mpr (by linarith [hT, hAdef])
      have hinv : Real.exp (-(Real.log A)) = (ε * uT) / (4 * u0) := by
        rw [Real.exp_neg, Real.exp_log hA, hAdef, inv_div]
      rw [← hinv]
      exact hstep
    calc
      2 * u0 * Real.exp (-(η * T)) / uT ≤ 2 * u0 * (ε * uT / (4 * u0)) / uT := by
        gcongr
      _ = ε / 2 := by field_simp; ring

/-- Lemma 9, p.19, second term of Eq. (71): with `T₀ = (1/η) log(4 bmax/(η ε uT))`,
the truncation term `2 bmax/(uT η)·e^{-ηT₀}` is at most `ε/2`. This is the paper's
Eqs. (72)-(73). -/
theorem lemma9_second_term
    {η ε uT bmax T0 : ℝ} (hη : 0 < η) (hε : 0 < ε) (huT : 0 < uT) (hbmax : 0 ≤ bmax)
    (hT0 : T0 = (1 / η) * Real.log (4 * bmax / (η * ε * uT))) :
    2 * bmax * Real.exp (-(η * T0)) / (uT * η) ≤ ε / 2 := by
  rcases eq_or_lt_of_le hbmax with hb0 | hbpos
  · -- Degenerate case `max_t ‖b(t)‖ = 0`.
    rw [← hb0]
    simp only [mul_zero, zero_mul, zero_div]
    positivity
  · set A : ℝ := 4 * bmax / (η * ε * uT) with hAdef
    have hA : 0 < A := by rw [hAdef]; positivity
    have hinv : Real.exp (-(η * T0)) = A⁻¹ := by
      have hηT0 : η * T0 = Real.log A := by
        rw [hT0, hAdef]; field_simp
      rw [show -(η * T0) = -(Real.log A) by rw [hηT0],
        Real.exp_neg, Real.exp_log hA]
    have hAinv : A⁻¹ = η * ε * uT / (4 * bmax) := by
      rw [hAdef, inv_div]
    rw [hinv, hAinv]
    -- The two sides are exactly equal once the common factors cancel.
    have hEq : 2 * bmax * (η * ε * uT / (4 * bmax)) / (uT * η) = ε / 2 := by
      field_simp
      ring
    rw [hEq]

/-- Lemma 9, p.19, assembled: if the Equation-(69) truncation error `E` obeys the
Eq.-(71) bound, `T` satisfies the paper's largeness condition, and `T₀` is chosen as in
Eq. (70), then `E ≤ ε_truncate` — i.e. Equation (69) is guaranteed. -/
theorem lemma9_truncation_time
    {η ε u0 uT bmax T T0 E : ℝ}
    (hη : 0 < η) (hε : 0 < ε) (huT : 0 < uT) (hu0 : 0 ≤ u0) (hbmax : 0 ≤ bmax)
    (hT : Real.log (4 * u0 / (ε * uT)) ≤ η * T)
    (hT0 : T0 = (1 / η) * Real.log (4 * bmax / (η * ε * uT)))
    (hE : E ≤ 2 * u0 * Real.exp (-(η * T)) / uT
              + 2 * bmax * Real.exp (-(η * T0)) / (uT * η)) :
    E ≤ ε := by
  have h1 := lemma9_first_term hε huT hu0 hT
  have h2 := lemma9_second_term hη hε huT hbmax hT0
  linarith [hE, h1, h2]

end Qatlib.Papers.DissipDESolve25.MainResults.SourceTruncationTime
