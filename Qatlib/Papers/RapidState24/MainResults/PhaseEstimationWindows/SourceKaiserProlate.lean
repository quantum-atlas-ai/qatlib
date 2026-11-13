/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RapidState24 — Kaiser and prolate-spheroidal window errors

Paper: Berry et al., *Rapid initial state preparation for the quantum simulation
of strongly correlated molecules*, arXiv:2409.11748v1 (2024).

This file covers:

* `c005` — Section IV.A, pp. 14–15, Eqs. (37)–(44).  The Kaiser tail
  `δ ≈ 4 ln(2α) √α e^{−2πα}` (Eq. 41), its exact logarithmic inversion
  `ln(1/δ) = 2πα − ln[4 ln(2α)√α]` (Eq. 42), the leading solution
  `α ≈ ln(1/δ)/(2π)` (Eq. 43), and the exact decomposition of the confidence
  width `N = (π/ε)√(1+α²)` into `ln(1/δ)/(2ε)` plus explicit remainder
  (Eq. 44).
* `c006` — Section IV.C, pp. 17–18, Eqs. (57)–(60), Appendix B p. 37.
  Slepian's expansion Eq. (58) with coefficients `(3/32, 389/2¹¹)`, the
  corrected expansion Eq. (59) with coefficients `(7/16, 91/2⁹)`, the
  difference of the two brackets, and the fact that for large `c` the corrected
  error is strictly smaller while both windows have the same leading cost
  `ln(1/δ)/(2ε)` (Eq. 60).

These are analytic approximations.  The Lean statements below keep the paper's
explicit formulas as definitions and prove the exact algebraic and ordering
content (logarithmic inversion, coefficient simplification, bracket ordering,
and leading-cost equality).  The `O(·)` remainders are represented explicitly
rather than as asymptotic classes.

Related library material: `Qatlib.Concepts.AmplitudeCore.PhaseEstimation`
contains the BHMT QPE window-mass bound, not the Kaiser/prolate expansions.
-/

namespace Qatlib.Papers.RapidState24.MainResults.PhaseEstimationWindows

set_option autoImplicit false

/-! ## Claim c005: Kaiser window -/

/-- Eq. (41), Section IV.A, p. 15: the Kaiser tail approximation
`δ ≈ 4 ln(2α) √α e^{−2πα}`.  This is the paper's expression, used here as the
definition of the tail. -/
noncomputable def kaiserTail (α : ℝ) : ℝ :=
  4 * Real.log (2 * α) * Real.sqrt α * Real.exp (-(2 * Real.pi * α))

/-- Positivity of the Kaiser tail for `α > 1/2` (the regime in which
`ln(2α) > 0`).  Section IV.A, p. 15. -/
theorem kaiserTail_pos (α : ℝ) (hα : 1 / 2 < α) : 0 < kaiserTail α := by
  have h2α : 1 < 2 * α := by linarith
  have hlog : 0 < Real.log (2 * α) := Real.log_pos h2α
  have hαpos : 0 < α := by linarith
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hαpos
  have hexp : 0 < Real.exp (-(2 * Real.pi * α)) := Real.exp_pos _
  unfold kaiserTail
  positivity

/-- **Claim c005, Eq. (42).**  Section IV.A, p. 15: taking logarithms of
Eq. (41) gives `ln(1/δ) = 2πα − ln[4 ln(2α)√α]`.  This is an exact identity for
the tail definition above, for `α > 1/2`. -/
theorem kaiser_log_identity (α : ℝ) (hα : 1 / 2 < α) :
    Real.log (1 / kaiserTail α)
      = 2 * Real.pi * α - Real.log (4 * Real.log (2 * α) * Real.sqrt α) := by
  have h2α : 1 < 2 * α := by linarith
  have hlog : 0 < Real.log (2 * α) := Real.log_pos h2α
  have hαpos : 0 < α := by linarith
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.2 hαpos
  have hinner : 0 < 4 * Real.log (2 * α) * Real.sqrt α := by positivity
  have hexp : 0 < Real.exp (-(2 * Real.pi * α)) := Real.exp_pos _
  have hx : kaiserTail α
      = (4 * Real.log (2 * α) * Real.sqrt α) * Real.exp (-(2 * Real.pi * α)) := by
    unfold kaiserTail
    ring
  rw [show (1 : ℝ) / kaiserTail α = (kaiserTail α)⁻¹ by rw [one_div], Real.log_inv]
  rw [hx, Real.log_mul hinner.ne' hexp.ne', Real.log_exp]
  ring

/-- **Claim c005, Eq. (43) leading term.**  Section IV.A, p. 15: the leading
solution of Eq. (42) is `α ≈ ln(1/δ)/(2π)`, i.e. `2πα = ln(1/δ)` exactly at
leading order. -/
theorem kaiser_alpha_leading (δ : ℝ) (hδ : 0 < δ) :
    2 * Real.pi * ((1 / (2 * Real.pi)) * Real.log (1 / δ)) = Real.log (1 / δ) := by
  field_simp [Real.pi_pos.ne']

/-- The Kaiser confidence width Eq. (44), Section IV.A, p. 15:
`N = (π/ε)√(1+α²)`. -/
noncomputable def kaiserN (ε α : ℝ) : ℝ :=
  Real.pi / ε * Real.sqrt (1 + α ^ 2)

/-- **Claim c005, Eq. (44) exact decomposition.**  Section IV.A, p. 15:
`N = (π/ε)√(1+α²)` equals `ln(1/δ)/(2ε)` plus the explicit remainder
`(1/(2ε)) ln[4 ln(2α)√α] + (π/ε)(√(1+α²) − α)`.  The paper writes the
remainder as `O(ε⁻¹ ln ln(1/δ))`; here it is kept explicitly. -/
theorem kaiserN_decomposition (ε α : ℝ) (hε : 0 < ε) (hα : 1 / 2 < α) :
    kaiserN ε α
      = (1 / (2 * ε)) * Real.log (1 / kaiserTail α)
          + (1 / (2 * ε)) * Real.log (4 * Real.log (2 * α) * Real.sqrt α)
          + Real.pi / ε * (Real.sqrt (1 + α ^ 2) - α) := by
  have hlog := kaiser_log_identity α hα
  have hεne : ε ≠ 0 := hε.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold kaiserN
  rw [hlog]
  field_simp [hεne, hpine]
  ring

/-- The correction `√(1+α²) − α` is nonnegative; Eq. (44), Section IV.A, p. 15. -/
theorem sqrt_one_add_sq_ge_alpha (α : ℝ) (hα : 0 ≤ α) :
    α ≤ Real.sqrt (1 + α ^ 2) := by
  have h1 : α ^ 2 ≤ 1 + α ^ 2 := by linarith [sq_nonneg α]
  have h2 : Real.sqrt (α ^ 2) ≤ Real.sqrt (1 + α ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq hα] at h2

/-- The correction `√(1+α²) − α` is at most `1`; Eq. (44), Section IV.A, p. 15.
This is the elementary bound behind the `O(ε⁻¹)` width correction. -/
theorem sqrt_one_add_sq_le_alpha_add_one (α : ℝ) (hα : 0 ≤ α) :
    Real.sqrt (1 + α ^ 2) ≤ α + 1 := by
  have h1 : 1 + α ^ 2 ≤ (α + 1) ^ 2 := by nlinarith [sq_nonneg α]
  have h2 : Real.sqrt (1 + α ^ 2) ≤ Real.sqrt ((α + 1) ^ 2) := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (by linarith)] at h2

/-! ## Claim c006: prolate spheroidal window -/

/-- Eq. (57), Section IV.C, p. 17, first-order Slepian expansion (Ref. [23],
Eq. (13)): `δ = 4√(πc) e^{−2c} [1 − 3/(32c) + O(c⁻²)]`.  The `O(c⁻²)` term is
omitted, so this is the first-order truncation. -/
noncomputable def slepianErrorFirstOrder (c : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * c) * Real.exp (-(2 * c)) * (1 - 3 / (32 * c))

/-- Eq. (58), Section IV.C, p. 17: Slepian's second-order expansion (Ref. [22],
Eq. (4.4)), with `2334/3! = 389`:
`δ = 4√(πc) e^{−2c} [1 − 3/(32c) − 389/(2¹¹ c²) + O(c⁻³)]`. -/
noncomputable def slepianError (c : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * c) * Real.exp (-(2 * c)) *
    (1 - 3 / (32 * c) - 389 / ((2 : ℝ) ^ 11 * c ^ 2))

/-- Eq. (59), Section IV.C, p. 17, and Appendix B p. 37: the corrected
prolate-spheroidal expansion
`δ = 4√(πc) e^{−2c} [1 − 7/(16c) − 91/(2⁹ c²) + O(c⁻³)]`. -/
noncomputable def correctedProlateError (c : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * c) * Real.exp (-(2 * c)) *
    (1 - 7 / (16 * c) - 91 / ((2 : ℝ) ^ 9 * c ^ 2))

/-- The leading prolate-spheroidal error `4√(πc) e^{−2c}`, i.e. Eqs. (57)–(59)
without the bracket corrections.  Section IV.C, p. 17. -/
noncomputable def leadingProlateError (c : ℝ) : ℝ :=
  4 * Real.sqrt (Real.pi * c) * Real.exp (-(2 * c))

/-- The simplification `2334/3! = 389` used in Eq. (58), Section IV.C, p. 17. -/
theorem slepian_coefficient_simplification : (2334 : ℝ) / 6 = 389 := by
  norm_num

/-- The bracket difference between Slepian's Eq. (58) and the corrected Eq. (59).
Section IV.C, p. 17: the corrected bracket subtracts more, and the difference is
`11/(32c) − 25/(2048 c²)`. -/
theorem slepian_bracket_sub_corrected (c : ℝ) (hc : 0 < c) :
    (1 - 3 / (32 * c) - 389 / ((2 : ℝ) ^ 11 * c ^ 2))
        - (1 - 7 / (16 * c) - 91 / ((2 : ℝ) ^ 9 * c ^ 2))
      = 11 / (32 * c) - 25 / (2048 * c ^ 2) := by
  have hcne : c ≠ 0 := hc.ne'
  field_simp [hcne]
  ring

/-- The common prefactor of Eqs. (57)–(59) is strictly positive for `c > 0`.
Section IV.C, p. 17. -/
theorem prolate_prefactor_pos (c : ℝ) (hc : 0 < c) :
    0 < 4 * Real.sqrt (Real.pi * c) * Real.exp (-(2 * c)) := by
  have hpic : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  have hs : 0 < Real.sqrt (Real.pi * c) := Real.sqrt_pos.2 hpic
  have he : 0 < Real.exp (-(2 * c)) := Real.exp_pos _
  positivity

/-- **Claim c006, corrected expansion dominates Slepian's for large `c`.**
Section IV.C, pp. 17–18: since the corrected bracket is smaller by
`11/(32c) − 25/(2048c²)`, for `c > 25/704` the corrected Eq. (59) gives a
strictly smaller error than Slepian's Eq. (58). -/
theorem corrected_better_than_slepian (c : ℝ) (hc : 0 < c) (h : (25 : ℝ) / 704 < c) :
    correctedProlateError c < slepianError c := by
  have hpos := prolate_prefactor_pos c hc
  have hdiff := slepian_bracket_sub_corrected c hc
  have hkey : (0 : ℝ) < 11 / (32 * c) - 25 / (2048 * c ^ 2) := by
    rw [show 11 / (32 * c) - 25 / (2048 * c ^ 2)
          = (1 / c) * (11 / 32 - 25 / (2048 * c)) by
        field_simp [hc.ne']]
    have hc25 : 25 / (2048 * c) < 11 / 32 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [h]
    exact mul_pos (by positivity) (by linarith)
  have hbracket : (1 - 7 / (16 * c) - 91 / ((2 : ℝ) ^ 9 * c ^ 2))
      < (1 - 3 / (32 * c) - 389 / ((2 : ℝ) ^ 11 * c ^ 2)) := by
    linarith [hdiff, hkey]
  unfold correctedProlateError slepianError
  simpa using mul_lt_mul_of_pos_left hbracket hpos

/-- **Claim c006, corrected expansion beats the leading term.**  Since the
bracket `1 − 7/(16c) − 91/(2⁹c²)` is strictly below `1` for `c > 0`, the
corrected Eq. (59) is strictly smaller than the leading `4√(πc)e^{−2c}`.
Section IV.C, p. 17. -/
theorem corrected_better_than_leading (c : ℝ) (hc : 0 < c) :
    correctedProlateError c < leadingProlateError c := by
  have hpos := prolate_prefactor_pos c hc
  have hbracket : (1 - 7 / (16 * c) - 91 / ((2 : ℝ) ^ 9 * c ^ 2)) < 1 := by
    have h1 : 0 < 7 / (16 * c) := by positivity
    have h2 : 0 < 91 / ((2 : ℝ) ^ 9 * c ^ 2) := by positivity
    linarith
  unfold correctedProlateError leadingProlateError
  have h := mul_lt_mul_of_pos_left hbracket hpos
  rw [mul_one] at h
  exact h

/-- Eq. (60), Section IV.C, p. 18: the prolate-spheroidal confidence width
`N = c/ε`. -/
noncomputable def prolateN (ε c : ℝ) : ℝ := c / ε

/-- **Claim c006, same leading cost as Kaiser (Eq. (60)).**  Section IV.C,
p. 18: with `c = ln(1/δ)/2` the prolate width is `ln(1/δ)/(2ε)`, exactly the
leading Kaiser cost from Eq. (44).  This is the paper's statement that the
prolate window improves the error but not the leading cost. -/
theorem prolate_kaiser_same_leading_cost (ε δ : ℝ) (hε : 0 < ε) (_hδ : 0 < δ) :
    prolateN ε (Real.log (1 / δ) / 2) = Real.log (1 / δ) / (2 * ε) ∧
      Real.pi / ε * (Real.log (1 / δ) / (2 * Real.pi))
        = Real.log (1 / δ) / (2 * ε) := by
  constructor
  · unfold prolateN
    field_simp [hε.ne']
  · have hεne : ε ≠ 0 := hε.ne'
    have hpine : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp [hεne, hpine]

end Qatlib.Papers.RapidState24.MainResults.PhaseEstimationWindows
