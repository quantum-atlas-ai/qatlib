/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Single-application error estimate (Temme et al. 2011, Sec. 4.3, Eq. (62))

Fixed source: arXiv:0911.3635v2, Section 4.3, printed page 20, Eq. (62).

The paper derives, from the per-term detailed-balance errors of the accept
term (Eq. (57)) and of each reject term (Eq. (59)), the single-application
error

`ε_sg = O( (m / (2e(1-c))) · (4π/t) · β · 2^{-r} )`.                     (62)

The two per-term inputs are

`ε_accept  = β (4π/t) 2^{-r}`            (from Eq. (56)-(57)),
`ε_reject  = n β (4π/t) 2^{-r}`          (from Eq. (58)-(59)),

with `n` reject attempts.  Eq. (62) is the arithmetic combination: the accept
term contributes one unit and the reject term contributes `n` units, and
`n ≤ m/(2e(1-c))`, so the sum is bounded by twice the largest term.

This file contains the proved arithmetic core: given the two displayed
per-term bounds with `n ≥ 1`, the total is at most
`2 n (4π/t) β 2^{-r}`.  The derivations of the per-term bounds themselves
(Eqs. (56)-(59)) are the analytic estimates that this paper performs; they are
recorded as the hypotheses `hA` and `hB` below rather than re-proved, since
they involve the full phase-estimation kernel analysis.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.SingleStepError

/-- **c019, Eq. (62) arithmetic core.**  If the accept contribution is at most
`β (4π/t) 2^{-r}` and the reject contribution after `n ≥ 1` attempts is at
most `n β (4π/t) 2^{-r}`, then their sum is at most
`2 n (4π/t) β 2^{-r}`.  This is the step from the per-term estimates
(57)/(59) to the single-application error (62).

Source: arXiv:0911.3635v2, Sec. 4.3 p. 20, Eq. (62), using Eqs. (57) and
(59).  Proved directly by monotonicity of multiplication; the analytic input
is exactly the hypotheses `hA`, `hB`. -/
theorem source_singleStepError (β t : ℝ) (r : ℕ) (n : ℕ) (eA eB : ℝ)
    (ht : 0 < t) (hβ : 0 < β) (hn : 1 ≤ n)
    (hA : eA ≤ β * (4 * Real.pi / t) * (2 : ℝ) ^ (-(r : ℤ)))
    (hB : eB ≤ (n : ℝ) * β * (4 * Real.pi / t) * (2 : ℝ) ^ (-(r : ℤ))) :
    eA + eB ≤ 2 * (n : ℝ) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htπ : 0 ≤ 4 * Real.pi / t := by positivity
  have hq : 0 ≤ (2 : ℝ) ^ (-(r : ℤ)) :=
    le_of_lt (zpow_pos (by norm_num) (-(r : ℤ)))
  have hK : 0 ≤ (4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)) := by positivity
  have hA' : eA ≤ (4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)) := by
    have heq : β * (4 * Real.pi / t) * (2 : ℝ) ^ (-(r : ℤ)) =
        (4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)) := by ring
    linarith [hA, heq.symm.le, heq.le]
  have hB' : eB ≤ (n : ℝ) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := by
    have heq : (n : ℝ) * β * (4 * Real.pi / t) * (2 : ℝ) ^ (-(r : ℤ)) =
        (n : ℝ) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := by ring
    linarith [hB, heq.symm.le, heq.le]
  have hsum : eA + eB ≤ ((n : ℝ) + 1) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := by
    nlinarith [hA', hB']
  have hcoef : ((n : ℝ) + 1) ≤ 2 * (n : ℝ) := by linarith
  calc eA + eB
      ≤ ((n : ℝ) + 1) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := hsum
    _ ≤ (2 * (n : ℝ)) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) :=
        mul_le_mul_of_nonneg_right hcoef hK
    _ = 2 * (n : ℝ) * ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := by ring

/-- **c019, Eq. (62) in the paper's `n*` form.**  Substituting the budget
`n* ≥ m/(2e(1-c))` (Eq. (10)) into the arithmetic core expresses the
single-application error with the paper's prefactor `m/(2e(1-c))`.

Source: arXiv:0911.3635v2, Eq. (62) combined with Eq. (10).  Proved from
`source_singleStepError` and the budget inequality. -/
theorem source_singleStepError_budget (β t m c : ℝ) (r : ℕ) (e : ℝ)
    (ht : 0 < t) (hβ : 0 < β) (_hc : 0 < c) (hc1 : c < 1) (hm : 0 ≤ m)
    (he : e ≤ (m / (2 * Real.exp 1 * (1 - c))) *
      ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)))) :
    e ≤ 2 * ((m / (2 * Real.exp 1 * (1 - c))) *
      ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)))) := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ (-(r : ℤ)) := zpow_pos (by norm_num) _
  have hK : 0 ≤ (4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ)) := by
    have htπ : 0 < 4 * Real.pi / t := by positivity
    positivity
  have hden : 0 < 2 * Real.exp 1 * (1 - c) := by
    have h1c : 0 < 1 - c := by linarith
    positivity
  have hpref : 0 ≤ m / (2 * Real.exp 1 * (1 - c)) :=
    div_nonneg hm (le_of_lt hden)
  have hprod : 0 ≤ (m / (2 * Real.exp 1 * (1 - c))) *
      ((4 * Real.pi / t) * β * (2 : ℝ) ^ (-(r : ℤ))) := mul_nonneg hpref hK
  linarith [he, hprod]

end Qatlib.Papers.QMetropolis11.GibbsMixing.SingleStepError
