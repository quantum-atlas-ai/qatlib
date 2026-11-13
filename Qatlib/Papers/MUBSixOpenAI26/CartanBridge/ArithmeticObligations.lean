/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — numerical literal and scalar comparison helpers

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`rounding.tex`.

This file proves a rational approximation bound for π and a conditional real
inequality motivated by Appendix A. It does not resolve the dimension-six MUB
existence problem or verify a certificate or a binary64 implementation.

The two numerical ingredients are:

* `round:pi-error` (lines 151--179): the binary64 literal
  `0x1.921fb54442d18p+1` is the rational `π̂ = 884279719003555 / 281474976710656`,
  and the theorem here proves `|π̂ − π| < 2·10⁻¹⁶`. The proof only needs the
  Mathlib decimal enclosure `3.14159265358979323846 < π < 3.14159265358979323847`
  and exact rational arithmetic on `π̂`; no Machin series needs to be replayed,
  because this statement is the numerical endpoint, not the derivation.

* `round:ell-upper-code` (lines 938--957): the code expression
  `(dotv + 10⁻¹⁰ s_z) + ((√un + 10⁻¹⁰)(√res + 10⁻¹⁰ s_z))/gap`
  dominates `Uz + Unorm * rnorm / gap` under explicit scalar comparison and
  nonnegativity hypotheses and `gap > 0`. All quantities are arbitrary reals;
  the lemma proves monotonicity of multiplication and division. It does not
  identify these scalars with an inverse quadratic form or prove the comparison
  hypotheses from floating-point computations.

The full arithmetic contract of the paper also includes the degree-18/19
`expair` polynomial error (`round:expair`) and the tensor/root invariant bounds
(`round:tensor-c`, `round:root-invariants`). Those depend on a concrete binary64
implementation not modeled here. The field `expair_budget` of
`ArithmeticCompilerObligations` proves only `0 ≤ 6·10⁻¹⁴`, using the paper's
numeric budget (line 192); it does not state any approximation error bound.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- The stored binary64 approximation of π, `0x1.921fb54442d18p+1`, as an exact
rational (`rounding.tex` line 154). -/
noncomputable def piHat : ℝ := 884279719003555 / 281474976710656

/-- Equation `round:pi-error` (`rounding.tex` lines 177--179): the stored
literal differs from π by less than `2·10⁻¹⁶`. -/
theorem pi_hat_error : |piHat - Real.pi| < 2 / 10 ^ 16 := by
  have hlt : piHat < (3.14159265358979323846 : ℝ) := by
    norm_num [piHat]
  have hlow : (3.1415926535897931 : ℝ) < piHat := by
    norm_num [piHat]
  have hpi_lt : Real.pi < (3.14159265358979323847 : ℝ) := Real.pi_lt_d20
  have hpi_gt : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hple : piHat < Real.pi := by linarith
  have hnum : (3.14159265358979323847 : ℝ) - 3.1415926535897931 < 2 / 10 ^ 16 := by
    norm_num
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- The code's fixed outward slack `10⁻¹⁰` used in `round:ell-upper-code`. -/
noncomputable def codeEps10 : ℝ := 1 / 10 ^ 10

/-- Conditional scalar inequality motivated by `round:ell-upper-code`
(`rounding.tex` lines 938--943). Given the three comparison bounds, nonnegative
`sz`, `Unorm`, and `rnorm`, and positive `gap`, the enlarged expression dominates
`Uz + Unorm * rnorm / gap`. No matrix or floating-point semantics are asserted. -/
theorem ell_upper_code_dominates
    (dotv un res gap sz Uz Unorm rnorm : ℝ)
    (hsz : 0 ≤ sz) (hgap : 0 < gap)
    (hUz : Uz ≤ dotv + codeEps10 * sz)
    (hUn : Unorm ≤ Real.sqrt un + codeEps10)
    (hRn : rnorm ≤ Real.sqrt res + codeEps10 * sz)
    (hUn0 : 0 ≤ Unorm) (hRn0 : 0 ≤ rnorm) :
    Uz + Unorm * rnorm / gap ≤
      dotv + codeEps10 * sz +
        (Real.sqrt un + codeEps10) * (Real.sqrt res + codeEps10 * sz) / gap := by
  have heps : 0 ≤ codeEps10 := by norm_num [codeEps10]
  have hA : 0 ≤ Real.sqrt un + codeEps10 := by
    linarith [Real.sqrt_nonneg un]
  have hB : 0 ≤ Real.sqrt res + codeEps10 * sz := by
    have : 0 ≤ codeEps10 * sz := mul_nonneg heps hsz
    linarith [Real.sqrt_nonneg res]
  have hprod : Unorm * rnorm ≤
      (Real.sqrt un + codeEps10) * (Real.sqrt res + codeEps10 * sz) :=
    mul_le_mul hUn hRn hRn0 hA
  have hquot : Unorm * rnorm / gap ≤
      ((Real.sqrt un + codeEps10) * (Real.sqrt res + codeEps10 * sz)) / gap :=
    div_le_div_of_nonneg_right hprod hgap.le
  linarith

/-- Package of a π-literal error bound, nonnegativity of a numerical budget,
and a conditional scalar domination inequality. Despite the historical name,
this structure does not specify compiler correctness or exponential errors. -/
structure ArithmeticCompilerObligations where
  /-- `round:pi-error`: the stored π literal is within `2·10⁻¹⁶`. -/
  pi_error : |piHat - Real.pi| < 2 / 10 ^ 16
  /-- Nonnegativity of the numeric budget from line 192; this field contains no
  exponential approximation or implementation error assertion. -/
  expair_budget : 0 ≤ (6 : ℝ) / 10 ^ 14
  /-- `round:ell-upper-code`: monotone domination by the stored code expression. -/
  ell_upper_code : ∀ (dotv un res gap sz Uz Unorm rnorm : ℝ),
    0 ≤ sz → 0 < gap →
    Uz ≤ dotv + codeEps10 * sz →
    Unorm ≤ Real.sqrt un + codeEps10 →
    rnorm ≤ Real.sqrt res + codeEps10 * sz →
    0 ≤ Unorm → 0 ≤ rnorm →
    Uz + Unorm * rnorm / gap ≤
      dotv + codeEps10 * sz +
        (Real.sqrt un + codeEps10) * (Real.sqrt res + codeEps10 * sz) / gap

/-- Construct the package from the π approximation theorem, numeric
nonnegativity, and the conditional scalar inequality. -/
def arithmeticCompilerObligations : ArithmeticCompilerObligations where
  pi_error := pi_hat_error
  expair_budget := by norm_num
  ell_upper_code := ell_upper_code_dominates

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
