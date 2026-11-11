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
# MUBSixOpenAI26 — Appendix A arithmetic/compiler obligations

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`rounding.tex`.

Two displayed obligations are transcribed here:

* `round:pi-error` (lines 151--179): the binary64 literal
  `0x1.921fb54442d18p+1` is the rational `π̂ = 884279719003555 / 281474976710656`,
  and `|π̂ − π| < 1.225418·10⁻¹⁶ < 2·10⁻¹⁶`. The proof below only needs the
  Mathlib decimal enclosure `3.14159265358979323846 < π < 3.14159265358979323847`
  and exact rational arithmetic on `π̂`; no Machin series needs to be replayed,
  because this statement is the numerical endpoint, not the derivation.

* `round:ell-upper-code` (lines 938--957): the code expression
  `(dotv + 10⁻¹⁰ s_z) + ((√un + 10⁻¹⁰)(√res + 10⁻¹⁰ s_z))/gap`
  is an upper bound for the exact inverse quadratic form once the stored
  quantities dominate the exact ones and `gap > 0`. The exact resolvent identity
  and the binary64 error estimates are the paper's hypotheses (recorded as the
  comparison hypotheses `hUz`, `hUn`, `hRn`); the Lean lemma isolates and proves
  the monotone-division step that turns those comparisons into the displayed
  code upper bound, including the nonnegativity needed for the denominator.

The full arithmetic contract of the paper also includes the degree-18/19
`expair` polynomial error (`round:expair`) and the tensor/root invariant bounds
(`round:tensor-c`, `round:root-invariants`). Those depend on a concrete binary64
implementation that this repository does not model; they are recorded as the
opaque field `expair_budget` of `ArithmeticCompilerObligations` with the paper's
numeric value `ε_exp = 6·10⁻¹⁴` (line 192).
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

/-- Equation `round:ell-upper-code` (`rounding.tex` lines 938--943): if the
stored dot product dominates `U^*z`, the stored `√un` dominates `‖U‖`, the
stored `√res` dominates `‖r‖`, and `gap > 0`, then the displayed code expression
is an upper bound for `U^*z + ‖U‖‖r‖/gap` (the exact right side of
`round:resolvent-residual`), with all outward `10⁻¹⁰ s_z` allowances. -/
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

/-- Appendix A arithmetic/compiler contract, restricted to the two obligations
that the paper states as the endpoint inequalities used by Stage C and by the
spectral bootstrap. `expair_budget` is the paper's common unit-exponential
error (line 192), left opaque because no binary64 `expair` exists in this
library. -/
structure ArithmeticCompilerObligations where
  /-- `round:pi-error`: the stored π literal is within `2·10⁻¹⁶`. -/
  pi_error : |piHat - Real.pi| < 2 / 10 ^ 16
  /-- `round:exp-budget`: the common exponential error used everywhere in the
  certificate (line 192), stated as a nonnegative numeric budget. -/
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

/-- The provable part of the arithmetic/compiler contract. -/
def arithmeticCompilerObligations : ArithmeticCompilerObligations where
  pi_error := pi_hat_error
  expair_budget := by norm_num
  ell_upper_code := ell_upper_code_dominates

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
