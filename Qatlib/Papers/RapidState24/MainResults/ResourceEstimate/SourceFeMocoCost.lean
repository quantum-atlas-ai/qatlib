/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# RapidState24 — FeMoco Toffoli resource estimate

Paper: Berry et al., *Rapid initial state preparation for the quantum simulation
of strongly correlated molecules*, arXiv:2409.11748v1 (2024).

This file covers claim `c009`: Section VII, pp. 28–33, Table II (p. 33), and the
comparison paragraph on p. 33.

The paper reports, for the FeMo cofactor with the Li Hamiltonian and THC block
encoding at a 95% confidence interval of half-width `ε = 1.0 × 10⁻³` Hartree:

* total QPE cost `7.27 × 10¹⁰` Toffoli gates, quoted as `7.3 × 10¹⁰`;
* `3.2 × 10¹⁰` for Ref. [27], hence "about 2.3 times higher";
* an LCU 1-norm reduced from `λ = 1201.5` (Ref. [27]) to `λ = 781.8172`,
  a factor `≈ 1.54` (and "up to a factor of 2" for symmetry shifting);
* only `2` QPE samples, because the MPS overlap is `0.95`;
* MPS preparation costs `7.33 × 10⁸` Toffolis, negligible against the QPE cost.

The Lean content is the exact arithmetic of these reported numbers.  The
resource ledger itself is numerical input from the paper, so the theorems below
are stated as explicit rational inequalities, not derived from a symbolic cost
model.

Related library vocabulary:
`Qatlib.Concepts.ResourceBounds.AsymBounds` supplies uniform
growth-rate predicates, not these concrete FeMoco counts.
-/

namespace Qatlib.Papers.RapidState24.MainResults.ResourceEstimate

set_option autoImplicit false

/-- Table II, p. 33: total 95%-confidence QPE cost for FeMoco (THC), in
Toffoli gates: `7.27 × 10¹⁰`. -/
noncomputable def femocoQpeCost95 : ℝ := 72700000000

/-- Table II, p. 33 and the comparison paragraph on p. 33: Ref. [27]'s THC
Toffoli cost, `3.2 × 10¹⁰`. -/
noncomputable def femocoRef27Cost : ℝ := 32000000000

/-- Table II, p. 33: MPS preparation Toffoli cost for FeMoco, `7.33 × 10⁸`. -/
noncomputable def femocoMpsToffolis : ℝ := 733000000

/-- p. 33: the LCU 1-norm used here, `λ = 781.8172`. -/
noncomputable def femocoLambda : ℝ := 7818172 / 10000

/-- p. 33: the LCU 1-norm of Ref. [27], `λ = 1201.5`. -/
noncomputable def femocoRef27Lambda : ℝ := 12015 / 10

/-- p. 33: the factor by which symmetry shifting reduced `λ`,
`1201.5 / 781.8172`. -/
noncomputable def femocoLambdaFactor : ℝ := 12015 / 10 / (7818172 / 10000)

/-- p. 33: the ratio of the reported cost to Ref. [27]'s cost,
`7.27 × 10¹⁰ / (3.2 × 10¹⁰)`. -/
noncomputable def femocoCostRatio : ℝ := 72700000000 / 32000000000

/-- p. 32: the number of QPE samples needed for FeMoco, `2`. -/
def femocoSamples : ℕ := 2

/-- **Claim c009, the reported cost rounds to `7.3 × 10¹⁰`.**  Section VII,
p. 33 and the abstract p. 1: the Table II value `7.27 × 10¹⁰` lies strictly
between `7.2 × 10¹⁰` and `7.4 × 10¹⁰`, so one-decimal rounding gives `7.3 × 10¹⁰`. -/
theorem femoco_cost_rounds_to_seven_point_three :
    (72 : ℝ) * 10 ^ 9 < femocoQpeCost95 ∧ femocoQpeCost95 < (74 : ℝ) * 10 ^ 9 := by
  unfold femocoQpeCost95
  constructor <;> norm_num

/-- **Claim c009, "about 2.3 times" Ref. [27].**  Section VII, p. 33: the
reported `7.27 × 10¹⁰` is `2.271875` times Ref. [27]'s `3.2 × 10¹⁰`, which the
paper quotes as "about 2.3 times higher". -/
theorem femoco_cost_ratio_about_two_point_three :
    femocoCostRatio = 727 / 320 ∧
      (2.27 : ℝ) < femocoCostRatio ∧ femocoCostRatio < 2.3 := by
  unfold femocoCostRatio
  constructor
  · norm_num
  constructor <;> norm_num

/-- **Claim c009, MPS preparation is negligible in the total.**  Section VII,
Table II p. 33: `7.33 × 10⁸` Toffolis of MPS preparation is less than a tenth
of the `7.27 × 10¹⁰` total QPE cost. -/
theorem femoco_mps_cost_small :
    femocoMpsToffolis < femocoQpeCost95 / 10 := by
  unfold femocoMpsToffolis femocoQpeCost95
  norm_num

/-- **Claim c009, symmetry-shifting reduction of `λ` is about `1.54`.**
Section VII, p. 33: `1201.5 / 781.8172` lies strictly between `1.53` and
`1.54`, matching the quoted factor `≈ 1.54`. -/
theorem femoco_lambda_factor_about_one_point_five_four :
    (1.53 : ℝ) < femocoLambdaFactor ∧ femocoLambdaFactor < 1.54 := by
  unfold femocoLambdaFactor
  constructor <;> norm_num

/-- **Claim c009, the `λ` reduction is at most a factor two.**  Section VII,
p. 33: symmetry shifting reduces the LCU 1-norm by "up to a factor of 2"; for
FeMoco THC the actual factor `1.5368…` is strictly below two. -/
theorem femoco_lambda_factor_lt_two : femocoLambdaFactor < 2 := by
  unfold femocoLambdaFactor
  norm_num

/-- **Claim c009, two QPE samples.**  Section VII, p. 32: high MPS overlap
means only two QPE samples are required for FeMoco. -/
theorem femoco_two_samples : femocoSamples = 2 := rfl

/-- The stated `λ` value is positive and reduced relative to Ref. [27].
Section VII, p. 33. -/
theorem femoco_lambda_reduced :
    0 < femocoLambda ∧ femocoLambda < femocoRef27Lambda := by
  unfold femocoLambda femocoRef27Lambda
  constructor <;> norm_num

end Qatlib.Papers.RapidState24.MainResults.ResourceEstimate
