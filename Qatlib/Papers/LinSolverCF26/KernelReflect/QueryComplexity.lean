/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# `QueryComplexity` — degree bound, constant factor 1, and the `≈ 48` analytic cost

Source: P. C. S. Costa, A. M. Dalzell, D. An, D. W. Berry,
*Constant Factor Analysis of Optimal Quantum Linear Solvers in Practice*,
arXiv:2604.22185v2 (fixed version), Section III A, Appendix A Eq. (A16), and
Section III B Eq. (19).

With `Δ̃ = κ⁻¹`, Eq. (A16) requires a QSVT degree `l ≤ (1/(2Δ̃)) ln(2/η)`,
i.e. `l ≤ (κ/2) ln(2/η)`. The paper chooses `η_KR = ε/√2` when the solution
norm is known, giving the rigorous bound `2l ≤ κ ln(2√2/ε)` with constant
factor `1`; numerically `ln(2√2/0.01) ≈ 5.64` and `ln(2√2/0.001) ≈ 7.94`,
matching the "`5.64κ` and `7.94κ`" values quoted in the text.

For the unknown-norm regime Eq. (19) gives the rigorous upper bound
`cost/κ ≤ 6 ln κ + 6 + 1.07 ln(1/ε) + (6 + 3 ln κ)/κ`, whose value at
`κ = 320`, `ε = 10⁻³` is `≈ 48`. We prove the algebraic identity, the two
decimal logarithm estimates, and the numerical `≈ 48` statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinSolverCF26.KernelReflect.QueryComplexity

/-- Eq. (A16): with `Δ̃ = 1/κ`, the sufficient QSVT degree for target error
`η` is `l = (1/(2Δ̃)) ln(2/η) = (κ/2) ln(2/η)`. -/
def degreeBound (κ η : ℝ) : ℝ := (κ / 2) * Real.log (2 / η)

/-- Known norm, `η_KR = ε/√2`: the degree cost is `2l = κ ln(2√2/ε)`, i.e. the
query complexity is `κ log(2√2/ε)` with constant factor exactly one
(the `(1+O(ε))` statement of Section III A). -/
theorem two_degreeBound_known_norm {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    2 * degreeBound κ (ε / Real.sqrt 2) =
      κ * Real.log (2 * Real.sqrt 2 / ε) := by
  unfold degreeBound
  have harg : 2 / (ε / Real.sqrt 2) = 2 * Real.sqrt 2 / ε := by
    rw [div_div_eq_mul_div]
  rw [harg]
  ring

/-- `ln(2√2/(1/100)) = (7/2) ln 2 + 2 ln 5`. -/
lemma log_eps_1e2 :
    Real.log (2 * Real.sqrt 2 / (1 / 100)) =
      (7 / 2) * Real.log 2 + 2 * Real.log 5 := by
  have harg : 2 * Real.sqrt 2 / (1 / 100) = 2 ^ 3 * 5 ^ 2 * Real.sqrt 2 := by
    field_simp
    ring
  rw [harg, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_sqrt (by norm_num)]
  ring

/-- `ln(2√2/(1/1000)) = (9/2) ln 2 + 3 ln 5`. -/
lemma log_eps_1e3 :
    Real.log (2 * Real.sqrt 2 / (1 / 1000)) =
      (9 / 2) * Real.log 2 + 3 * Real.log 5 := by
  have harg : 2 * Real.sqrt 2 / (1 / 1000) = 2 ^ 4 * 5 ^ 3 * Real.sqrt 2 := by
    field_simp
    ring
  rw [harg, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_sqrt (by norm_num)]
  ring

/-- The quoted value `5.64` for `ε = 10⁻²`: `5.64 < ln(2√2/ε) < 5.65`. -/
theorem log_bound_eps_1e2 :
    5.64 < Real.log (2 * Real.sqrt 2 / (1 / 100)) ∧
      Real.log (2 * Real.sqrt 2 / (1 / 100)) < 5.65 := by
  rw [log_eps_1e2]
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_five_gt_d9, Real.log_five_lt_d9]

/-- The quoted value `7.94` for `ε = 10⁻³`: `7.94 < ln(2√2/ε) < 7.95`. -/
theorem log_bound_eps_1e3 :
    7.94 < Real.log (2 * Real.sqrt 2 / (1 / 1000)) ∧
      Real.log (2 * Real.sqrt 2 / (1 / 1000)) < 7.95 := by
  rw [log_eps_1e3]
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_five_gt_d9, Real.log_five_lt_d9]

/-- Eq. (19): the rigorous unknown-norm upper bound on `cost/κ`. -/
def unknownNormBound (κ ε : ℝ) : ℝ :=
  6 * Real.log κ + 6 + 1.07 * Real.log (1 / ε) + (6 + 3 * Real.log κ) / κ

/-- `ln 320 = 6 ln 2 + ln 5`. -/
lemma log_320 : Real.log (320 : ℝ) = 6 * Real.log 2 + Real.log 5 := by
  have harg : (320 : ℝ) = 2 ^ 6 * 5 := by norm_num
  rw [harg, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

/-- `ln 1000 = 3 ln 2 + 3 ln 5`. -/
lemma log_1000 : Real.log (1000 : ℝ) = 3 * Real.log 2 + 3 * Real.log 5 := by
  have harg : (1000 : ℝ) = 2 ^ 3 * 5 ^ 3 := by norm_num
  rw [harg, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]
  ring

/-- Eq. (19) at `κ = 320`, `ε = 10⁻³`: the bound evaluates to `≈ 48`
(here `47 ≤ bound ≤ 49`), as stated in Section III B. -/
theorem unknownNormBound_kappa320_eps1e3 :
    47 ≤ unknownNormBound 320 (1 / 1000) ∧
      unknownNormBound 320 (1 / 1000) ≤ 49 := by
  unfold unknownNormBound
  have h1 : (1 : ℝ) / (1 / 1000) = 1000 := by norm_num
  rw [h1, log_320, log_1000]
  constructor <;>
    nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.log_five_gt_d9, Real.log_five_lt_d9]

end Qatlib.Papers.LinSolverCF26.KernelReflect.QueryComplexity
