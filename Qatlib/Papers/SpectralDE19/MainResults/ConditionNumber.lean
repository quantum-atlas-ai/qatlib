/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Condition number of the collocation system

Fixed source: arXiv:1901.00961, *Quantum spectral methods for differential
equations*, Lemma 4 (§5, p. 11, eq. (5.1)), proof pp. 11–14.

The collocation matrix `L` of (3.16) is a block matrix over
`C^{m+p} ⊗ C^d ⊗ C^{n+1}` built from `L_1 = D_n`, `L_2(A_h) = −A_h ⊗ P_n`,
`L_3`, `L_4`, `L_5`.  The paper proves two operator-norm estimates:

* `‖L‖ ≤ (n+1)^3`                                        (eq. (5.14)), and
* `‖L⁻¹‖ ≤ (πm + p + 1)(n+1)^{1/2}(2κ_V + e‖γ‖)`          (eq. (5.41)),

and multiplies them (eq. (5.42)) to obtain Lemma 4,

  `κ_L = ‖L‖‖L⁻¹‖ ≤ (πm + p + 2)(n+1)^{3.5}(2κ_V + e‖γ‖)`.

This file defines the condition number of a continuous linear equivalence and
proves the paper's *assembly* (5.42) rigorously, including the exponent algebra
`(n+1)^3 · (n+1)^{1/2} = (n+1)^{7/2}`.  The entry-level norm estimates (5.14)
and (5.41) — which are the paper's proven intermediate bounds, not new
assumptions — enter as hypotheses with their equation numbers.  Their
formalisation would require the concrete block structure of `L` (matrices over
the tensor registers); that part is not formalised here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpectralDE19.MainResults

/-- The condition number `κ(L) = ‖L‖·‖L⁻¹‖` of a continuous linear equivalence. -/
noncomputable def conditionNumber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) : ℝ :=
  ‖(L : E →L[ℝ] E)‖ * ‖(L.symm : E →L[ℝ] E)‖

/-- **SpectralDE19, Lemma 4, eq. (5.1).**  The condition number of the
collocation system is at most
`(πm + p + 2)(n+1)^{3.5}(2κ_V + e‖γ‖)`.

The hypotheses `hL` and `hLi` are the paper's bounds (5.14) and (5.41) on the
norms of `L` and `L⁻¹`; the proof below is the paper's final multiplication
(5.42). -/
theorem lemma4_condition_number_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E ≃L[ℝ] E) (m p n : ℕ) (κV γnorm : ℝ)
    (hκV : 1 ≤ κV) (hγ : 0 ≤ γnorm)
    (hL : ‖(L : E →L[ℝ] E)‖ ≤ ((n : ℝ) + 1) ^ 3)
    (hLi : ‖(L.symm : E →L[ℝ] E)‖ ≤
      (Real.pi * (m : ℝ) + (p : ℝ) + 1) * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)
        * (2 * κV + Real.exp 1 * γnorm)) :
    conditionNumber L ≤
      (Real.pi * (m : ℝ) + (p : ℝ) + 2) * ((n : ℝ) + 1) ^ (7 / 2 : ℝ)
        * (2 * κV + Real.exp 1 * γnorm) := by
  set A : ℝ := ‖(L : E →L[ℝ] E)‖ with hA
  set B : ℝ := ‖(L.symm : E →L[ℝ] E)‖ with hB
  set R : ℝ := 2 * κV + Real.exp 1 * γnorm with hR
  have hR0 : 0 ≤ R := by
    rw [hR]; positivity
  have hA0 : 0 ≤ A := by rw [hA]; exact norm_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact norm_nonneg _
  have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- The exponent algebra of (5.14)·(5.41): `(n+1)^3 · (n+1)^{1/2} = (n+1)^{7/2}`.
  have hpow : ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)
      = ((n : ℝ) + 1) ^ (7 / 2 : ℝ) := by
    have h1 : ((n : ℝ) + 1) ^ 3 = ((n : ℝ) + 1) ^ ((3 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    rw [h1, ← Real.rpow_add hbase]
    norm_num
  -- Multiply the two estimates.
  have hAB : A * B ≤ ((n : ℝ) + 1) ^ 3
      * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * R) :=
    mul_le_mul hL hLi hB0 (by positivity)
  have hAB' : A * B ≤ ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)
      * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * R) := by
    calc A * B
        ≤ ((n : ℝ) + 1) ^ 3
            * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * R) := hAB
      _ = ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)
            * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * R) := by ring
  calc conditionNumber L = A * B := by rw [conditionNumber, hA, hB]
    _ ≤ ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)
          * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * R) := hAB'
    _ = ((n : ℝ) + 1) ^ (7 / 2 : ℝ) * ((Real.pi * (m : ℝ) + (p : ℝ) + 1) * R) := by
          rw [hpow]
    _ ≤ ((n : ℝ) + 1) ^ (7 / 2 : ℝ) * ((Real.pi * (m : ℝ) + (p : ℝ) + 2) * R) := by
          gcongr
          linarith
    _ = (Real.pi * (m : ℝ) + (p : ℝ) + 2) * ((n : ℝ) + 1) ^ (7 / 2 : ℝ)
          * (2 * κV + Real.exp 1 * γnorm) := by
          rw [hR]; ring

end Qatlib.Papers.SpectralDE19.MainResults
