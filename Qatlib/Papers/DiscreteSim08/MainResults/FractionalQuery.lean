/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fractional Boolean queries and controlled simulation

The fractional Boolean phase is decomposed into a global phase and a linear combination of the
identity phase and Boolean sign. The normalization `controlledSimulationNorm` then gives
explicit scalar success and failure estimates for angles between zero and `π / 2`.

This development follows [CleveEtAl2009].

## Main statements

* `fractionalQuery_decomposition`: the normalized fractional phase decomposition.
* `controlledSimulation_success_probability`: the reciprocal squared normalization is at least
  `1 - θ`.
* `controlledSimulation_failure_probability`: the failure expression is at most `θ`.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped BigOperators

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- The Boolean phase `exp (-iθ)` on true inputs and one on false inputs decomposes into a
global phase `exp (-iθ / 2)` times a cosine and Boolean-sign sine combination. -/
theorem fractionalQuery_decomposition_booleanPhase (θ : ℝ) (b : Bool) :
    (if b then Complex.exp (-(Complex.I * (θ : ℂ))) else 1) =
      Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) *
        (((Real.cos (θ / 2) : ℝ) : ℂ) +
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I * (if b then -1 else 1)) := by
  cases b
  · simp only [if_false, Bool.false_eq_true, mul_one]
    have hfac : ((Real.cos (θ / 2) : ℝ) : ℂ) +
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I
        = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
      have h := Complex.cos_add_sin_I ((θ / 2 : ℝ) : ℂ)
      simp only [Complex.ofReal_cos, Complex.ofReal_sin] at h ⊢
      exact h
    rw [hfac, ← Complex.exp_add]
    rw [show -(Complex.I * ((θ / 2 : ℝ) : ℂ)) + ((θ / 2 : ℝ) : ℂ) * Complex.I = 0 by ring]
    simp
  · simp only [if_true]
    have hfac : ((Real.cos (θ / 2) : ℝ) : ℂ) +
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I * (-1)
        = Complex.exp (((-(θ / 2) : ℝ) : ℂ) * Complex.I) := by
      have h := Complex.cos_sub_sin_I ((θ / 2 : ℝ) : ℂ)
      simp only [Complex.ofReal_cos, Complex.ofReal_sin] at h ⊢
      rw [show Complex.cos ((θ / 2 : ℝ) : ℂ) + Complex.sin ((θ / 2 : ℝ) : ℂ) * Complex.I * (-1)
            = Complex.cos ((θ / 2 : ℝ) : ℂ) - Complex.sin ((θ / 2 : ℝ) : ℂ) * Complex.I by ring]
      rw [h]
      congr 1
      push_cast
      ring
    rw [hfac, ← Complex.exp_add]
    congr 1
    rw [show -(Complex.I * ((θ / 2 : ℝ) : ℂ)) + ((-(θ / 2) : ℝ) : ℂ) * Complex.I
          = -(Complex.I * (θ : ℂ)) by push_cast; ring]

/-- The fractional Boolean phase at parameter `-θ / π` equals `exp (-iθ)` for true inputs and
one for false inputs. -/
theorem fractionalBooleanPhase_neg_div_pi (θ : ℝ) (b : Bool) :
    fractionalBooleanPhase (-(θ / Real.pi)) b =
      (if b then Complex.exp (-(Complex.I * (θ : ℂ))) else 1) := by
  cases b
  · simp [fractionalBooleanPhase]
  · simp only [fractionalBooleanPhase, if_true]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- The fractional Boolean phase at `-θ / π` equals `exp (-iθ / 2) * (cos (θ / 2) + i * sin (θ /
2) * s)`, where `s` is minus one for true inputs and one for false inputs. -/
theorem fractionalQuery_decomposition (θ : ℝ) (b : Bool) :
    fractionalBooleanPhase (-(θ / Real.pi)) b =
      Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) *
        (((Real.cos (θ / 2) : ℝ) : ℂ) +
          ((Real.sin (θ / 2) : ℝ) : ℂ) * Complex.I * (if b then -1 else 1)) := by
  rw [fractionalBooleanPhase_neg_div_pi, fractionalQuery_decomposition_booleanPhase]

/-- The scalar normalization `cos (θ / 2) + sin (θ / 2)` for controlled simulation. -/
noncomputable def controlledSimulationNorm (θ : ℝ) : ℝ :=
  Real.cos (θ / 2) + Real.sin (θ / 2)

/-- The reciprocal squared controlled-simulation normalization equals `1 / (1 + sin θ)`. -/
theorem controlledSimulation_success_eq (θ : ℝ) :
    1 / (controlledSimulationNorm θ) ^ 2 = 1 / (1 + Real.sin θ) := by
  unfold controlledSimulationNorm
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hsq : (Real.cos (θ / 2) + Real.sin (θ / 2)) ^ 2 = 1 + Real.sin θ := by
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), h2]
  rw [hsq]

/-- For `0 ≤ θ ≤ π / 2`, the reciprocal squared controlled-simulation normalization is at least
`1 - θ`. See [CleveEtAl2009]. -/
theorem controlledSimulation_success_probability (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ Real.pi / 2) :
    1 - θ ≤ 1 / (controlledSimulationNorm θ) ^ 2 := by
  have hcos0 : 0 ≤ Real.cos (θ / 2) :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).le
  have hsinhalf0 : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hcospos : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hv : 0 < Real.cos (θ / 2) + Real.sin (θ / 2) := by linarith
  have h2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hsq : (Real.cos (θ / 2) + Real.sin (θ / 2)) ^ 2 = 1 + Real.sin θ := by
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), h2]
  unfold controlledSimulationNorm
  rw [hsq]
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  rw [le_div_iff₀ (by linarith)]
  have hsin_le : Real.sin θ ≤ θ := Real.sin_le h0
  nlinarith [mul_nonneg h0 hsin0]

/-- For `0 ≤ θ ≤ π / 2`, the failure expression `sin θ / (1 + sin θ)` is at most `θ`. -/
theorem controlledSimulation_failure_probability (θ : ℝ) (h0 : 0 ≤ θ)
    (h1 : θ ≤ Real.pi / 2) :
    Real.sin θ / (1 + Real.sin θ) ≤ θ := by
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  have hden : 1 ≤ 1 + Real.sin θ := by linarith
  calc Real.sin θ / (1 + Real.sin θ) ≤ Real.sin θ := div_le_self hsin0 hden
    _ ≤ θ := Real.sin_le h0

end Qatlib.Papers.DiscreteSim08.MainResults
