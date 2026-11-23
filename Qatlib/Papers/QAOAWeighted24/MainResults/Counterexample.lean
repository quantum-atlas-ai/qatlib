/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

@[expose] public section

/-!
# A sharpness witness for the weighted-QAOA derivative bound

The weighted MaxCut objective in Eq. (9) of [Sureshbabu2024], Lemma 2.1
specializes on a four-cycle with one selected edge of weight `w` and all
other edge weights zero to

`w / 2 + w * sin (w * γ) / 2`.

The printed Eq. (29) bound has no restriction on `γ`.  At `γ = 2` and
`w = π / 12`, the exact derivative of this specialization is strictly larger
than the printed right-hand side.  The witness is positive-weight and uses a
triangle-free 2-regular graph, so it refutes the literal unrestricted scope of
the source lemma.  The same calculation records the repaired domain condition
`0 ≤ γ ≤ 1` used by the source proof.

## References

* [Sureshbabu2024], Lemma 2.1
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QAOAWeighted24.MainResults

/-- The Eq. (9) objective specialized to a selected edge of a weighted C4.

The other three edge weights are zero.  Each of the two products in the
selected-edge term is therefore one, giving the displayed factor `1 / 2`.
-/
def c4SelectedObjective (γ w : ℝ) : ℝ :=
  w / 2 + w * Real.sin (w * γ) / 2

/-- The derivative obtained from the exact specialized Eq. (9) objective. -/
def c4SelectedDerivative (γ w : ℝ) : ℝ :=
  1 / 2 + (Real.sin (w * γ) + γ * w * Real.cos (w * γ)) / 2

/-- The right-hand side printed in Eq. (29) after the four-cycle neighbour
terms vanish. -/
def printedDerivativeBound (γ w : ℝ) : ℝ :=
  1 / 2 + (1 + γ) * |w| / 2

/-- The specialized objective has the derivative recorded by
`c4SelectedDerivative`. -/
theorem hasDerivAt_c4SelectedObjective (γ w : ℝ) :
    HasDerivAt (fun x : ℝ => c4SelectedObjective γ x)
      (c4SelectedDerivative γ w) w := by
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * γ))
      (Real.cos (w * γ) * γ) w := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (w * γ)).comp w ((hasDerivAt_id w).mul_const γ)
  have hprod : HasDerivAt (fun x : ℝ => x * Real.sin (x * γ))
      (Real.sin (w * γ) + w * (Real.cos (w * γ) * γ)) w := by
    convert (hasDerivAt_id w).mul hsin using 1
    · funext x
      rfl
    · change Real.sin (w * γ) + w * (Real.cos (w * γ) * γ) =
        1 * Real.sin (w * γ) + w * (Real.cos (w * γ) * γ)
      ring
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) w := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id w).mul_const (1 / 2 : ℝ)
  have hscaled := hprod.div_const (2 : ℝ)
  have hsum := hhalf.add hscaled
  convert hsum using 1
  · funext x
    simp [c4SelectedObjective, mul_comm]
  · simp [c4SelectedDerivative, mul_comm]
    ring

/-- At the positive C4 witness `γ = 2`, `w = π / 12`, the derivative is
strictly larger than the source's printed bound. -/
theorem c4_positive_literal_counterexample :
    |c4SelectedDerivative 2 (Real.pi / 12)| >
      printedDerivativeBound 2 (Real.pi / 12) := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hsqrt : (3 / 2 : ℝ) < Real.sqrt 3 := by
    have hsq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
      exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hnonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  rw [c4SelectedDerivative, printedDerivativeBound]
  have harg : Real.pi / 12 * (2 : ℝ) = Real.pi / 6 := by ring
  rw [harg]
  rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hw_pos : 0 < Real.pi / 12 := by positivity
  rw [abs_of_pos hw_pos]
  have houter : 0 < 1 / 2 + (1 / 2 + 2 * (Real.pi / 12) * (Real.sqrt 3 / 2)) / 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
    nlinarith
  rw [abs_of_pos houter]
  nlinarith

/-- The source's unrestricted Eq. (29) specialization is not a universal
bound.  This is the explicit negation of that literal statement. -/
theorem unrestricted_derivative_bound_refuted :
    ¬ (∀ γ w : ℝ,
      |c4SelectedDerivative γ w| ≤ printedDerivativeBound γ w) := by
  intro h
  exact (not_le_of_gt c4_positive_literal_counterexample) (h 2 (Real.pi / 12))

/-- On the source proof's repaired domain `0 ≤ γ ≤ 1`, the elementary
trigonometric estimate used in the proof is valid for every real weight. -/
theorem repaired_sine_bound (γ : ℝ) (hγ : 0 ≤ γ) (_hγ1 : γ ≤ 1) (w : ℝ) :
    |Real.sin (w * γ)| ≤ γ * |w| := by
  calc
    |Real.sin (w * γ)| ≤ |w * γ| := Real.abs_sin_le_abs
    _ = γ * |w| := by rw [abs_mul, abs_of_nonneg hγ, mul_comm]

/-- With `0 ≤ γ ≤ 1`, the source proof's direct-edge trigonometric term is
bounded by the coefficient used in Eq. (29). -/
theorem repaired_direct_derivative_bound (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (w : ℝ) :
    |Real.sin (w * γ) + γ * w * Real.cos (w * γ)| ≤ (1 + γ) * |w| := by
  have hs := repaired_sine_bound γ hγ hγ1 w
  have hc : |Real.cos (w * γ)| ≤ 1 := Real.abs_cos_le_one _
  have hgw : 0 ≤ γ * |w| := mul_nonneg hγ (abs_nonneg _)
  have hterm : |γ * w * Real.cos (w * γ)| ≤ γ * |w| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hγ]
    calc
      γ * |w| * |Real.cos (w * γ)| ≤ γ * |w| * 1 :=
        mul_le_mul_of_nonneg_left hc hgw
      _ = γ * |w| := by ring
  calc
    |Real.sin (w * γ) + γ * w * Real.cos (w * γ)| ≤
        |Real.sin (w * γ)| + |γ * w * Real.cos (w * γ)| := abs_add_le _ _
    _ ≤ γ * |w| + γ * |w| := add_le_add hs hterm
    _ ≤ (1 + γ) * |w| := by
      nlinarith [abs_nonneg w]

end Qatlib.Papers.QAOAWeighted24.MainResults
