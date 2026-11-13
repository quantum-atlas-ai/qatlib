/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ValueKickback

/-!
# Smooth gradient readout from value-oracle phases

`gradient_value_c2_same_record_consumer` transfers the smooth-function gradient bound to a
finite value table whose phase approximates the scaled sampled function modulo integers. The
resulting success bound combines grid tails, the Hessian-controlled remainder, and the
phase-precision penalty. See [Jordan2005Gradient] for background.

## Main statements

* `gradient_value_c2_same_record_consumer`: Under the stated smoothness and phase-precision
  hypotheses, the value-phase readout estimates every gradient coordinate within `w` with
  probability at least `1 - 16 * d / (M * w) - Real.pi * M * H * h * d / 2 - 4 * Real.pi * δ`.
  [Jordan2005Gradient]

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Qatlib.Concepts.GradientOracle.C2GradientAlg
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Under the stated smoothness and phase-precision hypotheses, the value-phase readout
estimates every gradient coordinate within `w` with probability at least `1 - 16 * d / (M *
w) - Real.pi * M * H * h * d / 2 - 4 * Real.pi * δ`. [Jordan2005Gradient] -/
theorem gradient_value_c2_same_record_consumer :
    ∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q]
      (v : GradientGrid d M → ZMod Q) (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (x : EuclideanSpace ℝ (Fin d)) (H h w δ : ℝ),
      ContDiff ℝ 2 f → 0 ≤ H → (∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) →
      2 ≤ M → 0 < h → 0 < w → w ≤ 1 / 8 → 0 ≤ δ →
      let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
      (∀ j, |g j| ≤ 1 / 4) →
      let φ := fun z : GradientGrid d M => (M : ℝ) / h * f (x +
        WithLp.toLp 2 (fun j : Fin d => h * ((z j).val / (M : ℝ) - 1 / 2)))
      (∀ z, ∃ k : ℤ, |gradientValuePhase Q v z - φ z - k| ≤ δ) →
      MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
        (Finset.univ.filter (fun z => ∀ j : Fin d, |signedGridValue M (z j) - g j| ≤ w)) ≥
        1 - 16 * d / ((M : ℝ) * w) - Real.pi * M * H * h * d / 2 - 4 * Real.pi * δ := by
  intro d M Q hM _ v f x H h w δ hf hH hessian hM2 hh hw0 hw hδ
  (try dsimp only)
  intro hg hprecision
  let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
  let φ := fun z : GradientGrid d M => (M : ℝ) / h * f (x +
    WithLp.toLp 2 (fun j : Fin d => h * ((z j).val / (M : ℝ) - 1 / 2)))
  let S := Finset.univ.filter (fun (z : GradientGrid d M) => ∀ j : Fin d,
    |signedGridValue M (z j) - g j| ≤ w)
  have hideal := gradient_smooth_function_actual_consumer d M hM f x H h w
    hf hH hessian hM2 hh hw0 hw hg
  have hvalue := gradient_value_precision_actual_readout_event d M Q hM v φ δ S hδ hprecision
  have hlo := (abs_le.mp hvalue).1
  linarith only [hideal, hlo]

end Qatlib.Concepts.GradientOracle.C2GradientAlg
