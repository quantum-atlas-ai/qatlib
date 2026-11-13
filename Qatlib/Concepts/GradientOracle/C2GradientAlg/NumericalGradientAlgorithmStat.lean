/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision

/-!
# Numerical gradient algorithm specification

`NumericalGradientAlgorithm` states a finite-grid success guarantee for a rounded coherent value
oracle. Under smoothness, bounded Hessian, gradient-range, and grid hypotheses, it bounds the
probability of simultaneous coordinate errors and records exact query and gate counts. See
[Jordan2005Gradient] for background.

## Main statements

* `NumericalGradientAlgorithm`: The proposition that the rounded value-oracle gradient program
  uses one query and `2 * d + 1` gates and achieves coordinate error at most `w` with
  probability at least `1 - 16 * d / (M * w) - Real.pi * M * H * h * d / 2 - 2 * Real.pi / Q`
  under the stated hypotheses.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.C2GradientAlg

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The proposition that the rounded value-oracle gradient program uses one query and `2 * d +
1` gates and achieves coordinate error at most `w` with probability at least `1 - 16 * d /
(M * w) - Real.pi * M * H * h * d / 2 - 2 * Real.pi / Q` under the stated hypotheses. -/
def NumericalGradientAlgorithm : Prop :=
  ∀ (d M Q n_o : ℕ) (hM : 0 < M) [NeZero Q], 2 ≤ M → Q = 2 ^ n_o → 0 < n_o →
    ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (H h w : ℝ),
      ContDiff ℝ 2 f → 0 ≤ H → (∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) →
      0 < h → 0 < w → w ≤ 1 / 8 →
      (∀ j : Fin d, |(fderiv ℝ f x) (EuclideanSpace.single j 1)| ≤ 1 / 4) →
      let φ := fun z : GradientGrid d M => (M : ℝ) / h * f (x +
        WithLp.toLp 2 (fun j : Fin d => h * ((z j).val / (M : ℝ) - 1 / 2)))
      let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
      MeasureProb
        (Run (gradientValueOracle Q (gradientValueRoundedTable d M Q φ))
          (gradientValueProgram d M Q)
          (TensorState (Ket (gradientZero d M hM)) (Ket 1)))
        ((Finset.univ.filter (fun z : GradientGrid d M =>
            ∀ j : Fin d, |signedGridValue M (z j) - g j| ≤ w)) ×ˢ
          (Finset.univ : Finset (ZMod Q)))
        ≥ 1 - 16 * d / ((M : ℝ) * w) - Real.pi * M * H * h * d / 2
          - 2 * Real.pi / ((Q : ℝ)) ∧
      QueryCount (gradientValueProgram d M Q) = 1 ∧
      GateCount (gradientValueProgram d M Q) = 2 * d + 1

end Qatlib.Concepts.GradientOracle.C2GradientAlg
