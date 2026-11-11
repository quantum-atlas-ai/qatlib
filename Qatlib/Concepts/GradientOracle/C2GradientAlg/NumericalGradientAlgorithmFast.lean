/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.C2GradientAlg.NumericalGradientAlgorithmStat

/-!
# A single-query numerical gradient algorithm

`numericalGradientAlgorithm` proves the numerical-gradient contract for a twice continuously
differentiable function with a uniform Hessian norm bound. The value-oracle program uses one
query and `2 * d + 1` gates, and its coordinatewise success probability includes finite-grid,
Taylor, and value-rounding errors. See [Jordan2005Gradient] for background.

## Main statements

* `numericalGradientAlgorithm`: The rounded finite-grid value-oracle program satisfies
  `NumericalGradientAlgorithm`, including its success-probability estimate, one oracle query,
  and `2 * d + 1` gates. [Jordan2005Gradient]

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.GradientOracle.C2GradientAlg
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The rounded finite-grid value-oracle program satisfies `NumericalGradientAlgorithm`,
including its success-probability estimate, one oracle query, and `2 * d + 1` gates.
[Jordan2005Gradient] -/
theorem numericalGradientAlgorithm : NumericalGradientAlgorithm := by
  intro d M Q n_o hM _ hM2 _hQ _hn_o f x H h w hf hH hessian hh hw0 hw hg
  (try dsimp only)
  let φ := fun z : GradientGrid d M => (M : ℝ)/h*f (x+
    WithLp.toLp 2 (fun j : Fin d => h*((z j).val/(M : ℝ)-1/2)))
  let v := gradientValueRoundedTable d M Q φ
  let S := Finset.univ.filter (fun z : GradientGrid d M =>
    ∀ j : Fin d, |signedGridValue M (z j)-(fderiv ℝ f x) (EuclideanSpace.single j 1)| ≤ w)
  have hprep := gradient_char_prep_inverse_qft d M hM Q
  have hrun : Run (gradientValueOracle Q v) (gradientCharPrep d M Q)
      (TensorState (Ket (gradientZero d M hM)) (Ket 1)) =
        TensorState (Ket (gradientZero d M hM)) (gradientKickState Q) := by
    simpa only [gradientCharPrep,run_gate,run_nil] using! hprep.1
  have hprob : MeasureProb (Run (gradientValueOracle Q v) (gradientValueProgram d M Q)
      (TensorState (Ket (gradientZero d M hM)) (Ket 1))) (S ×ˢ Finset.univ) =
      MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S := by
    rw [gradientValueProgram,run_append,hrun]
    exact gradient_value_actual_data_marginal d M Q hM v S
  have hwindow := gradient_value_c2_rounded_consumer d M Q hM f x H h w
    hf hH hessian hM2 hh hw0 hw hg
  have hword := gradient_value_one_query_clean_fourier_consumer d M Q hM v
  constructor
  · change MeasureProb (Run (gradientValueOracle Q v) (gradientValueProgram d M Q)
      (TensorState (Ket (gradientZero d M hM)) (Ket 1))) (S ×ˢ Finset.univ) ≥ _
    rw [hprob]
    exact hwindow
  · unfold gradientValueProgram
    rw [queryCount_append,gateCount_append,hprep.2.1,hprep.2.2,hword.2.1,hword.2.2]
    constructor <;> omega

end Qatlib.Concepts.GradientOracle.C2GradientAlg
