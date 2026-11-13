/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# ReadoutTools — Algorithm 2 (the Jordan gradient algorithm body)

Fixed source: arXiv:1711.00465v3, *Optimizing quantum optimization algorithms
via faster quantum gradient computation*, §5, Algorithm 2 (p.29-30).

Algorithm 2 runs, on the grid `G_n^d = [0, 2^n−1]^d`:

1. prepare `|0⟩^d` (`gradientZero`);
2. apply the coordinate QFT (`coordinateQFT j`) on every register — the paper's
   `H^{⊗d}` / Fourier transform step (`gradientQFTWord`);
3. make **one** phase query to `O_f : |x⟩ ↦ e^{2πi φ(x)}|x⟩`
   (`gradientPhase`, the paper's phase oracle at the scaled grid values);
4. apply the inverse coordinate QFTs (`gradientQFTWord` reversed and adjointed);
5. measure and read out the `d` registers as a gradient estimate.

The library contains this word as `gradientWord d M` together
with the resource/unitarity proof `gradient_coordinate_qft_word_unitarity` and
the phase-oracle unitarity `gradientPhase_unitary`.  The paper-layer theorem
below is a bridging restatement, naming the paper's Algorithm 2 and recording
its single query, `2d` fixed gates and prepared output state; it is proved in
full by invoking these results.
-/

set_option autoImplicit false
noncomputable section

open Qatlib
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SignalPrimitive.GridGradient
open scoped BigOperators

namespace Qatlib.Papers.QGradient17.ReadoutTools.Algorithm

/-- Algorithm 2 of arXiv:1711.00465v3 (§5, p.29): the gradient word
`gradientWord d M` (forward coordinate QFT, one phase query, inverse coordinate
QFT) is a unitary circuit making exactly one query to the phase oracle
`gradientPhase d M φ` and using `2d` fixed gates; its output state on `|0⟩^d`
is the grid-gradient readout `gradientReadout d M hM φ`. -/
theorem source_algorithm_two
    (d M : ℕ) (hM : 0 < M) (φ : GradientGrid d M → ℝ) :
    IsUnitaryCircuit (gradientWord d M) ∧
    QueryCount (gradientWord d M) = 1 ∧
    GateCount (gradientWord d M) = 2 * d ∧
    gradientPhase d M φ ∈ Matrix.unitaryGroup (GradientGrid d M) ℂ ∧
    Run (gradientPhase d M φ) (gradientWord d M)
        (Ket (gradientZero d M hM)) = gradientReadout d M hM φ := by
  obtain ⟨hunit, hquery, hgate⟩ := gradient_coordinate_qft_word_unitarity d M hM
  exact ⟨hunit, hquery, hgate, gradientPhase_unitary d M φ, rfl⟩

end Qatlib.Papers.QGradient17.ReadoutTools.Algorithm
