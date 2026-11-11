/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
import Qatlib.Concepts.HhlErrorBridge.FilterStability

set_option backward.isDefEq.respectTransparency false

/-!
# Bridge: the frozen one-run HHL certificate behind run-time (1a)

Fixed source: A. W. Harrow, *Review of Quantum Algorithms for Systems of Linear
Equations*, arXiv:1501.00008v1, §2.1, PDF p. 2. The quoted run-time (1a)
`Õ(κT_B + log(N) s² κ² T_A / ε)` is the HHL 2009 [5] result, whose
one-run success/cost certificate is formalized in Frozen under
`QuantumAlgorithm.Papers.LinearSystems09.SinEnvProgram.SinEnvelopeHHLConsumers`.

The paper-layer bridges below do not reprove the frozen content: they restate
it under the `QLinearSys15` namespace so that the review's §2.1 result is tied
to the concrete HHL program and the three-flag filter ledger bound by the claim
`c002` (`HhlErrorBridge`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLinearSys15.MainResults.MainRuntime

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers

/-- **One-run success and macro-cost of the HHL program (frozen certificate for
(1a)).** With a well-conditioned spectrum (`2d ≤ eig ≤ 1/4`), a repetition
count `k ≤ ⌈1/(5d)⌉+1` succeeds with Born mass at least `1/4` and stays inside
the frozen macro-query budget. Reused FQN:
`QuantumAlgorithm.Papers.LinearSystems09.SinEnvProgram.SinEnvelopeHHLConsumers.
sin_envelope_aa_success_and_cost`; this is the program-level content that the
review's HHL run-time (1a) charges. -/
theorem sinEnvelope_aa_success_and_cost_bridge {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (h2d : 2 * d ≤ 1 / 4) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1 / 4)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
        Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
      ∃ k : ℕ,
        k ≤ Nat.ceil (1 / (5 * d)) + 1 ∧
        MeasureProb (Run (preparedMark (sinEnvelopeWellSetCorrected D M))
            (preparedAACircuit (sinEnvelopeAmplifiedWord M hM
              (continuousHHLOracle eig V) d B)
              (sinEnvelopeCleanInputPoint hM j) k)
            (Ket (sinEnvelopeCleanInputPoint hM j)))
            (sinEnvelopeWellSetCorrected D M) ≥ 1 / 4 ∧
        ((2 * (k : ℝ) + 1) * (2 * ((M : ℝ) - 1)) + (k : ℝ) ≤
          (2 * ((Nat.ceil (1 / (5 * d)) : ℝ) + 1) + 1) * (2 * (M : ℝ)) +
            ((Nat.ceil (1 / (5 * d)) : ℝ) + 1)) :=
  sin_envelope_aa_success_and_cost M hM eig V B j d η hV hB hd h2d hη hη1 heig hbudget

/-- **Three-flag filter normalization (bound `HhlErrorBridge`).** The
three-flag amplitude vector of the HHL error bridge is normalized, for every
`sine-envelope width d > 0` and phase `θ`. Reused FQN:
`QuantumAlgorithm.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_normalized`;
this is the `HhlErrorBridge` ledger that the `c002` bind names. -/
theorem sinEnvelopeHVector_normalized_bridge (d θ : ℝ) (hd : 0 < d) :
    ∑ s : Fin 3, ‖Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeHVector
      d θ s‖ ^ 2 = 1 :=
  Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_normalized d θ hd

end Qatlib.Papers.QLinearSys15.MainResults.MainRuntime
