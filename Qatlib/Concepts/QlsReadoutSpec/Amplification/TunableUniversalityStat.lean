/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Specification of tunable schedule universality

`Clause8TunableUniversality` states forward and reverse relationships between thresholds, round
counts, and accumulated gain loss. For legal clocks and stages with positive final plain
amplitude, a bounded-threshold tunable schedule has positive pre-amplitudes and explicit ceiling
formulas. Conversely, sufficiently small positive pre-amplitudes give a tunable
`reverseThreshold` schedule whose threshold sum is controlled by logarithmic loss.

These schedule specifications are motivated by variable-time amplitude amplification
[Ambainis2012]. For universality of tunable VTAA, see [LowSu2026].

## Main statements

* `Clause8TunableUniversality`: Packages forward round-count formulas and reverse loss-budget
  bounds.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The specification relates bounded-threshold tunable schedules to positive pre-amplitudes,
explicit ceiling round counts, and an exponential loss lower bound; it also reconstructs
tunable reverse thresholds from sufficiently small positive pre-amplitudes and bounds their
sum by negative logarithmic loss. -/
def Clause8TunableUniversality : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ),
    clockLegal m P bad → stageLegal m P U → Normalized ω →
    0 < plainAmplitude (extendClock m P) bad U ω m →
    let E := extendClock m P
    ((tunable m E bad U ω α rs ∧ ∀ j : Fin m, α (j.val+1) ≤ 1) →
      (∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val ∧
        (2*rs (j.val+1)+1)*preAmplitude E bad ω U rs j.val ≤ 1 ∧
        rs (j.val+1)=Nat.ceil
          (Real.sqrt (α (j.val+1))/(6*preAmplitude E bad ω U rs j.val)-1/2)) ∧
      (5/6 : ℝ).rpow (∑ j : Fin m, α (j.val+1)) ≤ totalLoss m E bad U ω rs) ∧
    ((∀ j : Fin m, 0 < preAmplitude E bad ω U rs j.val ∧
      preAmplitude E bad ω U rs j.val ≤ 1/(3*(2*rs (j.val+1)+1))) →
      tunable m E bad U ω (reverseThreshold E bad U ω rs) rs ∧
      (∀ j : Fin m, reverseThreshold E bad U ω rs (j.val+1) ≤ 1) ∧
      (4*Real.pi-8)/(9*Real.pi^3)*(∑ j : Fin m, reverseThreshold E bad U ω rs (j.val+1)) ≤ -Real.log (totalLoss m E bad U ω rs))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
