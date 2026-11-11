/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Specification of optimized tunable amplification

`OptimizedTunableOptimizedTunableConsumer` specifies a universal weighted-cost bound for a legal
nested amplification schedule. For a positive final plain amplitude, it requires thresholds with
total budget at most one, final post-amplitude at least 1/10, and a cost controlled by initial
prices and the 2/3 quasinorm of intermediate amplitude-weighted prices.

The specification is motivated by variable-time amplitude amplification [Ambainis2012]. For
tunable VTAA query bounds, see [LowSu2026].

## Main statements

* `OptimizedTunableOptimizedTunableConsumer`: States the existence of uniformly bounded-cost
  amplification schedules.

## References

* [Ambainis, 2012][Ambainis2012]
* [Low and Su, 2026][LowSu2026]
-/

set_option warningAsError false
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

/-- The optimized consumer specification requires a universal constant bounding weighted
nested-amplification cost by the initial fees and an intermediate 2/3 quasinorm divided by
final plain amplitude, while achieving post-amplitude at least `1 / 10` with legal words and
threshold budget at most one. -/
def OptimizedTunableOptimizedTunableConsumer : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (prices : ℕ → ℕ),
    0 < m → clockLegal m P bad → stageLegal m P U → Normalized ω →
    let E := extendClock m P
    let a := plainAmplitude E bad U ω m
    0 < a → ∃ (α : ℕ → ℝ) (rs : ℕ → ℕ),
      tunable m E bad U ω α rs ∧
      (∀ j : Fin m, α (j.val+1) ≤ 1) ∧ (∑ j : Fin m, α (j.val+1)) ≤ 1 ∧
      legal (m+1) (nestedWord E bad ω rs m) ∧
      1/10 ≤ postAmplitude E bad ω U rs m ∧
      (weightedCost prices (nestedWord E bad ω rs m) : ℝ) ≤ K/a*
        (((prices 0+prices 1 : ℕ) : ℝ)+
          quasinorm23 (fun j : Fin (m-1) =>
            plainAmplitude E bad U ω (j.val+1)*prices (j.val+2)))

end Qatlib.Concepts.QlsReadoutSpec.Amplification
