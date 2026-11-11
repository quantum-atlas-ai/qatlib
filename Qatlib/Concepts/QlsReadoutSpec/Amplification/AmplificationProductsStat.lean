/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels

/-!
# Nested amplification product contract

Defines `Clause9AmplificationProducts`, which specifies exact initial-oracle counts and weighted
query costs for nested amplification. Under the clock, stage, tuning, and positivity hypotheses,
the product of the odd amplification factors equals the final amplified amplitude divided by the
plain amplitude and total loss, as in [LowSu2026].

## Main statements

* `Clause9AmplificationProducts`: states the call product, weighted cost recurrence, and final
  amplitude identity.

## References

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

/-- The nested amplification contract giving slot-zero call products, the stagewise weighted
cost recurrence, and the final amplitude-ratio identity under clock legality, stage
legality, normalized seed, positive plain amplitude, and tuning hypotheses. -/
def Clause9AmplificationProducts : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ)
    (U : ℕ → Matrix H H ℂ) (ω : QState H) (α : ℕ → ℝ) (rs : ℕ → ℕ),
    clockLegal m P bad → stageLegal m P U → Normalized ω →
    0 < plainAmplitude (extendClock m P) bad U ω m →
    tunable m (extendClock m P) bad U ω α rs →
    (∀ j : Fin m, α (j.val+1) ≤ 1) →
    let E := extendClock m P
    (∀ j : Fin (m+1),
      calls (nestedWord E bad ω rs j.val) 0=
        ∏ k : Fin j.val, (2*rs (k.val+1)+1)) ∧
    (∀ j : Fin m, ∀ prices,
      weightedCost prices (nestedWord E bad ω rs (j.val+1))=
        (2*rs (j.val+1)+1)*
          (weightedCost prices (nestedWord E bad ω rs j.val)+prices (j.val+1))) ∧
    (((∏ j : Fin m, (2*rs (j.val+1)+1)) : ℕ) : ℝ)=
      postAmplitude E bad ω U rs m/
        (plainAmplitude E bad U ω m*totalLoss m E bad U ω rs)

end Qatlib.Concepts.QlsReadoutSpec.Amplification
