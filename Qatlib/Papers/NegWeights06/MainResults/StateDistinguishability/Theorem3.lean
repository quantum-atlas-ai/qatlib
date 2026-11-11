/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

/-!
# NegWeights06, Theorem 3 — distinguishing two known states

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 3, §3, printed page 4:

Let `0 ≤ ε ≤ 1/2`.  There is a measurement that correctly identifies which of
the two known states `|ψx⟩`, `|ψy⟩` is given, with error probability `ε`, if and
only if `⟨ψx|ψy⟩ ≤ 2√(ε(1−ε))`.

The paper writes the inner product without absolute value because in its setting
`⟨ψx|ψy⟩` is a nonnegative real (it is used as the progress function of the
adversary construction).  The general-state statement is the absolute-value form
`|⟨ψx|ψy⟩| ≤ 2√(ε(1−ε))`, which is what is recorded here; the two coincide in
the paper's real nonnegative regime.

A distinguishing measurement is a two-outcome POVM `out : Bool → Matrix H H ℂ`
(`IsPovm`) whose Born probabilities (`povmProb`) of the correct outcomes are at
least `1 − ε` for both states.

The theorem is recorded as the closed `Prop` contract
`theorem3DistinguishabilitySpec`; it is **not** proved in this repository.  Fixed
version: quant-ph/0611054v2.  Source: Theorem 3 on p. 4.  Residual Lean gap: the
library has the POVM/Born-probability interface (`IsPovm`, `povmProb`) and the
complex inner product (`Inner`), but it has neither the Helstrom pure-state
distinguishability iff nor the supporting facts (the optimal two-outcome POVM
for a pair of pure states and the trace-distance expression
`1/2 + 1/2√(1 − |⟨ψx|ψy⟩|²)` of its success probability).  Candidate
dependencies: `povmProb`, `IsPovm`, `Inner`, and the operator-norm machinery of
`QuantumInfo.ForMathlib.MatrixNorm.TraceNorm`.  Suggested continuation: show
that for a two-outcome POVM with elements `E` and `1 − E` the worst-case success
probability is at most `1/2 + 1/2‖⟨ψx|ψy⟩‖` (trace-norm duality route of
Theorem 4), and that it is attained by the projection onto the positive part of
`|ψx⟩⟨ψx| − |ψy⟩⟨ψy|`; then invert the bound
`1 − ε ≤ (1 + ‖⟨ψx|ψy⟩‖)/2`.
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.StateDistinguishability

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality

noncomputable section

/-- **Theorem 3 (state distinguishability iff), recorded statement.**
For normalized pure states `psix`, `psiy` on a finite register `H` and
`0 ≤ ε ≤ 1/2`, a two-outcome POVM identifies which state was given with error
at most `ε` if and only if `|⟨psix|psiy⟩| ≤ 2√(ε(1−ε))`.

The measurement `out : Bool → Matrix H H ℂ` reads outcome `true` for `psix` and
`false` for `psiy`; "error at most `ε`" means both correct-outcome Born
probabilities are at least `1 − ε`.  This is quant-ph/0611054v2 Theorem 3
(p. 4), recorded as a closed `Prop`; it is not proved here.  See the module
docstring for the fixed version, the proof route, the current Lean gap, the
candidate dependencies, and the suggested continuation. -/
def theorem3DistinguishabilitySpec : Prop :=
  ∀ {H : Type} [Fintype H] [DecidableEq H]
    (psix psiy : QState H) (eps : ℝ),
    Normalized psix → Normalized psiy → 0 ≤ eps → eps ≤ 1 / 2 →
    ((∃ out : Bool → Matrix H H ℂ, IsPovm out ∧
        1 - eps ≤ povmProb out true psix ∧ 1 - eps ≤ povmProb out false psiy) ↔
      ‖Inner psix psiy‖ ≤ 2 * Real.sqrt (eps * (1 - eps)))

/-- **Theorem 3, sufficiency direction, recorded statement** (paper's "if"
half): an inner-product bound yields a measurement with error at most `ε`.

This is the forward implication of quant-ph/0611054v2 Theorem 3 (p. 4),
recorded as a closed `Prop` and not proved here; it is implied by
`theorem3DistinguishabilitySpec`. -/
def theorem3MeasurementOfInnerSpec : Prop :=
  ∀ {H : Type} [Fintype H] [DecidableEq H]
    (psix psiy : QState H) (eps : ℝ),
    Normalized psix → Normalized psiy → 0 ≤ eps → eps ≤ 1 / 2 →
    ‖Inner psix psiy‖ ≤ 2 * Real.sqrt (eps * (1 - eps)) →
    ∃ out : Bool → Matrix H H ℂ, IsPovm out ∧
      1 - eps ≤ povmProb out true psix ∧ 1 - eps ≤ povmProb out false psiy

end

end Qatlib.Papers.NegWeights06.MainResults.StateDistinguishability
