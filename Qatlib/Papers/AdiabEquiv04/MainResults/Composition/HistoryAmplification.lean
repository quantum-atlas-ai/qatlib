/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Ring
import Qatlib.Papers.AdiabEquiv04.MainResults.Model.ComputationDefs

/-!
# AdiabEquiv04 — amplification from history states to final states (Lemma 3.10)

Lemma 3.10 of arXiv:quant-ph/0405098v2 (p. 13) converts a simulator whose output
approximates the *history state* into one whose output, after tracing out the
clock (ancilla) qubits, approximates the *final state* `U|0ⁿ⟩` of the circuit.

Formally we introduce two predicates on a locality parameter `k` and a running
time function `f`:

* `SimulatesHistory k f` — every circuit with `L` gates can be turned into a
  `k`-local adiabatic computation whose output is `δ`-close to the history
  state in trace distance and whose running time is `f L δ`;
* `SimulatesFinalState k f` — for every circuit with `L` gates and every `δ > 0`
  there is a `k`-local adiabatic computation on `n + ⌈2L/δ⌉` particles whose
  output, traced over the clock, is `δ`-close to the final circuit state and
  whose running time is `f ⌈2L/δ⌉ (δ/2)`.

The lemma is the implication between them: appending `⌈2L/δ⌉ − L` identity gates
raises the weight of `|α(L)⟩` in the history state, and tracing out the clock
yields the final state up to `δ/2 + δ/2`, using the triangle inequality and the
fact that trace distance is bounded by ℓ2 distance for pure states.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.AdiabEquiv04.MainResults.Composition

open Qatlib.Papers.AdiabEquiv04.MainResults

open Qatlib.Papers.AdiabEquiv04.MainResults.Model

/-- Hypothesis of Lemma 3.10: every circuit is simulated by a `k`-local
adiabatic computation whose output is `δ`-close to the history state, in running
time `f L δ`.  (`StateClose` is the trace distance to the pure history state,
the paper's ℓ2-closeness being stronger for pure states.) -/
def SimulatesHistory (k : ℕ) (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ (n L : ℕ) (gates : GateSeq n) (δ : ℝ), 0 < δ →
    ∃ (A : AdiabaticComputation (TotalBasis n L)) (T : ℝ),
      A.locality = k ∧ 0 < T ∧ T ≤ f L δ ∧
      StateClose A.output (historyState (L := L) gates) δ

/-- Conclusion of Lemma 3.10: the same simulator, applied to the circuit padded
with identity gates to length `⌈2L/δ⌉`, produces — after tracing out the clock
qubits — a state `δ`-close in trace distance to the final circuit state
`U|0ⁿ⟩`, in running time `f ⌈2L/δ⌉ (δ/2)`. -/
def SimulatesFinalState (k : ℕ) (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ (n L : ℕ) (gates : GateSeq n) (δ : ℝ), 0 < δ →
    ∃ (A : AdiabaticComputation (TotalBasis n ⌈(2 * (L : ℝ) / δ)⌉₊)) (T : ℝ),
      A.locality = k ∧ 0 < T ∧ T ≤ f ⌈(2 * (L : ℝ) / δ)⌉₊ (δ / 2) ∧
      StateClose (partialTrace A.output) (alpha gates L) δ

/-- **Lemma 3.10** (arXiv:quant-ph/0405098v2, p. 13), recorded statement.  If
every circuit can be simulated by a `k`-local adiabatic computation whose output
is close to the history state of the circuit, then it can be simulated by a
`k`-local adiabatic computation whose output, after tracing out the clock, is
close to the final state.

Paper proof route: pad the circuit with `(2/δ − 1)L` identity gates, so the
modified circuit has `L' = 2L/δ` gates and its history state has larger weight
on the final step; the assumed simulator (applied at accuracy `δ/2`) gives a
state `δ/2`-close to `|η⟩⟨η|`; tracing out the clock gives a state `δ/2`-close
to the final state (`δ/√L`-type bound in the paper); conclude by the triangle
inequality.

This is recorded as a proposition; it is not proved here.  The identity-gate
padding needs an identity element of `Matrix.unitaryGroup` and the tracing-out
estimate needs the partial trace of `|η⟩⟨η|` in terms of the `alpha gates ℓ`,
neither of which is developed yet.  The module contains no `sorry`. -/
def lemma_3_10_amplificationStatement : Prop :=
  ∀ (k : ℕ) (f : ℕ → ℝ → ℝ), SimulatesHistory k f → SimulatesFinalState k f

end Qatlib.Papers.AdiabEquiv04.MainResults.Composition
