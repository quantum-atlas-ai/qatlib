/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GateEffSim12.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainSimulation — Theorem 3.2 (Main) of arXiv:1211.4637v2

Fixed paper version: arXiv:1211.4637v2 (5 April 2013), PDF SHA-256
`aef583fed3675ee75a251ed7438ab99cb4c16b34697dd8f4293f3d39d07d471d`.
Theorem 3.2 is stated on p. 3.

The theorem says: a continuous-time query algorithm whose driving Hamiltonian
`H(t)` is approximately implementable within precision `1/T` using `G` gates can
be simulated with constant error by a discrete-query algorithm using
`O(T log T / log log T)` queries, `O(T G log T + T log³(‖H‖T))` one- and
two-qubit gates, and `O(log³(‖H‖T))` qubits of space.

This file gives the faithful statement over the model of `SourceModel` and
records the proof gap.  The paper proves Theorem 3.2 in §6 by composing the
following ingredients, none of which is formalised in the library yet:

1. discretisation of the time evolution into `T / log T` fractional-query
   segments, each implemented with `O(log T / log log T)` queries (§2, §6.1);
2. the compressed CGMSY simulation (`B_q^k`/`C_m^k` encodings, Theorems 4.3
   and 5.1–5.5 of this paper, §4–§5), whose error is `O(ε' + ε log m)` by
   Theorem 5.5 (formalised as `MainResults.ErrorBounds.theorem_5_5`);
3. composition of the error bounds, using that the completely bounded error
   `ε'` accumulates linearly over the `O(T)` time steps.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.GateEffSim12.MainResults.SourceModel

namespace Qatlib.Papers.GateEffSim12.MainResults.MainSimulation

/-- **Theorem 3.2 (Main), arXiv:1211.4637v2, p. 3.**

The statement is recorded as the `Prop`-valued definition below; its proof is
not formalised.

Let `A` be a continuous-time query algorithm of duration `T = A.time` whose
driving Hamiltonian is bounded by `Hnorm` in operator norm and is approximately
implementable within precision `1/T` using `G` gates (the paper's hypothesis,
`himpl`).  Then there are a discrete-query algorithm `B` and a constant `c > 0`
such that `B` simulates `A` within the constant error `1/10` (the paper's
"constant error"), with the paper's three resource bounds:

* `O(T log T / log log T)` queries,
* `O(T G log T + T log³(‖H‖T))` one- and two-qubit gates,
* `O(log³(‖H‖T))` qubits of space.

The paper states the theorem asymptotically for `T → ∞`; the formal statement
fixes the regime `T ≥ 3`, where `log log T > 0`, so the query bound is positive
(an `O(1)` constant absorbs small `T`, as usual for big-O statements).
The constant `1/10` is the paper's unspecificated constant error; the constant
`c` is existentially quantified, matching the paper's `O(·)` notation.

Model boundary: the gate count `G` is a granted resource of the implementation
(see `SourceModel.ApproxImplementable`), and the semantics of `B` is its output
law (`SourceModel.Simulates`).  The internal unitary circuit of `B`, and hence
the paper's gate/space accounting, is not derived here.

Proof gap: the paper's §6 proof composes the discretisation of §2 (fractional
queries), the compressed CGMSY construction of §4 (Theorems 4.3, 5.1), and the
error analysis of §5 (Theorems 5.3–5.5).  Only Theorem 5.4/5.5 are formalised
(`MainResults.ErrorBounds`); the remaining ingredients would need (a) a formal
circuit/Gate model with gate synthesis, (b) the query-complexity accounting of
§6.1, and (c) the error-composition lemma `ε_tot = O(T ε')`.  Candidate
reusable dependencies: `QuantumAlgorithm.Concepts.GramQueryCore.LowerBoundTools`
(continuous-time model, `sourceVolterraMatrix`),
`QuantumAlgorithm.Papers.RandCompiler19.ChannelBudget.finiteDiamondDistance`
(completely bounded error), and `MainResults.ErrorBounds.theorem_5_5`
(compressed-simulation error).  Suggested successor tactics: build the
`DiscreteQueryAlgorithm` by `Classical.choose` from the compressed construction,
then discharge each resource inequality by `nlinarith` after instantiating the
big-O constants from §6. -/
def main_resource_theorem
    {X Ω : Type} [Fintype X] [Fintype Ω] {d : ℕ}
    (A : ContinuousTimeQueryAlgorithm X Ω d)
    (Hnorm : ℝ) (hHnorm : 0 ≤ Hnorm)
    (hH : ∀ t, ‖A.driving t‖ ≤ Hnorm)
    (G : ℕ)
    (himpl : ApproxImplementable A.driving A.time (1 / A.time) G)
    (hT : 3 ≤ A.time) : Prop :=
  ∃ (B : DiscreteQueryAlgorithm X Ω) (c : ℝ), 0 < c ∧
      Simulates A B (1 / 10) ∧
      (B.queryCount : ℝ) ≤
        c * (A.time * Real.log A.time / Real.log (Real.log A.time)) ∧
      (B.gateCount : ℝ) ≤
        c * (A.time * G * Real.log A.time + A.time * (Real.log (Hnorm * A.time)) ^ 3) ∧
      (B.space : ℝ) ≤ c * (Real.log (Hnorm * A.time)) ^ 3

end Qatlib.Papers.GateEffSim12.MainResults.MainSimulation
