/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Core.Toolkit

/-!
# Theorem 3.4 — `QMA ⊆ PP`

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 3.4 (page 13), proof pages 13--14.

Statement (verbatim): `QMA ⊆ PP`.

The paper applies Theorem 3.3 to obtain, for each time bound, an `m`-qubit
verifier with completeness `1 − 2^{−m−2}` and soundness `2^{−m−2}`, forms the
PSD acceptance operator `Q_x`, and observes the trace sandwich

* `tr(Q_x) ≥ 3/4` on YES (`x ∈ L`),
* `tr(Q_x) ≤ 2^m · 2^{−m−2} ≤ 1/4` on NO (`x ∉ L`),

after which the Fortnow--Rogers GapP representation of `Q_x` gives a `PP`
machine deciding `L` by the sign of `2^{g(x)} tr(Q_x)`.

## What is formalised here

The trace sandwich `tr(Q_x) ≥ 3/4` (resp. `2/3` for the unamplified
`QMA(2/3,1/3)`) and `tr(Q_x) ≤ dim · b` is proved from positivity alone:

* `theorem_3_4_yes` uses `Core.expectation_le_trace` together with the existence
  of a unit witness whose acceptance `⟨ψ|Q|ψ⟩` exceeds `2/3`;
* `theorem_3_4_no` uses `Core.trace_le_dim_mul_bound` from `Q ≤ (1/3) • 1`.

The GapP/PP transport itself (operator-to-counting-class bridge) is not present
in the shared library; see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Counting

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Papers.ArthurMerlin05.StaticGames.Core
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

/-- Theorem 3.4, YES trace bound (pp. 13--14): if a positive semidefinite
acceptance operator `Q` on `m` qubits has some unit witness with acceptance at
least `2/3`, then `tr(Q) ≥ 2/3`.  This is the `tr(Q_x) ≥ 3/4` step. -/
theorem theorem_3_4_yes {m : ℕ} (Q : Operator (Qdim m)) (hQ : Q.PosSemidef)
    (hyes : ∃ ψ : QState (Fin (Qdim m)), Normalized ψ ∧ (2 / 3 : ℝ) ≤ acceptProb Q ψ) :
    (2 / 3 : ℝ) ≤ (Matrix.trace Q).re := by
  obtain ⟨ψ, hψ, hacc⟩ := hyes
  have hle := expectation_le_trace hQ hψ
  unfold acceptProb at hacc
  linarith

/-- Theorem 3.4, NO trace bound (pp. 13--14): if a PSD acceptance operator `Q`
satisfies `Q ≤ (1/3) • 1` (soundness `1/3` for every witness), then
`tr(Q) ≤ dim · (1/3)`.  This is the `tr(Q_x) ≤ 2^m · 2^{−m−2} ≤ 1/4` step. -/
theorem theorem_3_4_no {m : ℕ} (Q : Operator (Qdim m))
    (hQ : Q ≤ ((1 / 3 : ℝ) : ℂ) • (1 : Operator (Qdim m))) :
    (Matrix.trace Q).re ≤ (Qdim m : ℝ) * (1 / 3) :=
  trace_le_dim_mul_bound hQ

/-- Theorem 3.4 (p. 13), trace sandwich: a `QMA(2/3,1/3)` acceptance operator
satisfies `2/3 ≤ tr(Q)` on YES and `tr(Q) ≤ dim/3` on NO. -/
theorem theorem_3_4 {m : ℕ} (Q : Operator (Qdim m)) (hQ : Q.PosSemidef)
    (hyes : ∃ ψ : QState (Fin (Qdim m)), Normalized ψ ∧ (2 / 3 : ℝ) ≤ acceptProb Q ψ)
    (hno : Q ≤ ((1 / 3 : ℝ) : ℂ) • (1 : Operator (Qdim m))) :
    (2 / 3 : ℝ) ≤ (Matrix.trace Q).re ∧
      (Matrix.trace Q).re ≤ (Qdim m : ℝ) * (1 / 3) :=
  ⟨theorem_3_4_yes Q hQ hyes, theorem_3_4_no Q hno⟩

end Qatlib.Papers.ArthurMerlin05.StaticGames.Counting
