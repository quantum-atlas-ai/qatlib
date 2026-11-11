/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Model.PaperGamesModel

/-!
# Theorem 3.6 — `QMAlog = BQP`

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 3.6 (page 13), proof page 14.

Statement (verbatim): `QMAlog = BQP`, where `QMAlog = QMAlog(2/3, 1/3)` is the
union of `QMAm(a,b)` over `m(n) = O(log n)` (page 13).

The inclusion `BQP ⊆ QMAlog` is trivial (no witness is needed, and the empty
message register has length `0`, which is `O(log n)`).  For `QMAlog ⊆ BQP` the
paper replaces Merlin's message by the totally mixed state `2^{−m} I`, so the
new algorithm's acceptance probability is `2^{−m} tr(Q_x)`; with `m = O(log n)`
the YES/NO gap `2^{−m}·(3/4 − 1/4)` is inverse-polynomial, and standard
amplification gives `BQP`.

## What is formalised here

* the trivial inclusion `BQP ⊆ QMAlog` is proved in full;
* the central operator identity of the reverse direction,
  `tr(Q · 2^{−m} I) = 2^{−m} tr(Q)`, is proved in full
  (`trace_totally_mixed`, and restated as the second conjunct below).

The remaining reverse step (instantiating a `BQP` machine from the totally mixed
witness and invoking amplification) needs an operator-to-uniform-circuit bridge
that is not in the shared library; see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.LogWitness

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Foundations.PureStateMath
open Matrix

/-- The totally mixed state on `m` qubits is `2^{−m} · I`. -/
noncomputable def totallyMixed (m : ℕ) : Operator (Qdim m) :=
  ((1 / (Qdim m : ℝ) : ℂ)) • (1 : Operator (Qdim m))

/-- Acceptance probability of the totally mixed witness equals `2^{−m} tr(Q)`.
This is the identity in the proof of Theorem 3.6 (p. 14):
`Pr[B accepts x] = tr(Q_x · 2^{−m} I) = 2^{−m} tr(Q_x)`. -/
theorem trace_totally_mixed {m : ℕ} (Q : Operator (Qdim m)) :
    Matrix.trace (Q * totallyMixed m) =
      (1 / (Qdim m : ℝ) : ℂ) * Matrix.trace Q := by
  unfold totallyMixed
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

/-- Theorem 3.6 (page 13), the two formalised components:

* `BQP ⊆ QMAlog`: `BQP = QMAm` with the empty witness register `m ≡ 0`, and the
  empty register has length `0 = O(log n)`;
* the totally-mixed-witness acceptance identity
  `tr(Q · 2^{−m} I) = 2^{−m} tr(Q)` that drives the converse `QMAlog ⊆ BQP`. -/
theorem theorem_3_6 :
    (∀ L : List Bool → Prop,
        InBqp L → InQMAlog (fun _ => 2 / 3) (fun _ => 1 / 3) L) ∧
      (∀ (m : ℕ) (Q : Operator (Qdim m)),
        Matrix.trace (Q * totallyMixed m) =
          (1 / (Qdim m : ℝ) : ℂ) * Matrix.trace Q) := by
  refine ⟨?_, ?_⟩
  · intro L hL
    -- `BQP ⊆ QMAlog`: use the empty message, which is `O(log n)`.
    exact ⟨fun _ => 0, ⟨0, fun n => Nat.zero_le _⟩, hL⟩
  · intro m Q
    exact trace_totally_mixed Q

end Qatlib.Papers.ArthurMerlin05.StaticGames.LogWitness
