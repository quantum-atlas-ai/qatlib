/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Bayesian Deep Learning on a Quantum Computer (arXiv:1806.11463), Section III C.

Shared model layer for Lemmas 1-2 and Theorem 1: the unitary time evolution
`e^{-i H t}`, and `IteratedStepWitness`, which formalizes the paper's phrase
"there exists a quantum algorithm to implement the unitary `e^{-i H t}` on a
`d`-dimensional qubit input state `σ`, ... to accuracy `ε` in operator norm"
(arXiv:1806.11463, Lemma 1 p.4-5, Lemma 2 p.5, Theorem 1 p.5), together with the
copy budget `O(t²/ε)` (resp. `O(N²t²/ε)`) consumed from the source copies.

A witness commits to a concrete step family `step : ℝ → Operator d → Operator d`
(the single-round channel, whose definition fixes which copies of the source are
consumed), a step size `δ` and a number of rounds `copies` with
`copies · δ = t`, and demands that the `copies`-fold iterate of `step δ` agree
with the exact evolution `e^{-iHt} σ e^{iHt}` to operator-norm accuracy `ε`.
Because the step family is fixed by each lemma (not freely chosen by the
witness), a zero-copy or single-copy witness cannot satisfy the accuracy demand
and the copy bound is a genuine resource statement.

Paper version read: arXiv:1806.11463 (PDF pages 4-6).
-/
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.BayesDeepNet18.MainResults.SourceOperators
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Copy Evolution Model

Paper-level definitions and results for `BayesDeepNet18`.
The declarations below retain the mathematical statements and helper proofs of the source model.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.BayesDeepNet18.MainResults

/-- The unitary time evolution `e^{-i H t}` of a Hamiltonian `H`, written with
the (complex) scalar `-i t` in front of `H` (arXiv:1806.11463, Section III C). -/
def timeEvolution {d : ℕ} (H : Operator d) (t : ℝ) : Operator d :=
  NormedSpace.exp (((-Complex.I) * (t : ℂ)) • H)

/-- A single-round channel family on the `d`-dimensional input state, indexed by
the step size `δ`; each round consumes one fresh copy of every source state it
uses (encoded in the concrete definition of the family). -/
abbrev StepFamily (d : ℕ) : Type := ℝ → Operator d → Operator d

/-- A faithful witness that the unitary `e^{-i H t}` has been implemented on a
`d`-dimensional input state from repeated rounds of a fixed copy-consuming step
family, to operator-norm accuracy `ε` (arXiv:1806.11463, Lemma 1 p.4-5,
Lemma 2 p.5, Theorem 1 p.5).

Fields: `copies` is the number of rounds (hence of fresh source copies of each
input density matrix), `δ` is the per-round time step with `copies · δ = t`, and
`accurate` states that iterating `step δ` `copies` times reproduces the exact
evolution `e^{-iHt} σ e^{iHt}` of every input `σ` within `ε` in the L2 operator
norm. -/
structure IteratedStepWitness (d : ℕ) (H : Operator d) (t ε : ℝ) (step : StepFamily d) where
  /-- Number of rounds, i.e. the number of fresh copies taken of each source
  density matrix. -/
  copies : ℕ
  /-- The per-round time step. -/
  δ : ℝ
  /-- The per-round time step is positive. -/
  hδ : 0 < δ
  /-- The rounds partition the total time `t`. -/
  hsteps : (copies : ℝ) * δ = t
  /-- Iterating the step channel `copies` times approximates the exact
  evolution of every input state to operator-norm accuracy `ε`. -/
  accurate : ∀ σ : Operator d,
    ‖((step δ)^[copies]) σ - timeEvolution H t * σ * (timeEvolution H t)ᴴ‖ ≤ ε

end Qatlib.Papers.BayesDeepNet18.MainResults
