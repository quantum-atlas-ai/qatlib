/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIQuadOpt25.MainResults.Source.AlgorithmModel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# DQIQuadOpt25 — Theorem 1 (max-QUADSAT DQI state preparation)

Fixed arXiv:2510.08061v2, Theorem 1, p.3 (Algorithm 1, pp.9–10).

The paper's Theorem 1 states: there is an efficient algorithm (Algorithm 1)
that prepares the DQI state for max-QUADSAT when `b_i = 0`, the `C_i` are
diagonal, and the diagonals of the `C_i` are columns of a parity-check matrix
with an efficient decoding scheme.

Modelling notes.

* `IsDiagonalInstance inst` is exactly the hypothesis "`b_i = 0` and every `C_i`
  is diagonal".  Symmetry of the `C_i` (Definition 1) is automatic for the
  diagonal instances, see `isSymmetric_of_isDiagonal`.
* The parity-check matrix is `diagVector inst : Fin m → Fin n → F_p`, whose
  `i`-th column is the diagonal of `C_i`.  `HasEfficientDecoder` is the
  paper's "efficient decoding scheme": a single-valued decoder for
  `y ↦ Dᵀy`, correct on all error vectors of weight at most `ℓ`, with
  polynomially bounded declared cost.
* `PreparesIn` is the declared-resource state-preparation model of
  `AlgorithmModel.lean`: the conclusion asserts the existence of a procedure
  producing exactly the DQI amplitude vector of `P` with cost bounded by a
  polynomial in `m`, `n` and `p`.  This subsumes the paper's standing
  assumptions `m = poly(n)` and `p = poly(n)`.
* The paper's own disclaimer (p.1, 2026-03-09) says that Step 7 of Algorithm 1
  is flawed and "invalidates (Theorem 1)/(algorithm 1) as of now"; the claim
  is nevertheless the paper's stated theorem and is formalised verbatim.  See
  the statement-only definition below for the exact gap.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIQuadOpt25.MainResults

open Qatlib.Papers.DQIQuadOpt25.MainResults.Source

/-- **Theorem 1 of arXiv:2510.08061v2 (p.3).**

There is an efficient algorithm preparing the DQI state of a max-QUADSAT
instance with `b_i = 0` and diagonal `C_i`, whenever the diagonals of the
`C_i` form the columns of a parity-check matrix with an efficient decoding
scheme.  Concretely: for every degree-`≤ ℓ` polynomial `P`, the amplitude
vector `x ↦ P(f(x))` is produced by some state-preparation procedure whose
declared cost is bounded by `(m + n + p)^c + 1` for some `c`.

The proof follows Algorithm 1 (Steps 1–8, pp.9–10): prepare the weight
register from the classically precomputed weights `w_k` (Step 1), prepare the
Dicke state (Step 2), uncompute the weight register (Step 3), create the error
register with the single-constraint Fourier transforms `G_i` (Step 4), compute
the syndrome `Dᵀy` (Step 5), decode it to uncompute the error register
(Step 6), apply `F_0` on each syndrome subregister (Step 7), and finally apply
the QFT (Step 8), which by Claim 6 (Eq. (25)) yields the DQI state.

Formalization gap.  The paper's Step 7 contains an acknowledged
error (disclaimer of 2026-03-09): applying `F_0` to each subregister involves a
measurement succeeding with probability `1/8`, so the step only succeeds with
probability `8^{-m}`; the paper gives no repair.  Consequently the existence
of a procedure with the claimed correctness is not derivable from the paper's
current text.  The statement is kept faithful to Theorem 1.  Remaining
ingredients to formalise on a future repair: an explicit `F_0` unitary
(Primitive 1/4), the reversible syndrome computation and its uncomputation by
the decoder (`EfficientDecoder.correct`, already available), and the QFT
identity of Claim 6, Eq. (24)–(25).  Once Theorem 1's Step 7 is repaired, the
proof should construct `StateProcedure` from the gate list and bound its cost
by the decoder, Dicke-state and QFT costs.

Candidate reusable dependencies: `HasEfficientDecoder` and
`EfficientDecoder.correct` (this repository, `Source/AlgorithmModel.lean`);
`dotProduct_mulVec_of_diagonal` and `constraintArg_diagonal`
(`Source/PaperModel.lean`). -/
def theorem1_maxQUADSAT_statePrep
    {p n m ℓ : ℕ} [Fact p.Prime]
    (inst : QUADSATInstance p n m) (hinst : IsDiagonalInstance inst)
    (hdec : HasEfficientDecoder (m := m) (n := n) (ℓ := ℓ) (diagVector inst))
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ ℓ) : Prop := ∃ c : ℕ, PreparesIn (dqiAmplitude inst P) ((m + n + p) ^ c + 1)

/-- The degree-`ℓ` DQI state is, by definition, among the states covered by
Theorem 1: the conclusion is stated for the explicit amplitude vector
`dqiState inst P`. -/
theorem theorem1_prepares_dqiState
    {p n m ℓ : ℕ} [Fact p.Prime]
    (inst : QUADSATInstance p n m) (hinst : IsDiagonalInstance inst)
    (hdec : HasEfficientDecoder (m := m) (n := n) (ℓ := ℓ) (diagVector inst))
    (P : Polynomial ℂ) (hdeg : P.natDegree ≤ ℓ)
    (hprep : theorem1_maxQUADSAT_statePrep inst hinst hdec P hdeg) :
    ∃ c : ℕ, PreparesIn (dqiState inst P) ((m + n + p) ^ c + 1) :=
  hprep

end Qatlib.Papers.DQIQuadOpt25.MainResults
