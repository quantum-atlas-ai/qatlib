/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Qatlib.Papers.DissipNonlin20.MainResults.LowerBound

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# DissipNonlin20 — Theorem 1 error decomposition and algorithm records

Source: arXiv:2011.03185, Theorem 1 (pp. 5-6, Eqs. (3.13)-(3.15)).

This module preserves the closed support of the original development of
this material: the explicit prefactor and poly-log argument of the (3.14) bound,
the `CarlemanAlgorithm` record, and `theorem1_error_decomposition`.

`theorem1_statement` and `theorem1_statement_real_eigenvalues` remain
model-contract deferrals of this development: the conclusion is an
existential over `CarlemanAlgorithm` records whose `correct` field is an
unconstrained proposition, so the statement is only vacuously satisfiable
(`Alg` with `correct := True` and zero complexity fields witnesses it); a
faithful theorem needs a circuit/oracle/QLSA complexity semantics, which the
legacy model does not carry.
-/

set_option autoImplicit false

namespace Qatlib.Papers.DissipNonlin20.MainResults.MainTheorem

noncomputable section

/-- The prefactor of the query-complexity bound (3.14) in Theorem 1:
`sT²q[(‖F₂‖+‖F₁‖+‖F₀‖)² + ‖F₀'‖] / ((1-‖u_in‖)²(‖F₂‖+‖F₀‖)gε)`. -/
def theorem1Prefactor (s T q F2 F1 F0 F0' uin g eps : ℝ) : ℝ :=
  s * T ^ 2 * q * ((F2 + F1 + F0) ^ 2 + F0') /
    ((1 - uin) ^ 2 * (F2 + F0) * g * eps)

/-- The argument of the polylogarithmic factor in (3.14):
`s T ‖F₂‖‖F₁‖‖F₀‖‖F₀'‖ / ((1-‖u_in‖) g ε)`. -/

def theorem1PolyLogArg (s T F2 F1 F0 F0' uin g eps : ℝ) : ℝ :=
  s * T * F2 * F1 * F0 * F0' / ((1 - uin) * g * eps)

/-- A quantum algorithm for the quantum quadratic ODE problem of Problem 1, recorded by its
quantitative performance: approximation error, success probability, and query and gate
complexities.  The residual field `correct` is the semantic specification that the output
state approximates `u(T)/‖u(T)‖` to within `errorBound`. -/

structure CarlemanAlgorithm where
  /-- Error in trace distance between the output state and `u(T)/‖u(T)‖`. -/
  errorBound : ℝ
  /-- Success probability of the postselection, with a flag indicating success. -/
  successProb : ℝ
  /-- Query complexity (number of queries to `O_{F₂}, O_{F₁}, O_{F₀}, O_x`). -/
  queryComplexity : ℝ
  /-- Gate complexity. -/
  gateComplexity : ℝ
  /-- The approximation specification. -/
  correct : Prop

/-- **Theorem 1, Section 4.1 error decomposition (printed p. 6).**  The total error of the
algorithm is the sum of the Carleman truncation error, the Euler discretisation error and the
QLSA error; if each of the three contributions is at most `ε/3`, the total is at most `ε`.
This is the arithmetic content of the statement "the error has three contributions" in
Section 4.1. -/

theorem theorem1_error_decomposition (ε1 ε2 ε3 ε : ℝ)
    (h1 : ε1 ≤ ε / 3) (h2 : ε2 ≤ ε / 3) (h3 : ε3 ≤ ε / 3)
    (_hε : 0 ≤ ε) :
    ε1 + ε2 + ε3 ≤ ε := by
  linarith

/- **Theorem 1 (printed pp. 5--6, Eqs. (3.13)--(3.15)): end-to-end complexity.**

Consider a quantum quadratic ODE instance with `s = ‖·‖₀`-sparsity, dimension parameter `n`,
evolution time `T`, and `g = ‖u(T)‖`, `q = ‖u_in‖/‖u(T)‖` (3.13).  Assume `R < 1` and
`‖F₀‖ ≤ ‖F₂‖`.  Then there is a quantum algorithm producing a state approximating
`u(T)/‖u(T)‖` within error `ε ≤ 1`, succeeding with probability `Ω(1)` and a success flag,
whose query complexity is at most the bound (3.14)

`C · sT²q[(‖F₂‖+‖F₁‖+‖F₀‖)² + ‖F₀'‖] / ((1-‖u_in‖)²(‖F₂‖+‖F₀‖)gε) ·
   (log(sT‖F₂‖‖F₁‖‖F₀‖‖F₀'‖/((1-‖u_in‖)gε)))^K / log(1/‖u_in‖)`

for some constants `C, K > 0` (the paper's `poly log` written explicitly as a fixed power),
and whose gate complexity is larger by a factor `D · (log(arg))^L / log(1/‖u_in‖)`.  This is
the paper's (3.14) and the following gate-complexity sentence.  The real-eigenvalue variant
(3.15) is the same statement without the factor `q`; it is recorded in the docstring of
`theorem1_statement_real_eigenvalues` below. -/



end

end Qatlib.Papers.DissipNonlin20.MainResults.MainTheorem
