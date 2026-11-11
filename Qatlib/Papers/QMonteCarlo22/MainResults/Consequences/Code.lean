/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Average

set_option backward.isDefEq.respectTransparency false

/-!
# Specification-level model of "the code" and of query-complexity procedures

Fixed arXiv version: `2208.07544v1`.  Source locations: §1 (Equation (2)), §4
(Equation (69)) and Appendix A of Kothari--O'Donnell, *Mean estimation when you have
the source code; or, quantum Monte Carlo methods*.

The paper's computational model is a quantum circuit with oracle access to the code
of a real random variable `y`.  The circuit-level model (unitary gates, oracle
reversibility, gate complexity) is *not* formalized anywhere in this repository, and
formalizing it is out of scope for the paper layer.  What is formalized here is the
*specification interface* that every query-complexity statement of the paper uses:

* `Code`: a probability law on `ℝ`, the distribution of the random variable `y`;
* `Code.mean`, `Code.secondMoment`, `Code.variance`, `Code.stdDev`: the quantities
  `μ`, `s²`, `σ²`, `σ` of Equations (28) and (69);
* `Procedure α`: a procedure is specified by a query budget (a function of the
  accuracy parameter) and the law of its output; the actual quantum circuit is left
  implicit, exactly as the paper's query-complexity theorems leave it implicit;
* `winProb`: the probability that the output lies in a prescribed "good" set,
  computed from the output law.

All theorems in `QueryClaims.lean` are stated over this interface, so their
conclusions (query budgets and success probabilities) are meaningful mathematical
statements; what is missing is the construction of the procedures, which is the
quantum-algorithmic content of the paper.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Qatlib.Papers.QMonteCarlo22.MainResults.Consequences

/-- A code for a real-valued random variable: a probability measure on `ℝ`. -/
abbrev Code : Type := ProbabilityMeasure ℝ

namespace Code

/-- Equation (69): `μ = E_p[y]`. -/
def mean (y : Code) : ℝ := ∫ x, x ∂(y : Measure ℝ)

/-- Equation (69): `s² = E_p[y²]`. -/
def secondMoment (y : Code) : ℝ := ∫ x, x ^ 2 ∂(y : Measure ℝ)

/-- Equation (69): `σ² = Var_p[y]`, in its centred form. -/
def variance (y : Code) : ℝ := ∫ x, (x - mean y) ^ 2 ∂(y : Measure ℝ)

/-- Equation (69): `σ = stddev[y]`. -/
def stdDev (y : Code) : ℝ := Real.sqrt (variance y)

end Code

/-- A randomized procedure with oracle access to the code of `y`.

`queryBudget ε` is the number of queries used when the accuracy parameter is `ε`
(the paper's `O(1/ε)` or `O(n)` counts), and `outputLaw ε` is the law of the output
when the accuracy parameter is `ε`.  The quantum circuit realizing the procedure is
not modelled; this is the same level of abstraction at which the paper states its
query-complexity theorems. -/
structure Procedure (α : Type*) [MeasurableSpace α] where
  /-- Number of queries to the code, as a function of the accuracy parameter. -/
  queryBudget : ℝ → ℕ
  /-- Law of the output, as a function of the accuracy parameter. -/
  outputLaw : ℝ → ProbabilityMeasure α

/-- The probability that the output of `P` at accuracy `ε` lies in the good set. -/
def winProb {α : Type*} [MeasurableSpace α] (P : Procedure α) (ε : ℝ)
    (good : Set α) : ℝ :=
  ((P.outputLaw ε : Measure α) good).toReal

/-- The output of a decision procedure is a `Bool`; `true` denotes the second case. -/
abbrev DecisionProcedure : Type := Procedure Bool

end Qatlib.Papers.QMonteCarlo22.MainResults.Consequences
