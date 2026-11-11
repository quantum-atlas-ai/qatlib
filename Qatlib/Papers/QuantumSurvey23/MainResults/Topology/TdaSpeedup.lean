/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c015 — Topological data analysis: quadratic speedup, no exponential one

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 9.4 (arXiv source lines 9207–9211).

Source conclusion: (a) for clique-dense complexes the quantum Betti-number
algorithm of [refs] gives a quadratic speedup over the classical power method /
sparse numerical linear algebra; (b) for general graphs no exponential speedup
is possible, because the problem is NP-hard (QMA-hard in the weighted setting)
[refs 15,16,17].

Formalization notes:
* `powerMethodCost S = |S|` (classical power-method work on `S` simplices),
  `quantumTdaCost S = ceil(√|S|)`; `tda_quadratic_speedup` is the two-sided
  quadratic bound;
* `HasExponentialSpeedup classical quantum` means the quantum work is
  polylogarithmic while the classical work exceeds every constant multiple of
  `log N` — an exponential separation;
* `NotInBQP quantum` records the cited hardness barrier: no polynomial-time
  (hence no polylogarithmic) quantum algorithm solves the general-graph problem.

The second theorem, `no_exponential_speedup_general_graph`, is a complete proof
of the implication "if the general-graph problem has no polynomial-time quantum
algorithm, then it admits no exponential quantum speedup".  The hardness
hypothesis itself is the cited NP/QMA-hardness result and is not re-proved here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Topology

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Classical power-method work for a simplex set of size `S`. -/
def powerMethodCost (S : ℕ) : ℕ := S

/-- Quantum Betti-number cost for a simplex set of size `S`. -/
def quantumTdaCost (S : ℕ) : ℕ := sqrtCost S

/-- **c015a (Section 9.4).** On a clique-dense complex with `S` simplices
the quantum algorithm makes at most `√S` work where the power method makes `S`,
and the search space `S` is below `(√S+1)²`: a quadratic speedup. -/
theorem tda_quadratic_speedup (S : ℕ) (hS : 2 ≤ S) :
    quantumTdaCost S ≤ powerMethodCost S ∧ S ≤ (quantumTdaCost S) ^ 2 := by
  refine ⟨sqrtCost_le S hS, ?_⟩
  exact le_of_lt (sqrtCost_sq_gt S)

/-- An *exponential speedup*: quantum work is polylogarithmic in the problem
size while the classical work beats every fixed multiple of `log N`. -/
def HasExponentialSpeedup (classical quantum : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ N, quantum N ≤ Nat.log2 N + 1 ∧ C * (Nat.log2 N + 1) < classical N

/-- The cited hardness barrier: no polynomial-time quantum algorithm solves the
general-graph problem.  This is the consequence of NP- or QMA-hardness under the
standard `NP ⊄ BQP` / `QMA ⊄ BQP` assumptions. -/
def NotInBQP (quantum : ℕ → ℕ) : Prop :=
  ¬ ∃ C d, ∀ N, quantum N ≤ polyCost C d N

/-- **c015b (Section 9.4).** No exponential speedup for general graphs:
if the general-graph Betti-number problem has no polynomial-time quantum
algorithm (the NP/QMA-hardness barrier), then no quantum algorithm for it can
have an exponential speedup over the classical cost. -/
theorem no_exponential_speedup_general_graph
    (classical quantum : ℕ → ℕ) (hHard : NotInBQP quantum) :
    ¬ HasExponentialSpeedup classical quantum := by
  rintro ⟨C, hC⟩
  apply hHard
  refine ⟨1, 1, fun N => ?_⟩
  have h1 : quantum N ≤ Nat.log2 N + 1 := (hC N).1
  have h2 : Nat.log2 N + 1 ≤ N + 1 := by
    have hlog := Nat.log_le_self 2 N
    rw [Nat.log2_eq_log_two]
    omega
  simp only [polyCost]
  exact le_trans h1 (by simpa using h2)

/-- **c015 (Section 9.4), combined assessment.** Quadratic speedup in the
clique-dense regime; no exponential speedup in general. -/
theorem tda_assessment (S : ℕ) (hS : 2 ≤ S) (classical quantum : ℕ → ℕ)
    (hHard : NotInBQP quantum) :
    (quantumTdaCost S ≤ powerMethodCost S ∧ S ≤ (quantumTdaCost S) ^ 2) ∧
    ¬ HasExponentialSpeedup classical quantum :=
  ⟨tda_quadratic_speedup S hS, no_exponential_speedup_general_graph classical quantum hHard⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Topology
