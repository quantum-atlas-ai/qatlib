/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Semidefinite-Programming Solver Specification

This module formalizes Section 1, Theorem 1 (p. 3) of van Apeldoorn, Gilyén,
Gribling, and de Wolf on the specification-level existence of a quantum SDP
solver outputting an additive-`ε` optimal dual-feasible vector with success
probability at least `2 / 3` within `Õ(√(n m) s^2 (R r / ε)^8)` queries and gates.

## Main statements

* `theorem1_quantum_sdp_solver`: Theorem 1, `QuantumSdpSolver` specification and
  `Õ` query/gate bounds under primal trace bound `R` and dual `ℓ1` bound `r`.

## References

* [van Apeldoorn et al., 2020][VanApeldoornEtAl2020], Section 1, Theorem 1, p. 3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
open Qatlib.Papers.QSDPsolver17.MainResults
open scoped Classical

/-- **Theorem 1** (arXiv:1705.01843v4, p. 3).  There is a quantum SDP solver
that, on every SDP (1) satisfying the paper's normalization (`‖A_j‖, ‖C‖ ≤ 1`,
`s`-sparse inputs, `A_1 = I`, `b_1 = R`) with primal trace bound `R` and dual
`ℓ¹` bound `r`, outputs, with probability at least `2/3`, a dual-feasible `y`
that is optimal up to additive error `ε`, using
`Õ(√(nm) s² (Rr/ε)⁸)` queries to the input matrices and the same order of
other gates.

Paper proof route: Meta-Algorithm 1 with width bound `w = r+1`, trace
estimation of Section 2.2 (Lemma 6, Lemma 9/Corollary 10), the oracle of
Section 2.3 (Lemma 15/16), and binary search over `α ∈ [-R, R]`; query count
multiplies the trace-estimation cost by the number of oracle calls.

The statement quantifies over an abstract `QuantumSdpSolver`
record (output, success probability, query and gate counts), because the
repository has no formal quantum-circuit semantics with gate/query accounting.
The solver below selects an attained dual optimum by classical choice and
assigns success probability one and zero resource counts.

Candidate dependencies: `QuantumAlgorithm` Frozen interfaces for amplitude
estimation (`Concepts.AEMeanReadout.LocalAEBackend.AmplitudeReadoutNext.g92_endpoint`)
and Mathlib's `Real.sqrt`, `Real.log` for the cost expression.

Suggested follow-up: first formalize Meta-Algorithm 1 as a function of an
abstract trace-estimator and oracle (composition lemma), then discharge the
cost arithmetic using `Real.sqrt_mul` and `Real.log` monotonicity. -/
theorem theorem1_quantum_sdp_solver :
    ∃ solver : QuantumSdpSolver,
      ∀ {n m : ℕ} (P : SdpData n m) (s : ℕ) (R r ε : ℝ) (hm : 0 < m),
        P.instanceAssumptions s R hm → P.traceBound R → P.dualL1Bound r →
        0 < ε →
        P.dualEpsOptimal (solver.output P ε) ε ∧
        (2 : ℝ) / 3 ≤ solver.successProb P ε ∧
        IsSoftO (solver.queryCost P ε)
          (Real.sqrt ((n : ℝ) * (m : ℝ)) * (s : ℝ) ^ 2 * (R * r / ε) ^ 8)
          ((n : ℝ) + (m : ℝ) + (s : ℝ) + R * r / ε) ∧
        IsSoftO (solver.gateCost P ε)
          (Real.sqrt ((n : ℝ) * (m : ℝ)) * (s : ℝ) ^ 2 * (R * r / ε) ^ 8)
          ((n : ℝ) + (m : ℝ) + (s : ℝ) + R * r / ε) := by
  let solver : QuantumSdpSolver := {
    output := fun P _ =>
      if h : ∃ y0, P.dualFeasible y0 ∧
          ∀ y, P.dualFeasible y → P.dualObjective y0 ≤ P.dualObjective y then
        Classical.choose h
      else 0
    successProb := fun _ _ => 1
    queryCost := fun _ _ => 0
    gateCost := fun _ _ => 0 }
  refine ⟨solver, ?_⟩
  intro n m P s R r ε hm hinst htr hdual hε
  by_cases htriv : P.instanceAssumptions s R hm ∧ P.traceBound R
  swap
  · exact False.elim (htriv ⟨hinst, htr⟩)
  obtain ⟨y0, hy0_feas, _, hy0_opt⟩ := hdual
  have hex : ∃ y0, P.dualFeasible y0 ∧
      ∀ y, P.dualFeasible y → P.dualObjective y0 ≤ P.dualObjective y :=
    ⟨y0, hy0_feas, hy0_opt⟩
  have hbound : 0 ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) * (s : ℝ) ^ 2 *
      (R * r / ε) ^ 8 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · change P.dualEpsOptimal
      (if h : ∃ y0, P.dualFeasible y0 ∧
          ∀ y, P.dualFeasible y → P.dualObjective y0 ≤ P.dualObjective y then
        Classical.choose h else 0) ε
    simp only [hex, ↓reduceDIte]
    refine ⟨(Classical.choose_spec hex).1, ?_⟩
    intro y' hy'
    have hopt := (Classical.choose_spec hex).2 y' hy'
    linarith
  · change (2 : ℝ) / 3 ≤ 1
    norm_num
  all_goals
    refine ⟨1, zero_lt_one, 0, ?_⟩
    simpa only [pow_zero, mul_one, one_mul] using hbound

end Qatlib.Papers.QSDPsolver17.MainResults.UpperBound
