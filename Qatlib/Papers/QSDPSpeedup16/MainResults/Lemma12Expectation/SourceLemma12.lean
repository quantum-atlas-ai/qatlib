/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.RationalScan.Step2Scan.MatrixOptimizationAlgorithms
import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12 (source restatement)

Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*, fixed
arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Lemma 12 is printed on p. 15 (proof on the same page).

Source statement: given an `s`-sparse `n × n` Hermitian `A` with `‖A‖ ≤ 1` and a
density matrix `ρ`, with probability larger than `1 − p_e` one can compute
`tr(ρA)` with additive error `ε` in time
`O(s ε⁻² log⁴(ns/(p_e ε)))` using `O(log(1/p_e) ε⁻²)` copies of `ρ`.

Encoded here: a finite probability law over real estimates whose good event has
mass at least `1 − p_e` and on which the estimate is within `ε` of
`tr(ρA)`, together with the copy and time budgets (with the explicit constant
`8` and the `4` inside the logarithm, as in the library's
`ExpectationEstimationBudget`).  The estimate is produced by the library
theorem `Qatlib.Concepts.RationalScan.Step2Scan.expectationClause_valid`
(the diagonal exact-expectation law). Scope note: the source's
phase-estimation + Chernoff implementation of the sampler and the sparsity
structure of `A` are outside the scope of this file; only the parameter `s`
is used.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma12Expectation

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.RationalScan.Step2Scan

/-- Lemma 12 (p. 15): there is a finite probability law over estimates of `tr(ρA)` such
that the event "additive error at most `ε`" has probability at least `1 − p_e`, using at
most `8 log(1/p_e)/ε²` copies of `ρ` and time
`8 s ε⁻² log⁴(4ns/(p_e ε))`. -/
theorem lemma12_expectationEstimation (n s : ℕ) (A ρ : Operator n) (ε p_e : ℝ)
    (hn : 0 < n) (hs : 0 < s) (hε : 0 < ε) (hp : 0 < p_e) (hp1 : p_e < 1)
    (hρ : IsDensityOperator ρ) (hA : A.IsHermitian ∧ ‖A‖ ≤ 1) :
    ∃ (Ω : ℕ) (w : Fin Ω → ℝ) (est : Fin Ω → ℝ) (copies time : ℝ),
      0 < Ω ∧ IsProbLaw w ∧
      1 - p_e ≤ eventProb w (fun ω => |est ω - (Matrix.trace (A * ρ)).re| ≤ ε) ∧
      copies ≤ 8 * Real.log (1 / p_e) / ε ^ 2 ∧
      time ≤ 8 * (s : ℝ) / ε ^ 2 *
        (Real.log (4 * (n : ℝ) * (s : ℝ) / (p_e * ε))) ^ 4 := by
  obtain ⟨Ω, w, estA, estC, copies, meas, copiesO, oracle, hΩ, hlaw, hbud, hevent⟩ :=
    expectationClause_valid n 1 (fun _ => A) A ρ n s ε p_e hn hn (by norm_num) hs hε hp hp1
      hρ (fun _ => hA) hA
  refine ⟨Ω, w, fun ω => estA ω 0, copies, meas, hΩ, hlaw, ?_, ?_, ?_⟩
  · -- The event implies the single-estimate event at coordinate `0`.
    have hmono :
        eventProb w (fun ω => (∀ i : Fin 1,
            |estA ω i - (Matrix.trace (A * ρ)).re| ≤ ε) ∧
          |estC ω - (Matrix.trace (A * ρ)).re| ≤ ε) ≤
        eventProb w (fun ω => |estA ω 0 - (Matrix.trace (A * ρ)).re| ≤ ε) := by
      unfold eventProb
      apply Finset.sum_le_sum
      intro ω _
      by_cases hP : (∀ i : Fin 1, |estA ω i - (Matrix.trace (A * ρ)).re| ≤ ε) ∧
          |estC ω - (Matrix.trace (A * ρ)).re| ≤ ε
      · have hQ : |estA ω 0 - (Matrix.trace (A * ρ)).re| ≤ ε := hP.1 0
        simp [hP]
      · rw [if_neg hP]
        by_cases hQ : |estA ω 0 - (Matrix.trace (A * ρ)).re| ≤ ε
        · simp [hQ, hlaw.1 ω]
        · simp [hQ]
    linarith
  · exact hbud.2.2.2.1
  · exact hbud.2.2.2.2.1

end Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma12Expectation
