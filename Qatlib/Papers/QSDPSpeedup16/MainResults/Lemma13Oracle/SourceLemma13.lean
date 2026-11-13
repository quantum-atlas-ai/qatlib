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
# Lemma 13 (source restatement)

Brandão–Svore, *Quantum Speed-ups for Semidefinite Programming*, fixed
arXiv:1609.05537v5 (PDF SHA-256
746714c3d97424df74d7f5956107687f73c6501403e35af757421328dfb030b7).
Lemma 13 is printed on pp. 15–16 (proof on p. 16).

Source statement: using `O(log(m/p_e) h_precision⁻²)` copies of `ρ` and time
`O(s h_precision⁻² log⁴(nms/(p_e h_precision)))`, one can implement the oracle
`O[h]` with error probability `p_e`.  The proof applies Lemma 12 to each of the
`m` expectations `tr(Aᵢρ)` and takes a union bound, giving all estimates
`h_precision`-close with probability `1 − m p_e'`.

Encoded here: a finite probability law over `m`-tuples of estimates such that the
event "every estimate is within `h` of `tr(Aᵢρ)`" has mass at least `1 − p_e`,
with the `m`-fold copy and oracle-time budgets (explicit constant `8`, `4` inside
the logarithm, matching the library's `ExpectationEstimationBudget`).  The law is
the library's exact-expectation law of
`Qatlib.Concepts.RationalScan.Step2Scan.expectationClause_valid`.

Scope note: this module formalizes the estimate law and budgets. The oracle
`O[h]` as a quantum channel `∑ cᵢ|i⟩ ↦ ∑ cᵢ|i, eᵢ⟩`, its
phase-estimation/Chernoff implementation, and the sparsity structure of the
`Aᵢ` are outside its scope; only the parameter `s` is used.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma13Oracle

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Concepts.RationalScan.Step2Scan

/-- Lemma 13 (pp. 15–16): there is a finite probability law over `m`-tuples of
estimates such that every `tr(Aᵢρ)` is estimated within `h` on an event of probability at
least `1 − p_e`, using at most `8 log(m/p_e)/h²` copies of `ρ` and oracle time
`8 s h⁻² log⁴(4nms/(p_e h))`. -/
theorem lemma13_oracleImplementation (n m s : ℕ) (A : Fin m → Operator n) (ρ : Operator n)
    (h p_e : ℝ) (hn : 0 < n) (hm : 0 < m) (hs : 0 < s) (hh : 0 < h)
    (hp : 0 < p_e) (hp1 : p_e < 1) (hρ : IsDensityOperator ρ)
    (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) :
    ∃ (Ω : ℕ) (w : Fin Ω → ℝ) (estA : Fin Ω → Fin m → ℝ) (copiesO oracle : ℝ),
      0 < Ω ∧ IsProbLaw w ∧
      1 - p_e ≤ eventProb w (fun ω => ∀ i,
        |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
      copiesO ≤ 8 * Real.log ((m : ℝ) / p_e) / h ^ 2 ∧
      oracle ≤ 8 * (s : ℝ) / h ^ 2 *
        (Real.log (4 * (n : ℝ) * (m : ℝ) * (s : ℝ) / (p_e * h))) ^ 4 := by
  obtain ⟨Ω, w, estA, estC, copies, meas, copiesO, oracle, hΩ, hlaw, hbud, hevent⟩ :=
    expectationClause_valid n m A (A ⟨0, hm⟩) ρ n s h p_e hn hn hm hs hh hp hp1
      hρ hA (hA ⟨0, hm⟩)
  refine ⟨Ω, w, estA, copiesO, oracle, hΩ, hlaw, ?_, ?_, ?_⟩
  · -- The conjunction implies the all-`m` estimate event.
    have hmono :
        eventProb w (fun ω => (∀ i : Fin m,
            |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
          |estC ω - (Matrix.trace (A ⟨0, hm⟩ * ρ)).re| ≤ h) ≤
        eventProb w (fun ω => ∀ i : Fin m,
          |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h) := by
      unfold eventProb
      apply Finset.sum_le_sum
      intro ω _
      by_cases hP : (∀ i : Fin m,
          |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h) ∧
          |estC ω - (Matrix.trace (A ⟨0, hm⟩ * ρ)).re| ≤ h
      · simp [hP]
      · rw [if_neg hP]
        by_cases hQ : ∀ i : Fin m, |estA ω i - (Matrix.trace (A i * ρ)).re| ≤ h
        · simp [hQ, hlaw.1 ω]
        · simp [hQ]
    linarith
  · exact hbud.2.2.2.2.2.1
  · exact hbud.2.2.2.2.2.2

end Qatlib.Papers.QSDPSpeedup16.MainResults.Lemma13Oracle
