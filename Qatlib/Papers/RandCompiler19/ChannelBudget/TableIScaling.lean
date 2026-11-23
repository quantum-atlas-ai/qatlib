/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftCore

@[expose] public section

/-!
# Table I scaling of the qDRIFT component budget

Table I of [Campbell2019] records the dependence of the qDRIFT rotation count on the number
of Hamiltonian components `L`. In the source, `Λ` bounds the coefficients of normalized
components and `λ = ∑ j, |h_j|` is their total weight. The table distinguishes two regimes:

* `λ = Λ * L`, giving `L²` growth;
* `λ = Λ * sqrt L`, giving `L` growth.

Here the law `d` gives the coefficients `λ * d.prob j` of the Hermitian contractions.
The statements use the specified total weight and hold for every such law, including
source instances whose coefficients are bounded by `Λ`.

The locked library proves the native exponential-macro budget `N ≤ 2 * λ² * t² / ε + 1`
with the finite diamond distance at most `ε`. This module substitutes the two source
parameterizations into that bound and records a *uniform* constant for both. No asymptotic
notation is used: the same numerical constant `C = 2` works for every component count,
dimension, time and precision.

## Main statements

* `tableI_linear_component_scaling`: for `λ = Λ * L` the budget grows as `L²`.
* `tableI_sqrt_component_scaling`: for `λ = Λ * sqrt L` the budget grows as `L`.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option autoImplicit false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.RandCompiler19.ChannelBudget

open Matrix
open scoped Matrix.Norms.L2Operator ENNReal BigOperators

/-- The precision-driven qDRIFT step count is always positive. -/
private theorem qdriftSteps_pos (lam t ε : ℝ) : 0 < qdriftSteps lam t ε := by
  unfold qdriftSteps
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- Table I of [Campbell2019] in the linear-weight regime `λ = Λ * L`. A single constant
`C = 2` bounds every `L`-component qDRIFT budget and the corresponding finite diamond
distance simultaneously. -/
theorem tableI_linear_component_scaling :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L D : ℕ) (_ : 1 ≤ L) (_ : 0 < D)
        (d : FinDist (Fin L)) (K : Fin L → Operator D)
        (Λ t ε : ℝ) (_ : 0 ≤ Λ) (_ : 0 < ε)
        (_ : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1),
        let N := qdriftSteps (Λ * (L : ℝ)) t (2 * ε)
        0 < N ∧
        (N : ℝ) ≤ C * Λ ^ 2 * (L : ℝ) ^ 2 * t ^ 2 / ε + 1 ∧
        finiteDiamondDistance (exactQdriftMap d K (Λ * (L : ℝ)) t N)
          (conjBranch (HamiltonianEvolution
            (qdriftHamiltonian d K (Λ * (L : ℝ))) t)) ≤ ENNReal.ofReal ε := by
  refine ⟨2, by norm_num, ?_⟩
  intro L D hL hD d K Λ t ε hΛ hε hK
  have hlam : 0 ≤ Λ * (L : ℝ) := mul_nonneg hΛ (by positivity)
  have hbudget := (exact_qdrift_actual_finite_diamond_budget L D d K
    (Λ * (L : ℝ)) t (qdriftSteps (Λ * (L : ℝ)) t (2 * ε)) hlam
      (qdriftSteps_pos _ _ _) hK).2 ε hε
  dsimp only
  refine ⟨hbudget.1, ?_, hbudget.2.2⟩
  refine hbudget.2.1.trans_eq ?_
  ring

/-- Table I of [Campbell2019] in the square-root-weight regime `λ = Λ * sqrt L`. The same
uniform constant `C = 2` controls the component budget, which now grows only linearly in
`L`, together with the finite diamond distance at most `ε`. -/
theorem tableI_sqrt_component_scaling :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L D : ℕ) (_ : 1 ≤ L) (_ : 0 < D)
        (d : FinDist (Fin L)) (K : Fin L → Operator D)
        (Λ t ε : ℝ) (_ : 0 ≤ Λ) (_ : 0 < ε)
        (_ : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1),
        let lam := Λ * Real.sqrt (L : ℝ)
        let N := qdriftSteps lam t (2 * ε)
        0 < N ∧
        (N : ℝ) ≤ C * Λ ^ 2 * (L : ℝ) * t ^ 2 / ε + 1 ∧
        finiteDiamondDistance (exactQdriftMap d K lam t N)
          (conjBranch (HamiltonianEvolution (qdriftHamiltonian d K lam) t)) ≤
            ENNReal.ofReal ε := by
  refine ⟨2, by norm_num, ?_⟩
  intro L D hL hD d K Λ t ε hΛ hε hK
  have hLnonneg : (0 : ℝ) ≤ L := by positivity
  have hlam : 0 ≤ Λ * Real.sqrt (L : ℝ) := mul_nonneg hΛ (Real.sqrt_nonneg _)
  have hbudget := (exact_qdrift_actual_finite_diamond_budget L D d K
    (Λ * Real.sqrt (L : ℝ)) t
    (qdriftSteps (Λ * Real.sqrt (L : ℝ)) t (2 * ε)) hlam
      (qdriftSteps_pos _ _ _) hK).2 ε hε
  dsimp only
  refine ⟨hbudget.1, ?_, hbudget.2.2⟩
  refine hbudget.2.1.trans_eq ?_
  have hsq : (Λ * Real.sqrt (L : ℝ)) ^ 2 = Λ ^ 2 * (L : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hLnonneg]
  rw [hsq]
  ring

end Qatlib.Papers.RandCompiler19.ChannelBudget
