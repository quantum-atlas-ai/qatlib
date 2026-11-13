/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.ApproxGibbs
import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpStep2SampledOracle
import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpWidthSlackPayoffRangeQuan
import Qatlib.Concepts.SdpMmwSolver.SdpContract.SdpConvexCombinationSamplingQuan
import Qatlib.Concepts.SdpMmwSolver.OracleError.SdpAlphaRescaleLemma2Quan
import Qatlib.Concepts.SdpDuality.ConeSeparation.SharedMatrixOptimization

/-!
# Search decisions, sampling, and resource accounts for semidefinite programming

`step2Decision` and `step2NoOutput` express the finite search conditions for a sampled SDP
oracle. The module relates exact and relaxed width budgets, constructs dyadic mixture samplers,
and records error and resource totals using `roundErrorLedger` and `sdpRunLedger`. The no-output
implications retain an explicit selection hypothesis, and concrete examples establish limits on
universal separation and exact finite-tree sampling. See [BrandaoSvore2017] for the mathematical
setting.

## Main statements

* `clause28_complete`: packages the search equivalences and conditional separation result.
* `clause29_complete`: collects width-budget comparisons and the same-run objective bound.
* `clause30_complete`: collects sampling, error-transfer, and realization-boundary results.
* `clause31_complete`: packages shell budgets and rescaling; `clause32_complete` packages
  compiled-run resource accounts.

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SdpDuality.ConeSeparation
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G7
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G8
open Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationExecutionRefutations.G9
open Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep
open Qatlib.Concepts.SdpDuality.ConeSeparation.SamplerTree
open Qatlib.Concepts.SdpDuality.ConeSeparation.Step2Search
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SdpMmwSolver.OracleError
open Qatlib.Concepts.SdpMmwSolver.SdpContract
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

set_option autoImplicit false

namespace Qatlib.Papers.SDPBrandao16.MainResults

open Qatlib
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

/-- The cost mean, payoff mean, and cell estimate associated with a Step 2 search cell. -/
structure Step2Aggregates {m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q)
    (b : Fin m → ℝ) (k : Fin γ) (N : Fin Nmax) where

  costMean : ℝ

  payoffMean : ℝ

  cellEstimate : ℝ

/-- Computes the empirical cost and payoff means and the stored cell estimate for the specified
search cell. -/
noncomputable def step2Aggregates {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (k : Fin γ) (N : Fin Nmax) :
    Step2Aggregates S b k N :=
  { costMean := (∑ j : Fin M, b (S.draws k N j)) / M
    payoffMean := (∑ j : Fin M, S.estA k N j) / M
    cellEstimate := S.estC k N }

/-- The conjunction of the payoff and cost acceptance inequalities for a Step 2 search cell. -/
noncomputable def step2Decision {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (α R κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) : Prop :=
  (step2Aggregates S b k N).cellEstimate / Step2Search.gridMass κ N - (κ + ν)
      ≤ (step2Aggregates S b k N).payoffMean ∧
    (step2Aggregates S b k N).costMean
      ≤ α / Step2Search.gridMass κ N + R * (κ + ν)

/-- The aggregate-based Step 2 decision is equivalent to the search's acceptance predicate. -/
theorem step2Decision_iff {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (α R κ ν : ℝ)
    (k : Fin γ) (N : Fin Nmax) :
    step2Decision S b α R κ ν k N ↔ S.accepts b α R κ ν k N := by
  rfl

/-- Enumerates all search cells, with the mass-grid index varying within each outer grid index. -/
noncomputable def step2Trajectory {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) : List (Fin γ × Fin Nmax) :=
  (List.finRange γ).flatMap fun k => (List.finRange Nmax).map fun N => (k, N)

/-- The search trajectory contains `γ * Nmax` cells. -/
theorem step2Trajectory_length {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) :
    (step2Trajectory S).length = γ * Nmax := by
  simp [step2Trajectory]

/-- Every pair of valid grid indices occurs in the search trajectory. -/
theorem step2Trajectory_covers {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (k : Fin γ) (N : Fin Nmax) :
    (k, N) ∈ step2Trajectory S := by
  exact List.mem_flatMap.mpr ⟨k, List.mem_finRange k,
    List.mem_map.mpr ⟨N, List.mem_finRange N, rfl⟩⟩

/-- Every cell in the enumerated Step 2 trajectory fails its acceptance test. -/
noncomputable def step2NoOutput {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (α R κ ν : ℝ) : Prop :=
  ∀ t ∈ step2Trajectory S, ¬ step2Decision S b α R κ ν t.1 t.2

/-- Failure at every enumerated trajectory cell is equivalent to the search's no-output
predicate. -/
theorem step2NoOutput_iff {m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (α R κ ν : ℝ) :
    step2NoOutput S b α R κ ν ↔ S.noOutput b α R κ ν := by
  constructor
  · intro h k N hk
    exact h (k, N) (step2Trajectory_covers S k N)
      ((step2Decision_iff S b α R κ ν k N).mpr hk)
  · intro h t ht
    rcases List.mem_flatMap.mp ht with ⟨k, _, ht'⟩
    rcases List.mem_map.mp ht' with ⟨N, _, hcell⟩
    rw [← hcell]
    intro hk
    exact h k N hk

/-- The selection condition requiring any nonnegative separator below the width threshold to
yield an accepted search cell. -/
def step2SelectionIngredient {D m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (α R κ ν : ℝ)
    (A : Fin m → Operator D) (Cv ρ : Operator D) (ε : ℝ) : Prop :=
  ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
    eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re →
    (∑ i, z i * b i < Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε) →
    ∃ (k : Fin γ) (N : Fin Nmax), S.accepts b α R κ ν k N

/-- Under the selection condition, no output excludes every nonnegative separator meeting the
payoff threshold and lying strictly below `noCheapWidth`. -/
theorem clause21_no_output_universal {D m γ Nmax M L Q : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (A : Fin m → Operator D)
    (Cv ρ : Operator D) (α R κ ν ε : ℝ)
    (hno : step2NoOutput S b α R κ ν)
    (hsel : step2SelectionIngredient S b α R κ ν A Cv ρ ε) :
    ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
      eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re →
      ¬ (∑ i, z i * b i < Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε) := by
  intro z hz hsep
  intro hcheap
  obtain ⟨k, N, hacc⟩ := hsel z hz hsep hcheap
  exact (step2NoOutput_iff S b α R κ ν).mp hno k N hacc

/-- The fixed `G8` instance fails the corrected no-cheap-separator condition. -/
theorem clause21_universal_refuted :
    ¬ Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator
        G8.A0 G8.Cv0 G8.b0 G8.ρ8 (3:ℝ) (1:ℝ) (1/6:ℝ) :=
  Qatlib.Concepts.SdpDuality.ConeSeparation.clause16_refuted_boundary

/-- The fixed search `G8.S8` produces no accepted cell at the specified parameter values. -/
theorem clause21_frozen_no_output :
    step2NoOutput G8.S8 G8.b0 (3:ℝ) (1:ℝ) (1/100) (1/1000) := by
  rw [step2NoOutput_iff]
  exact G8.no_output

/-- Collects the search-decision and no-output equivalences, trajectory length, conditional
separator exclusion, and the fixed separator counterexample. See [BrandaoSvore2017] for the
mathematical setting. -/
theorem clause28_complete :

    (∀ {m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (α R κ ν : ℝ) (k : Fin γ) (N : Fin Nmax),
      step2Decision S b α R κ ν k N ↔ S.accepts b α R κ ν k N) ∧

    (∀ {m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q),
      (step2Trajectory S).length = γ * Nmax) ∧

    (∀ {m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (α R κ ν : ℝ),
      step2NoOutput S b α R κ ν ↔ S.noOutput b α R κ ν) ∧

    (∀ {D m γ Nmax M L Q : ℕ} (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ)
      (A : Fin m → Operator D) (Cv ρ : Operator D) (α R κ ν ε : ℝ),
      step2NoOutput S b α R κ ν →
      step2SelectionIngredient S b α R κ ν A Cv ρ ε →
      ∀ z : Fin m → ℝ, (∀ i, 0 ≤ z i) →
        eq75Threshold Cv ρ α ε ≤ ∑ i, z i * (Matrix.trace (A i * ρ)).re →
        ¬ (∑ i, z i * b i < Qatlib.Concepts.SdpDuality.ConeSeparation.noCheapWidth α R ε)) ∧

    (¬ Qatlib.Concepts.SdpDuality.ConeSeparation.correctedNoCheapSeparator
        G8.A0 G8.Cv0 G8.b0 G8.ρ8 (3:ℝ) (1:ℝ) (1/6:ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m γ Nmax M L Q S b α R κ ν k N
    exact step2Decision_iff S b α R κ ν k N
  · intro m γ Nmax M L Q S
    exact step2Trajectory_length S
  · intro m γ Nmax M L Q S b α R κ ν
    exact step2NoOutput_iff S b α R κ ν
  · intro D m γ Nmax M L Q S b A Cv ρ α R κ ν ε hno hsel
    exact clause21_no_output_universal S b A Cv ρ α R κ ν ε hno hsel
  · exact clause21_universal_refuted

/-- The weighted cost of `y` is at most `α`. -/
def exactWidthBudget {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ) (α : ℝ) : Prop :=
  ∑ i, b i * y i ≤ α

/-- The weighted cost of `y` is at most the relaxed bound `α * (1 + 2 * R * ε)`. -/
def quantumWidthBudget {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ) (α R ε : ℝ) : Prop :=
  ∑ i, b i * y i ≤ α * (1 + 2 * R * ε)

/-- The relaxed width bound exceeds the exact bound by `2 * α * R * ε`. -/
theorem clause29_width_gap (α R ε : ℝ) :
    α * (1 + 2 * R * ε) - α = 2 * α * R * ε := by ring

/-- The sampled width budget equals the relaxed width formula with error `κ + ν`. -/
theorem clause29_sampled_budget_bridge (α R κ ν : ℝ) :
    sdpSampledWidthBudget α R κ ν = α * (1 + 2 * R * (κ + ν)) := rfl

/-- An exact width budget implies the relaxed width budget when `α`, `R`, and `ε` are
nonnegative. -/
theorem clause29_exact_implies_quantum {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ)
    (α R ε : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (h : exactWidthBudget b y α) : quantumWidthBudget b y α R ε := by
  have hfac : 1 ≤ 1 + 2 * R * ε := by nlinarith
  have hstep : α ≤ α * (1 + 2 * R * ε) := by
    simpa using! mul_le_mul_of_nonneg_left hfac hα
  exact le_trans h hstep

/-- A one-coordinate example satisfies the relaxed width budget but fails the exact width
budget. -/
theorem clause29_quantum_not_implies_exact :
    ¬ (quantumWidthBudget (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 3 / 2) 1 1 (1 / 4) →
        exactWidthBudget (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 3 / 2) 1) := by
  intro h
  have h1 := h
  norm_num [quantumWidthBudget, exactWidthBudget, Fin.sum_univ_one] at h1

/-- Under the stated normalization and error bounds, exact per-round budgets imply relaxed
budgets and a dual-certificate objective at most `(1 + δ) * α`. -/
theorem clause29_same_run_certificate {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D)
    (b : Fin m → ℝ) (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ)
    (hD : 0 < D) (hα : 0 < α) (hα2 : 2 ≤ α) (hR : 0 < R) (hδ : 0 < δ) (hε : 0 < ε)
    (hsmall : 2 * R * ε ≤ 1 / 2) (hbudget : 2 * R * ε ≤ δ / 2)
    (hA : ∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) (hCv : Cv.IsHermitian ∧ ‖Cv‖ ≤ 1)
    (hb : ∀ i, 1 ≤ b i) (hAj : A j₀ = 1) (hbj : b j₀ = R)
    (hy : ∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α)) :
    (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α * (1 + 2 * R * ε))) ∧
    (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ ε) i * b i
        ≤ (1 + δ) * α) := by
  have hR0 : 0 ≤ R := hR.le
  have hε0 : 0 ≤ ε := hε.le
  have hα0 : 0 ≤ α := hα.le
  refine ⟨?_, ?_⟩
  · intro t
    exact ⟨(hy t).1,
      clause29_exact_implies_quantum b (y t) α R ε hα0 hR0 hε0 (hy t).2⟩
  · have hwidth : ∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α * (1 + 2 * R * ε)) := by
      intro t
      exact ⟨(hy t).1,
        clause29_exact_implies_quantum b (y t) α R ε hα0 hR0 hε0 (hy t).2⟩
    have hcontract := sdpWidthSlackPayoffRange D m A Cv b y j₀ α R δ ε
      hD hα hα2 hR hδ hε hsmall hbudget hA hCv hb hAj hbj hwidth
    exact hcontract.2

/-- Collects the width-gap identity, sampled-budget identity, one-way budget implication,
counterexample to its converse, and conditional certificate bound. See [BrandaoSvore2017]
for the mathematical setting. -/
theorem clause29_complete :
    (∀ (α R ε : ℝ), α * (1 + 2 * R * ε) - α = 2 * α * R * ε) ∧
    (∀ (α R κ ν : ℝ), sdpSampledWidthBudget α R κ ν = α * (1 + 2 * R * (κ + ν))) ∧
    (∀ {m : ℕ} (b : Fin m → ℝ) (y : Fin m → ℝ) (α R ε : ℝ),
      0 ≤ α → 0 ≤ R → 0 ≤ ε → exactWidthBudget b y α → quantumWidthBudget b y α R ε) ∧
    (¬ (quantumWidthBudget (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 3 / 2) 1 1 (1 / 4) →
          exactWidthBudget (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => 3 / 2) 1)) ∧
    (∀ {D m : ℕ} (A : Fin m → Operator D) (Cv : Operator D) (b : Fin m → ℝ)
      (y : ℕ → Fin m → ℝ) (j₀ : Fin m) (α R δ ε : ℝ),
      0 < D → 0 < α → 2 ≤ α → 0 < R → 0 < δ → 0 < ε →
      2 * R * ε ≤ 1 / 2 → 2 * R * ε ≤ δ / 2 →
      (∀ i, (A i).IsHermitian ∧ ‖A i‖ ≤ 1) →
      Cv.IsHermitian ∧ ‖Cv‖ ≤ 1 →
      (∀ i, 1 ≤ b i) → A j₀ = 1 → b j₀ = R →
      (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α)) →
        (∀ t, (∀ i, 0 ≤ y t i) ∧ (∑ i, b i * y t i ≤ α * (1 + 2 * R * ε))) ∧
        (∑ i, sdpDualCertificate m δ α R j₀ y (sdpDualCertRounds D R δ ε) i * b i
          ≤ (1 + δ) * α)) := by
  refine ⟨clause29_width_gap, clause29_sampled_budget_bridge, clause29_exact_implies_quantum,
    clause29_quantum_not_implies_exact, clause29_same_run_certificate⟩

/-- Records sparsification, Gibbs, expectation, and cost errors together with a failure mass for
one round. -/
structure roundErrorLedger where

  sparsifyError : ℝ

  gibbsError : ℝ

  expectError : ℝ

  costError : ℝ

  failMass : ℝ

/-- Computes the four observed errors for a search cell and assigns zero to its failure-mass
entry. -/
noncomputable def step2RoundLedger {m γ Nmax M L Q D : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (A : Fin m → Operator D)
    (Cv ρ : Operator D) (α κ R ν : ℝ) (k : Fin γ) (N : Fin Nmax) : roundErrorLedger where
  sparsifyError :=
    ‖sdpScaledSparsifiedPayoff D m Q A Cv α (Step2Search.gridMass κ N) (S.idx k N) -
      sourceScaledPayoff A Cv α (S.roundVector κ k N)‖
  gibbsError := |S.estC k N - (Matrix.trace (Cv * ρ)).re|
  expectError := ∑ i : Fin m,
    |(∑ l : Fin L, S.measA k N i l) / L - (Matrix.trace (A i * ρ)).re|
  costError := |(∑ i : Fin m, S.law k i * b i) - (∑ j : Fin M, b (S.draws k N j)) / M|
  failMass := 0

/-- On the search good event, the round ledger bounds sparsification by `ν`, Gibbs error by `κ +
ν`, summed expectation error by `m * (κ + ν)`, and cost error by `R * (κ + ν)`. -/
theorem clause30_error_bounds {m γ Nmax M L Q D : ℕ}
    (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (A : Fin m → Operator D)
    (Cv ρ : Operator D) (α κ R ν : ℝ) (k : Fin γ) (N : Fin Nmax)
    (hgood : S.goodEvent b A Cv ρ α κ R ν) :
    (step2RoundLedger S b A Cv ρ α κ R ν k N).sparsifyError ≤ ν ∧
    (step2RoundLedger S b A Cv ρ α κ R ν k N).gibbsError ≤ κ + ν ∧
    (step2RoundLedger S b A Cv ρ α κ R ν k N).expectError ≤ (m : ℝ) * (κ + ν) ∧
    (step2RoundLedger S b A Cv ρ α κ R ν k N).costError ≤ R * (κ + ν) := by
  obtain ⟨hcost, hexp, hobs, hgibbs, hsp⟩ := hgood k N
  refine ⟨hsp, hgibbs, ?_, hcost⟩
  calc (∑ i : Fin m,
        |(∑ l : Fin L, S.measA k N i l) / L - (Matrix.trace (A i * ρ)).re|)
      ≤ ∑ _i : Fin m, (κ + ν) := Finset.sum_le_sum fun i _ => hobs i
    _ = (m : ℝ) * (κ + ν) := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

/-- Counts occurrences of an element in a list as a real number. -/
def countEq {α : Type} [DecidableEq α] (a : α) : List α → ℝ
  | [] => 0
  | b :: l => (if a = b then 1 else 0) + countEq a l

/-- The occurrence count in a concatenation is the sum of the two occurrence counts. -/
theorem countEq_append {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α) :
    countEq a (l₁ ++ l₂) = countEq a l₁ + countEq a l₂ := by
  induction l₁ with
  | nil => simp only [List.nil_append, countEq, zero_add]
  | cons b l ih =>
    simp only [countEq, List.cons_append]
    rw [ih]
    ring

/-- Real-valued occurrence counts are nonnegative. -/
theorem countEq_nonneg {α : Type} [DecidableEq α] (a : α) (l : List α) :
    0 ≤ countEq a l := by
  induction l with
  | nil => simp only [countEq]; norm_num
  | cons b l ih =>
    simp only [countEq]
    split_ifs <;> linarith

/-- Recursively splits a list into a binary sampler tree, emitting at singleton leaves and
failing at other depth-zero leaves. -/
def listTree {α : Type} : (k : ℕ) → List α → SamplerTree α
  | 0, l => match l with
    | [a] => .emit a
    | _ => .fail
  | (k + 1), l => .bit (listTree k (l.take (2 ^ k))) (listTree k (l.drop (2 ^ k)))

/-- A list of length `2 ^ k` yields a sampler tree of maximum depth `k`. -/
theorem listTree_maxDepth {α : Type} (k : ℕ) (l : List α) (h : l.length = 2 ^ k) :
    (listTree k l).maxDepth = k := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons a l =>
      cases l with
      | nil => rfl
      | cons b l => simp at h
  | succ k ih =>
    have htake : (l.take (2 ^ k)).length = 2 ^ k := by
      rw [List.length_take, min_eq_left (by omega)]
    have hdrop : (l.drop (2 ^ k)).length = 2 ^ k := by
      rw [List.length_drop, h]
      omega
    simp only [listTree, SamplerTree.maxDepth]
    rw [ih _ htake, ih _ hdrop]
    omega

/-- For a list of length `2 ^ k`, the sampler law is the occurrence count divided by `2 ^ k`. -/
theorem listTree_law {α : Type} [DecidableEq α] (k : ℕ) (l : List α)
    (h : l.length = 2 ^ k) (a : α) :
    (listTree k l).law a = countEq a l / (2 ^ k : ℝ) := by
  induction k generalizing l with
  | zero =>
    cases l with
    | nil => simp at h
    | cons b l =>
      cases l with
      | nil =>
        show (if a = b then (1 : ℝ) else 0) = countEq a [b] / 1
        by_cases hb : a = b <;> simp [hb, countEq]
      | cons c l => simp at h
  | succ k ih =>
    have htake : (l.take (2 ^ k)).length = 2 ^ k := by
      rw [List.length_take, min_eq_left (by omega)]
    have hdrop : (l.drop (2 ^ k)).length = 2 ^ k := by
      rw [List.length_drop, h]
      omega
    have hsplit : l.take (2 ^ k) ++ l.drop (2 ^ k) = l := by
      rw [List.take_append_drop]
    simp only [listTree, SamplerTree.law]
    rw [ih _ htake, ih _ hdrop]
    have hcount : countEq a (l.take (2 ^ k)) + countEq a (l.drop (2 ^ k)) = countEq a l := by
      calc countEq a (l.take (2 ^ k)) + countEq a (l.drop (2 ^ k))
          = countEq a (l.take (2 ^ k) ++ l.drop (2 ^ k)) := (countEq_append a _ _).symm
        _ = countEq a l := by rw [hsplit]
    have htwo : (2 : ℝ) ^ k ≠ 0 := by positivity
    have h3 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [h3]
    field_simp [htwo]
    rw [hcount]

/-- The law of a bound sampler tree is the finite sum of the outer law times each conditional
law. -/
theorem bind_law {O P : Type} [Fintype O] [DecidableEq O] [DecidableEq P]
    (c : SamplerTree O) (k : O → SamplerTree P) :
    ∀ p : P, (c.bind k).law p = ∑ o, c.law o * (k o).law p := by
  induction c with
  | emit o =>
    intro p
    have hz : ∀ b : O, b ≠ o → (if b = o then (1 : ℝ) else 0) * (k b).law p = 0 := by
      intro b hb; simp [hb]
    simp only [SamplerTree.bind, SamplerTree.law]
    rw [Finset.sum_eq_single o (fun b _ hb => hz b hb)
      (fun h => absurd h (by simp))]
    simp
  | fail =>
    intro p
    simp [SamplerTree.bind, SamplerTree.law]
  | bit l r ihl ihr =>
    intro p
    simp only [SamplerTree.bind, SamplerTree.law]
    rw [ihl, ihr]
    have hsplit : ∀ x, ((l.law x + r.law x) / 2) * (k x).law p
        = (l.law x * (k x).law p + r.law x * (k x).law p) / 2 := by
      intro x; ring
    rw [Finset.sum_congr rfl (fun x _ => hsplit x)]
    rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- Binding trees of depth at most `M` increases maximum depth by at most `M`. -/
theorem bind_maxDepth_le {O P : Type} (c : SamplerTree O) (k : O → SamplerTree P)
    (M : ℕ) (h : ∀ o, (k o).maxDepth ≤ M) :
    (c.bind k).maxDepth ≤ c.maxDepth + M := by
  induction c generalizing M with
  | emit o =>
    simp only [SamplerTree.bind, SamplerTree.maxDepth]
    have h1 := h o
    omega
  | fail =>
    simp only [SamplerTree.bind, SamplerTree.maxDepth]
    omega
  | bit l r ihl ihr =>
    simp only [SamplerTree.bind, SamplerTree.maxDepth]
    have h1 := ihl M h
    have h2 := ihr M h
    omega

/-- Selecting from a list of length `2 ^ k` and then running the selected tree realizes the
mixture weighted by normalized list counts. -/
theorem clause30_mixture_sampler {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
    (trees : Fin n → SamplerTree (Fin m)) (hL : Lst.length = 2 ^ k) :
    treeRealizes (fun i => ∑ t, (countEq t Lst / (2 ^ k : ℝ)) * (trees t).law i)
      (SamplerTree.bind (listTree k Lst) trees) := by
  intro i
  rw [bind_law]
  show (∑ o, (listTree k Lst).law o * (trees o).law i)
      = ∑ t, (countEq t Lst / (2 ^ k : ℝ)) * (trees t).law i
  apply Finset.sum_congr rfl
  intro t _
  rw [listTree_law k Lst hL t]

/-- The depth of the composed mixture sampler is bounded by the selector depth plus the uniform
component-depth bound. -/
theorem clause30_mixture_cost {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
    (trees : Fin n → SamplerTree (Fin m)) (M : ℕ)
    (h : ∀ t, (trees t).maxDepth ≤ M) :
    (SamplerTree.bind (listTree k Lst) trees).maxDepth
      ≤ (listTree k Lst).maxDepth + M := by
  exact bind_maxDepth_le (listTree k Lst) trees M h

/-- Prepends the point mass at `j₀` to a finite family of component laws. -/
def mixtureComponentLaw {m T : ℕ} (j₀ : Fin m) (q : Fin T → Fin m → ℝ) :
    Fin (T + 1) → Fin m → ℝ :=
  Fin.cases (fun i => if i = j₀ then 1 else 0) (fun t i => q t i)

/-- Prepends the deterministic sampler emitting `j₀` to a finite family of sampler trees. -/
def mixtureComponents {m T : ℕ} (j₀ : Fin m) (qt : Fin T → SamplerTree (Fin m)) :
    Fin (T + 1) → SamplerTree (Fin m) :=
  Fin.cases (SamplerTree.emit j₀) (fun t => qt t)

/-- The prepended sampler family has the prepended component laws when each original tree has
its specified law. -/
theorem clause30_component_tree_laws {m T : ℕ} (j₀ : Fin m) (qt : Fin T → SamplerTree (Fin m))
    (q : Fin T → Fin m → ℝ) (hq : ∀ t, (qt t).law = q t) (i : Fin m) :
    (∀ t : Fin (T + 1), (mixtureComponents j₀ qt t).law i
        = mixtureComponentLaw j₀ q t i) := by
  intro t
  cases t using Fin.cases with
  | zero => rfl
  | succ t =>
      rw [show mixtureComponents j₀ qt t.succ = qt t from rfl]
      rw [show mixtureComponentLaw j₀ q t.succ = (fun i => q t i) from rfl]
      rw [hq t]

/-- For nonnegative component masses, positive `a`, and positive `T`, the weighted component sum
equals `dualMixtureLaw`. -/
theorem clause30_dual_mixture_identity {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ)
    (q : Fin T → Fin m → ℝ) (hμ : ∀ t, 0 ≤ μ t) (ha : 0 < a) (hT : 0 < T)
    (i : Fin m) :
    (∑ t : Fin (T + 1), dualMixtureWeights a μ t * mixtureComponentLaw j₀ q t i)
      = dualMixtureLaw j₀ a μ q i := by
  have hsc : 0 < dualMixtureScale a μ := by
    unfold dualMixtureScale
    have h1 : (0:ℝ) < a := ha
    have hsumμ : 0 ≤ ∑ t : Fin T, μ t := Finset.sum_nonneg fun t _ => hμ t
    have h2 : 0 ≤ (∑ t : Fin T, μ t) / T := by positivity
    linarith
  have hscne : dualMixtureScale a μ ≠ 0 := ne_of_gt hsc
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
  have hw0 : dualMixtureWeights a μ 0 = a / dualMixtureScale a μ := rfl
  have hwS : ∀ t : Fin T,
      dualMixtureWeights a μ t.succ = μ t / (T * dualMixtureScale a μ) := fun _ => rfl
  have hcomp0 : mixtureComponentLaw j₀ q 0 i = (if i = j₀ then 1 else 0) := rfl
  have hcompS : ∀ t : Fin T, mixtureComponentLaw j₀ q t.succ i = q t i := fun _ => rfl
  have hsum1 : (∑ t : Fin T, (μ t / (T * dualMixtureScale a μ)) * q t i)
      = (∑ t : Fin T, μ t * q t i) / (T * dualMixtureScale a μ) := by
    calc (∑ t : Fin T, (μ t / (T * dualMixtureScale a μ)) * q t i)
        = ∑ t : Fin T, (μ t * q t i) / (T * dualMixtureScale a μ) := by
          apply Finset.sum_congr rfl
          intro t _
          ring
      _ = (∑ t : Fin T, μ t * q t i) / (T * dualMixtureScale a μ) := by
          rw [Finset.sum_div]
  have hsum2 : (∑ x : Fin T,
        (μ x / (T * dualMixtureScale a μ)) * mixtureComponentLaw j₀ q x.succ i)
      = ∑ x : Fin T, (μ x / (T * dualMixtureScale a μ)) * q x i := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hcompS x]
  unfold dualMixtureLaw
  rw [Fin.sum_univ_succ]
  simp only [hw0, hwS, hcomp0]
  rw [hsum2]
  rw [hsum1]
  by_cases hi : i = j₀
  · simp only [hi, if_true]
    field_simp [hscne, hTne] <;> ring
  · simp only [hi, if_false]
    field_simp [hscne, hTne] <;> ring

/-- A dyadic list representation of the dual mixture weights and exact component trees yield an
exact sampler for the dual mixture law. -/
theorem clause30_dual_mixture_sampler {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ)
    (q : Fin T → Fin m → ℝ) (hμ : ∀ t, 0 ≤ μ t) (ha : 0 < a) (hT : 0 < T)
    (k : ℕ) (Lst : List (Fin (T + 1))) (qt : Fin T → SamplerTree (Fin m))
    (hL : Lst.length = 2 ^ k)
    (hw : ∀ t, dualMixtureWeights a μ t = countEq t Lst / (2 ^ k : ℝ))
    (hq : ∀ t, (qt t).law = q t) :
    treeRealizes (dualMixtureLaw j₀ a μ q)
      (SamplerTree.bind (listTree k Lst) (mixtureComponents j₀ qt)) := by
  intro i
  rw [bind_law]
  have h1 : (∑ o, (listTree k Lst).law o * (mixtureComponents j₀ qt o).law i)
      = ∑ o, dualMixtureWeights a μ o * (mixtureComponents j₀ qt o).law i := by
    apply Finset.sum_congr rfl
    intro o _
    rw [listTree_law k Lst hL o, ← hw o]
  rw [h1]
  have h2 : (∑ o, dualMixtureWeights a μ o * (mixtureComponents j₀ qt o).law i)
      = ∑ o, dualMixtureWeights a μ o * mixtureComponentLaw j₀ q o i := by
    apply Finset.sum_congr rfl
    intro o _
    rw [clause30_component_tree_laws j₀ qt q hq i o]
  rw [h2]
  exact clause30_dual_mixture_identity j₀ a μ q hμ ha hT i

/-- The ℓ¹ difference between two mixtures with dyadic list weights is bounded by the weighted
sum of their componentwise ℓ¹ error bounds. -/
theorem clause30_mixture_error_transfer {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
    (trees : Fin n → SamplerTree (Fin m)) (hL : Lst.length = 2 ^ k)
    (w : Fin n → ℝ) (hw : ∀ t, w t = countEq t Lst / (2 ^ k : ℝ))
    (q q' : Fin n → Fin m → ℝ) (hq : ∀ t, (trees t).law = q t)
    (νs : Fin n → ℝ) (hν : ∀ t, 0 ≤ νs t)
    (hpert : ∀ t, ∑ i, |q' t i - q t i| ≤ νs t) :
    ∑ i, |(∑ t, w t * q' t i) - (∑ t, w t * q t i)| ≤ ∑ t, w t * νs t := by
  have hw0 : ∀ t, 0 ≤ w t := by
    intro t
    rw [hw t]
    have h1 : 0 ≤ countEq t Lst := countEq_nonneg t Lst
    have h2 : (0:ℝ) < 2 ^ k := by positivity
    exact div_nonneg h1 h2.le
  have hcoord : ∀ i, |(∑ t, w t * q' t i) - (∑ t, w t * q t i)|
      ≤ ∑ t, w t * |q' t i - q t i| := by
    intro i
    have h1 : (∑ t, w t * q' t i) - (∑ t, w t * q t i)
        = ∑ t, w t * (q' t i - q t i) := by
      rw [← Finset.sum_sub_distrib (fun t => w t * q' t i) (fun t => w t * q t i)]
      apply Finset.sum_congr rfl
      intro t _
      ring
    rw [h1]
    calc |∑ t, w t * (q' t i - q t i)| ≤ ∑ t, |w t * (q' t i - q t i)| :=
          Finset.abs_sum_le_sum_abs (fun t => w t * (q' t i - q t i))
            (Finset.univ : Finset (Fin n))
      _ = ∑ t, w t * |q' t i - q t i| := by
          apply Finset.sum_congr rfl
          intro t _
          rw [abs_mul, abs_of_nonneg (hw0 t)]
  calc (∑ i, |(∑ t, w t * q' t i) - (∑ t, w t * q t i)|)
      ≤ ∑ i, ∑ t, w t * |q' t i - q t i| := Finset.sum_le_sum fun i _ => hcoord i
    _ = ∑ t, w t * (∑ i, |q' t i - q t i|) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
    _ ≤ ∑ t, w t * νs t := Finset.sum_le_sum fun t _ =>
        mul_le_mul_of_nonneg_left (hpert t) (hw0 t)

/-- No finite sampler tree realizes the specified two-point dual mixture law from the `G9`
instance. -/
theorem clause30_exact_realization_boundary :
    ¬ ∃ (choose : SamplerTree (Fin 2)),
        treeRealizes (dualMixtureLaw (0 : Fin 2) (1:ℝ) G9.mu0 G9.q0) choose :=
  Qatlib.Concepts.SdpDuality.ConeSeparation.dual_mixture_finite_tree_obstruction

/-- Collects round-error bounds, mixture laws and depth bounds, dual-mixture realization,
perturbation transfer, and the finite-tree obstruction. See [BrandaoSvore2017] for the
mathematical setting. -/
theorem clause30_complete :
    (∀ {m γ Nmax M L Q D : ℕ}
      (S : Step2Search m γ Nmax M L Q) (b : Fin m → ℝ) (A : Fin m → Operator D)
      (Cv ρ : Operator D) (α κ R ν : ℝ) (k : Fin γ) (N : Fin Nmax),
      S.goodEvent b A Cv ρ α κ R ν →
        (step2RoundLedger S b A Cv ρ α κ R ν k N).sparsifyError ≤ ν ∧
        (step2RoundLedger S b A Cv ρ α κ R ν k N).gibbsError ≤ κ + ν ∧
        (step2RoundLedger S b A Cv ρ α κ R ν k N).expectError ≤ (m : ℝ) * (κ + ν) ∧
        (step2RoundLedger S b A Cv ρ α κ R ν k N).costError ≤ R * (κ + ν)) ∧
    (∀ {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
      (trees : Fin n → SamplerTree (Fin m)), Lst.length = 2 ^ k →
        treeRealizes (fun i => ∑ t, (countEq t Lst / (2 ^ k : ℝ)) * (trees t).law i)
          (SamplerTree.bind (listTree k Lst) trees)) ∧
    (∀ {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
      (trees : Fin n → SamplerTree (Fin m)) (M : ℕ),
      (∀ t, (trees t).maxDepth ≤ M) →
        (SamplerTree.bind (listTree k Lst) trees).maxDepth
          ≤ (listTree k Lst).maxDepth + M) ∧
    (∀ {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ)
      (hμ : ∀ t, 0 ≤ μ t) (ha : 0 < a) (hT : 0 < T)
      (k : ℕ) (Lst : List (Fin (T + 1))) (qt : Fin T → SamplerTree (Fin m)),
      Lst.length = 2 ^ k →
      (∀ t, dualMixtureWeights a μ t = countEq t Lst / (2 ^ k : ℝ)) →
      (∀ t, (qt t).law = q t) →
        treeRealizes (dualMixtureLaw j₀ a μ q)
          (SamplerTree.bind (listTree k Lst) (mixtureComponents j₀ qt))) ∧
    (∀ {m T : ℕ} (j₀ : Fin m) (a : ℝ) (μ : Fin T → ℝ) (q : Fin T → Fin m → ℝ)
      (hμ : ∀ t, 0 ≤ μ t) (ha : 0 < a) (hT : 0 < T) (i : Fin m),
      (∑ t : Fin (T + 1), dualMixtureWeights a μ t * mixtureComponentLaw j₀ q t i)
        = dualMixtureLaw j₀ a μ q i) ∧
    (∀ {m n : ℕ} (k : ℕ) (Lst : List (Fin n))
      (trees : Fin n → SamplerTree (Fin m)) (hL : Lst.length = 2 ^ k)
      (w : Fin n → ℝ) (hw : ∀ t, w t = countEq t Lst / (2 ^ k : ℝ))
      (q q' : Fin n → Fin m → ℝ) (hq : ∀ t, (trees t).law = q t)
      (νs : Fin n → ℝ) (hν : ∀ t, 0 ≤ νs t)
      (hpert : ∀ t, ∑ i, |q' t i - q t i| ≤ νs t),
      ∑ i, |(∑ t, w t * q' t i) - (∑ t, w t * q t i)| ≤ ∑ t, w t * νs t) ∧
    (¬ ∃ (choose : SamplerTree (Fin 2)),
        treeRealizes (dualMixtureLaw (0 : Fin 2) (1:ℝ) G9.mu0 G9.q0) choose) := by
  refine ⟨clause30_error_bounds, clause30_mixture_sampler, clause30_mixture_cost,
    clause30_dual_mixture_sampler, clause30_dual_mixture_identity, clause30_mixture_error_transfer,
    clause30_exact_realization_boundary⟩

/-- Records an objective parameter, round count, failure mass, and error mass for one call in a
bisection shell. -/
structure alphaBisectCall where

  α : ℝ

  rounds : ℕ

  failMass : ℝ

  errorMass : ℝ

/-- A list of bisection calls together with declared failure and error masses. -/
structure alphaBisectShell where

  calls : List alphaBisectCall

  failMass : ℝ

  errorMass : ℝ

namespace alphaBisectShell

/-- The sum of the round counts of all calls in a bisection shell. -/
def totalRounds (S : alphaBisectShell) : ℕ :=
  (S.calls.map (fun c => c.rounds)).sum

/-- The sum of the failure masses of all calls in a bisection shell. -/
def spentFail (S : alphaBisectShell) : ℝ :=
  (S.calls.map (fun c => c.failMass)).sum

/-- The sum of the error masses of all calls in a bisection shell. -/
def spentError (S : alphaBisectShell) : ℝ :=
  (S.calls.map (fun c => c.errorMass)).sum

end alphaBisectShell

/-- A list of nonnegative reals has a nonnegative sum that bounds every entry. -/
private theorem listSum_nonneg_le {l : List ℝ} (h : ∀ a ∈ l, 0 ≤ a) :
    0 ≤ l.sum ∧ ∀ a ∈ l, a ≤ l.sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : 0 ≤ b := h b (by simp)
    have hrest : 0 ≤ l.sum ∧ ∀ a ∈ l, a ≤ l.sum :=
      ih (fun a ha => h a (by simp [ha]))
    simp only [List.sum_cons]
    refine ⟨by linarith, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with hba | ha
    · subst hba
      linarith
    · have := hrest.2 a ha
      linarith

/-- Nonnegative call masses give nonnegative total failure and error masses, each bounding every
corresponding call mass. -/
theorem clause31_shell_budget (S : alphaBisectShell)
    (hfail : ∀ c ∈ S.calls, 0 ≤ c.failMass)
    (herr : ∀ c ∈ S.calls, 0 ≤ c.errorMass) :
    0 ≤ S.spentFail ∧ 0 ≤ S.spentError ∧
    (∀ c ∈ S.calls, c.failMass ≤ S.spentFail) ∧
    (∀ c ∈ S.calls, c.errorMass ≤ S.spentError) := by
  have hfail' : ∀ a ∈ S.calls.map (fun c => c.failMass), 0 ≤ a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact hfail c hc
  have herr' : ∀ a ∈ S.calls.map (fun c => c.errorMass), 0 ≤ a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    exact herr c hc
  have hf := listSum_nonneg_le hfail'
  have he := listSum_nonneg_le herr'
  refine ⟨hf.1, he.1, ?_, ?_⟩
  · intro c hc
    have hle := hf.2 c.failMass (by
      simp only [List.mem_map]
      exact ⟨c, hc, rfl⟩)
    exact hle
  · intro c hc
    have hle := he.2 c.errorMass (by
      simp only [List.mem_map]
      exact ⟨c, hc, rfl⟩)
    exact hle

/-- For positive `δ` and `η`, the certificate round count bounds `16 * R * log D / (δ * η)` from
below. -/
theorem clause31_cert_rounds_eq72 {D : ℕ} (R δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    16 * R * Real.log D / (δ * η) ≤ sdpDualCertRounds D R δ η := by
  have hpos : 0 < δ * η := mul_pos hδ hη
  have hne : δ * η ≠ 0 := ne_of_gt hpos
  have hceil : 16 * R * Real.log D / (δ * η)
      ≤ (Nat.ceil (16 * R * Real.log D / (δ * η)) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  rw [sdpDualCertRounds]
  push_cast
  linarith

/-- Scaling every objective coefficient by `1 / α` scales the total objective by `1 / α`. -/
theorem clause31_rescale_objective (m : ℕ) (b sol : Fin m → ℝ) (α : ℝ) :
    (∑ i, sol i * (b i / α)) = (∑ i, sol i * b i) / α :=
  sdpAlphaRescaleObjective m b sol α

/-- For positive `α`, an objective bound of `1 + δ / α` after rescaling yields the original
bound `α + δ`. -/
theorem clause31_rescale_additive (m : ℕ) (b : Fin m → ℝ) (α δ : ℝ) (hα : 0 < α)
    (sol : Fin m → ℝ) (hscaled : (∑ i, sol i * (b i / α)) ≤ 1 + δ / α) :
    (∑ i, sol i * b i) ≤ α + δ :=
  sdpAlphaRescaleAdditive m b sol α δ hα hscaled

/-- Under the stated positivity and budget conditions, extends `b` by one coordinate equal to `R
+ 1`, preserving all entries and the lower bound one. -/
theorem clause31_lemma2_lift {m : ℕ} (b : Fin m → ℝ) (R r α δ : ℝ)
    (hm : 0 < m) (hR : 0 < R) (hr : 0 < r) (hα : 0 < α) (hδ : 0 < δ)
    (hαR : α ≤ R) (hrαR : r * α ≤ R) (hb : ∀ i, 1 ≤ b i) :
    ∃ (liftedB : Fin (m + 1) → ℝ),
      (∀ i, 1 ≤ liftedB i) ∧
      liftedB (Fin.last m) = R + 1 ∧
      (∀ i : Fin m, liftedB i.castSucc = b i) := by
  obtain ⟨liftedB, h1, h2, h3⟩ :=
    (sdpAlphaRescaleLemma2 1 m b R r α δ (by norm_num) hm hR hr hα hδ hb hαR hrαR).1
  exact ⟨liftedB, h1, h2, h3⟩

/-- Records per-round input accesses, preparation, estimation and base gates, bit time, fair
bits, and peak space. -/
structure sdpRoundCost where

  inputAccesses : ℕ

  prepGates : ℕ

  estimateGates : ℕ

  baseGates : ℕ

  bitTime : ℕ

  fairBits : ℕ

  peakSpace : ℕ

/-- Records call and round counts together with total accesses, gates, bit time, fair bits, and
peak space. -/
structure sdpFullRunCost where

  calls : ℕ

  rounds : ℕ

  inputAccesses : ℕ

  prepGates : ℕ

  estimateGates : ℕ

  baseGates : ℕ

  bitTime : ℕ

  fairBits : ℕ

  peakSpace : ℕ

/-- Forms the full-run cost by multiplying per-round additive costs by the shell's total rounds
and retaining per-round peak space. -/
def sdpFullRunCost.ofShell (S : alphaBisectShell) (perRound : sdpRoundCost) :
    sdpFullRunCost where
  calls := S.calls.length
  rounds := S.totalRounds
  inputAccesses := perRound.inputAccesses * S.totalRounds
  prepGates := perRound.prepGates * S.totalRounds
  estimateGates := perRound.estimateGates * S.totalRounds
  baseGates := perRound.baseGates * S.totalRounds
  bitTime := perRound.bitTime * S.totalRounds
  fairBits := perRound.fairBits * S.totalRounds
  peakSpace := perRound.peakSpace

/-- Expands the call count, round count, additive resource totals, and peak space of the
full-run cost constructed from a shell. -/
theorem clause31_run_cost_account (S : alphaBisectShell) (perRound : sdpRoundCost) :
    (sdpFullRunCost.ofShell S perRound).rounds = S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).calls = S.calls.length ∧
    (sdpFullRunCost.ofShell S perRound).inputAccesses
      = perRound.inputAccesses * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).prepGates
      = perRound.prepGates * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).estimateGates
      = perRound.estimateGates * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).baseGates
      = perRound.baseGates * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).bitTime
      = perRound.bitTime * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).fairBits
      = perRound.fairBits * S.totalRounds ∧
    (sdpFullRunCost.ofShell S perRound).peakSpace = perRound.peakSpace := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Combines compiled-backend costs and fair bits with per-round SDP resources, a round count,
and sampler fair bits. -/
structure sdpRunLedger where

  backend : IntCost

  backendFairBits : ℕ

  inputAccesses : ℕ

  prepGates : ℕ

  estimateGates : ℕ

  sdpBitTime : ℕ

  sdpPeakSpace : ℕ

  rounds : ℕ

  samplerFairBits : ℕ

namespace sdpRunLedger

/-- Adds backend bit time to the per-round SDP bit time multiplied by the round count. -/
def totalBitTime (L : sdpRunLedger) : ℕ :=
  L.backend.bitTime + L.sdpBitTime * L.rounds

/-- Adds backend gates to the preparation and estimation gates accumulated over all rounds. -/
def totalGates (L : sdpRunLedger) : ℕ :=
  L.backend.gates + (L.prepGates + L.estimateGates) * L.rounds

/-- Adds backend queries to the input accesses accumulated over all rounds. -/
def totalQueries (L : sdpRunLedger) : ℕ :=
  L.backend.queries + L.inputAccesses * L.rounds

/-- The maximum of backend peak space and SDP peak space. -/
def peakSpace (L : sdpRunLedger) : ℕ :=
  max L.backend.peakSpace L.sdpPeakSpace

/-- The sum of backend fair bits and sampler fair bits. -/
def totalFairBits (L : sdpRunLedger) : ℕ :=
  L.backendFairBits + L.samplerFairBits

end sdpRunLedger

/-- Builds a run ledger from the cost of a compiled step list and the supplied SDP resource
entries. -/
def sdpRunLedger.ofCompiled (steps : List Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep)
    (fairBits : ℕ) (inputAccesses prepGates estimateGates sdpBitTime sdpPeakSpace
      rounds samplerFairBits : ℕ) : sdpRunLedger where
  backend := Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps
  backendFairBits := fairBits
  inputAccesses := inputAccesses
  prepGates := prepGates
  estimateGates := estimateGates
  sdpBitTime := sdpBitTime
  sdpPeakSpace := sdpPeakSpace
  rounds := rounds
  samplerFairBits := samplerFairBits

/-- Expands all five total-resource formulas for the ledger constructed from compiled steps. -/
theorem clause32_ledger_account (steps : List Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep)
    (fairBits : ℕ) (inputAccesses prepGates estimateGates sdpBitTime sdpPeakSpace
      rounds samplerFairBits : ℕ) :
    (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
        sdpBitTime sdpPeakSpace rounds samplerFairBits).totalBitTime
      = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).bitTime
        + sdpBitTime * rounds ∧
    (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
        sdpBitTime sdpPeakSpace rounds samplerFairBits).totalGates
      = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).gates
        + (prepGates + estimateGates) * rounds ∧
    (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
        sdpBitTime sdpPeakSpace rounds samplerFairBits).totalQueries
      = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).queries
        + inputAccesses * rounds ∧
    (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
        sdpBitTime sdpPeakSpace rounds samplerFairBits).peakSpace
      = max (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).peakSpace sdpPeakSpace ∧
    (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
        sdpBitTime sdpPeakSpace rounds samplerFairBits).totalFairBits
      = fairBits + samplerFairBits := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An access count bounded by the sparse input length is also bounded by the total input length
including rational weights and parameter data. -/
theorem clause32_input_access_bound (D m : ℕ) (s bits : ℕ) (wt : Fin m → ℚ) (β : ℚ)
    (roundAccesses : ℕ) (h : roundAccesses ≤ sparseInputLength D m s bits) :
    roundAccesses ≤ totalInputLength D m s bits wt β := by
  have hsum : 0 ≤ Finset.univ.sum fun i : Fin m =>
        (wt i).num.natAbs.size + (wt i).den.size := by
    exact Finset.sum_nonneg fun i _ => by positivity
  have hrest : 0 ≤ (Finset.univ.sum fun i : Fin m =>
        (wt i).num.natAbs.size + (wt i).den.size) + β.num.natAbs.size + β.den.size := by
    omega
  unfold totalInputLength
  omega

/-- Every step in a compiled run satisfying `usesFixedGates` uses a gate kind from
`MmwGateSet.all`. -/
theorem clause32_fixed_gates (steps : List Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep)
    (h : Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.usesFixedGates steps)
    (s : Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep)
    (hs : s ∈ steps) :
    s.gateKind ∈ Qatlib.Concepts.SdpDuality.ConeSeparation.MmwGateSet.all := h s hs

/-- Collects bisection-shell mass bounds, the certificate round lower bound, objective
rescaling, coefficient lifting, and full-run cost identities. See [BrandaoSvore2017] for the
mathematical setting. -/
theorem clause31_complete :
    (∀ (S : alphaBisectShell) (hfail : ∀ c ∈ S.calls, 0 ≤ c.failMass)
      (herr : ∀ c ∈ S.calls, 0 ≤ c.errorMass),
      0 ≤ S.spentFail ∧ 0 ≤ S.spentError ∧
      (∀ c ∈ S.calls, c.failMass ≤ S.spentFail) ∧
      (∀ c ∈ S.calls, c.errorMass ≤ S.spentError)) ∧
    (∀ {D : ℕ} (R δ η : ℝ), 0 < δ → 0 < η →
      16 * R * Real.log D / (δ * η) ≤ sdpDualCertRounds D R δ η) ∧
    (∀ (m : ℕ) (b sol : Fin m → ℝ) (α : ℝ),
      (∑ i, sol i * (b i / α)) = (∑ i, sol i * b i) / α) ∧
    (∀ (m : ℕ) (b : Fin m → ℝ) (α δ : ℝ), 0 < α →
      ∀ (sol : Fin m → ℝ), (∑ i, sol i * (b i / α)) ≤ 1 + δ / α →
        (∑ i, sol i * b i) ≤ α + δ) ∧
    (∀ {m : ℕ} (b : Fin m → ℝ) (R r α δ : ℝ),
      0 < m → 0 < R → 0 < r → 0 < α → 0 < δ → α ≤ R → r * α ≤ R →
      (∀ i, 1 ≤ b i) →
        ∃ (liftedB : Fin (m + 1) → ℝ),
          (∀ i, 1 ≤ liftedB i) ∧
          liftedB (Fin.last m) = R + 1 ∧
          (∀ i : Fin m, liftedB i.castSucc = b i)) ∧
    (∀ (S : alphaBisectShell) (perRound : sdpRoundCost),
      (sdpFullRunCost.ofShell S perRound).rounds = S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).calls = S.calls.length ∧
      (sdpFullRunCost.ofShell S perRound).inputAccesses
        = perRound.inputAccesses * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).prepGates
        = perRound.prepGates * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).estimateGates
        = perRound.estimateGates * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).baseGates
        = perRound.baseGates * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).bitTime
        = perRound.bitTime * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).fairBits
        = perRound.fairBits * S.totalRounds ∧
      (sdpFullRunCost.ofShell S perRound).peakSpace = perRound.peakSpace) := by
  refine ⟨clause31_shell_budget, clause31_cert_rounds_eq72, clause31_rescale_objective,
    clause31_rescale_additive, clause31_lemma2_lift, clause31_run_cost_account⟩

/-- Collects compiled-run ledger identities, the total-input access bound, and membership in the
fixed gate set. See [BrandaoSvore2017] for the mathematical setting. -/
theorem clause32_complete :
    (∀ (steps : List Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep) (fairBits : ℕ)
      (inputAccesses prepGates estimateGates sdpBitTime sdpPeakSpace rounds
        samplerFairBits : ℕ),
      (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
          sdpBitTime sdpPeakSpace rounds samplerFairBits).totalBitTime
        = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).bitTime
          + sdpBitTime * rounds ∧
      (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
          sdpBitTime sdpPeakSpace rounds samplerFairBits).totalGates
        = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).gates
          + (prepGates + estimateGates) * rounds ∧
      (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
          sdpBitTime sdpPeakSpace rounds samplerFairBits).totalQueries
        = (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).queries
          + inputAccesses * rounds ∧
      (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
          sdpBitTime sdpPeakSpace rounds samplerFairBits).peakSpace
        = max (Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.cost steps).peakSpace
          sdpPeakSpace ∧
      (sdpRunLedger.ofCompiled steps fairBits inputAccesses prepGates estimateGates
          sdpBitTime sdpPeakSpace rounds samplerFairBits).totalFairBits
        = fairBits + samplerFairBits) ∧
    (∀ (D m : ℕ) (s bits : ℕ) (wt : Fin m → ℚ) (β : ℚ) (roundAccesses : ℕ),
      roundAccesses ≤ sparseInputLength D m s bits →
        roundAccesses ≤ totalInputLength D m s bits wt β) ∧
    (∀ (steps : List Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep)
      (h : Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledRun.usesFixedGates steps)
      (s : Qatlib.Concepts.SdpDuality.ConeSeparation.MmwCompiledStep) (hs : s ∈ steps),
      s.gateKind ∈ Qatlib.Concepts.SdpDuality.ConeSeparation.MmwGateSet.all) := by
  refine ⟨clause32_ledger_account, clause32_input_access_bound, clause32_fixed_gates⟩

end Qatlib.Papers.SDPBrandao16.MainResults
