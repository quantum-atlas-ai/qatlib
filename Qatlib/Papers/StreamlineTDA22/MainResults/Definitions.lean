/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

set_option backward.isDefEq.respectTransparency false

/-!
# StreamlineTDA22 — shared paper-level vocabulary

Paper under formalisation: *A streamlined quantum algorithm for topological data
analysis with exponentially fewer qubits* (arXiv:2209.12887).

This file fixes the vocabulary every claim in `MainResults` shares:

* the **normalised rank ratio** `sqrt (rank P / rank Pt)` of Theorem 2/3 and
  Corollary 3.1;
* the **persistent Betti number** in the rank form of Eq. (5)/(24):
  `dim Ker ∂^i_k − dim (Ker ∂^i_k ∩ Im ∂^j_{k+1})`, encoded by the ranks of the
  kernel and image projectors;
* the **gap parameters** `Λ_∂` (smallest nonzero singular value, Sec. 5.3/5.4)
  and `Λ_{ΠΠ}` (deviation of the largest non-unit singular value of
  `PKer · PIm` from one, Sec. 5.4);
* an **incoherent-repetition estimator** together with its success probability
  and independent resource labels (`reps`, `calls`, `gates`, `qubits`, `depth`);
* the explicit depth budget of Theorem 1, Eq. (1).

The main Theorem 1 estimator construction is absent. `EstimatorExecution` supplies
a conditional interface to an explicit word in a caller-supplied circuit model;
the word determines its output law and resource counts. The estimator contract is
a statement only. The separate QSVT module proves matrix-word identities and
query counts, without constructing this estimator or proving its depth budget.
-/

set_option autoImplicit false

namespace Qatlib.Papers.StreamlineTDA22.MainResults

open Matrix
open scoped BigOperators

noncomputable section

/-! ## Normalised projector rank (Theorem 2/3, Corollary 3.1) -/

/-- The quantity estimated by the paper's rank subroutine: the square root of
`rank P / rank Pt` (Theorem 2, Theorem 3, Corollary 3.1). -/
noncomputable def normalizedRankRatio {I : Type*} [Fintype I]
    (P Pt : Matrix I I ℂ) : ℝ :=
  Real.sqrt ((P.rank : ℝ) / (Pt.rank : ℝ))

/-- The normalised rank ratio is nonnegative. -/
theorem normalizedRankRatio_nonneg {I : Type*} [Fintype I]
    (P Pt : Matrix I I ℂ) : 0 ≤ normalizedRankRatio P Pt :=
  Real.sqrt_nonneg _

/-- The normalised rank ratio is at most one as soon as `rank P ≤ rank Pt`. -/
theorem normalizedRankRatio_le_one {I : Type*} [Fintype I]
    (P Pt : Matrix I I ℂ) (h : P.rank ≤ Pt.rank) :
    normalizedRankRatio P Pt ≤ 1 := by
  unfold normalizedRankRatio
  rw [Real.sqrt_le_one]
  exact div_le_one_of_le₀ (by exact_mod_cast h) (by positivity)

/-! ## Persistent Betti numbers, Eq. (5)/(24) -/

/-- The persistent Betti number in the rank form of Eq. (5)/(24):
`dim Ker ∂^i_k − dim (Ker ∂^i_k ∩ Im ∂^j_{k+1})`.  For orthogonal projectors
`PKer` and `PIm` the intersection projector has rank `rank (PKer * PIm)`
(the paper's Sec. 5.4 discussion), so the rank form below is exactly (24). -/
noncomputable def bettiRank {I : Type*} [Fintype I]
    (PKer PIm : Matrix I I ℂ) : ℕ :=
  PKer.rank - (PKer * PIm).rank

/-- The Betti number normalised by the number of `k`-simplices,
`β^{i,j}_k / C(N, k+1)`; this is the quantity whose two factors are estimated
in Corollary 3.1. -/
noncomputable def normalizedBetti (β : ℝ) (N k : ℕ) : ℝ :=
  β / (Nat.choose N (k + 1) : ℝ)

/-! ## Gap parameters (Sec. 5.3 / Sec. 5.4) -/

/-- `Λ` is the smallest nonzero singular value of `A`: every `v` with `A v ≠ 0`
has `Λ ‖v‖ ≤ ‖A v‖`, and `Λ` is attained.  This is the meaning of `Λ_∂^i_k`
and `Λ_∂^j_{k+1}` in Theorem 1. -/
def IsSmallestNonzeroSingularValue {O I : Type*} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) (Λ : ℝ) : Prop :=
  0 < Λ ∧
    (∃ v : I → ℂ, v ≠ 0 ∧ A.mulVec v ≠ 0 ∧ ‖A.mulVec v‖ = Λ * ‖v‖) ∧
    (∀ v : I → ℂ, v ≠ 0 → A.mulVec v ≠ 0 → Λ * ‖v‖ ≤ ‖A.mulVec v‖)

/-- `Λ` is the projector-overlap gap of Sec. 5.4: every nonzero singular value
of `M = PKer · PIm` is either `1` or at most `1 − Λ`.  The paper defines
`Λ_{ΠΠ}` as the deviation from one of the largest non-unit singular value, and
notes that it equals `1` for ordinary (non-persistent) Betti numbers. -/
def IsProjectorOverlapGap {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (Λ : ℝ) : Prop :=
  0 < Λ ∧ Λ ≤ 1 ∧
    (∀ v : I → ℂ, M.mulVec v ≠ 0 →
      ‖M.mulVec v‖ = ‖v‖ ∨ ‖M.mulVec v‖ ≤ (1 - Λ) * ‖v‖)

/-! ## Incoherent-repetition estimators and their cost ledger -/

/-- An output-law specification with independent resource labels.
The probability and value fields impose no execution requirement on `reps`,
`calls`, `gates`, `qubits` or `depth`. `EstimatesWithin` only checks probability.
Use `EstimatorExecution` for an additional circuit implementation obligation. -/
structure IncoherentEstimator (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : (∑ ω, prob ω) = 1
  value : Ω → ℝ
  reps : ℕ
  calls : ℕ
  gates : ℕ
  qubits : ℕ
  depth : ℕ

/-- Probability that the estimator is within additive `δ` of `target`. -/
noncomputable def successProb {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => |E.value ω - target| ≤ δ), E.prob ω

/-- An output-law success condition, with no resource or implementation claim:
the estimate is within additive `δ` with probability at least `1 − η`. -/
def EstimatesWithin {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ η : ℝ) : Prop :=
  1 - η ≤ successProb E target δ

/-- Every success probability is nonnegative. -/
theorem successProb_nonneg {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ : ℝ) : 0 ≤ successProb E target δ := by
  unfold successProb
  exact Finset.sum_nonneg (fun ω _ => E.prob_nonneg ω)

/-- Every success probability is at most one. -/
theorem successProb_le_one {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ : ℝ) : successProb E target δ ≤ 1 := by
  unfold successProb
  calc
    (∑ ω ∈ Finset.univ.filter (fun ω => |E.value ω - target| ≤ δ), E.prob ω)
        ≤ ∑ ω : Ω, E.prob ω := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ω _ _ => E.prob_nonneg ω)
    _ = 1 := E.prob_sum

/-- Relaxing the failure budget preserves success: if an estimator succeeds with
probability at least `1 - η` and `η ≤ η'`, it also succeeds with probability at
least `1 - η'`.  Used to weaken the per-instance error budgets in Corollary 3.1. -/
theorem estimatesWithin_mono_eta {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ η η' : ℝ)
    (h : EstimatesWithin E target δ η) (hη : η ≤ η') :
    EstimatesWithin E target δ η' := by
  unfold EstimatesWithin at *
  linarith

/-- The probability of the complementary (failure) event. -/
noncomputable def failureProb {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ : ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => ¬ |E.value ω - target| ≤ δ), E.prob ω

/-- Success and failure probabilities sum to one.  This is the union-bound
input used when Corollary 3.1 composes two rank estimations. -/
theorem successProb_add_failureProb {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (target δ : ℝ) :
    successProb E target δ + failureProb E target δ = 1 := by
  have hsplit : ∀ ω : Ω,
      (if |E.value ω - target| ≤ δ then E.prob ω else 0) +
        (if ¬ |E.value ω - target| ≤ δ then E.prob ω else 0) = E.prob ω := by
    intro ω
    by_cases h : |E.value ω - target| ≤ δ <;> simp [h]
  unfold successProb failureProb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  calc (∑ ω : Ω,
        ((if |E.value ω - target| ≤ δ then E.prob ω else 0) +
          (if ¬ |E.value ω - target| ≤ δ then E.prob ω else 0)))
      = ∑ ω : Ω, E.prob ω := Finset.sum_congr rfl (fun ω _ => hsplit ω)
    _ = 1 := E.prob_sum

/-! ## Theorem 1's explicit budget, Eq. (1) -/

/-- A standalone scale inspired by Theorem 1's depth, Eq. (1):
`Õ( N^{3/2} sqrt(k β^{i,j}_k) / (Δ Λ_{ΠΠ}^{1/2} min(Λ_∂i, Λ_∂j)) )`.
The `Õ` suppresses polylogarithmic factors; the explicit representative used
here carries the factor `(1 + log N)^2` and the constant `2`. Neither this choice
of factors nor a depth bound for an implemented estimator is proved here. -/
noncomputable def theorem1DepthBudget (N k : ℕ) (β Δ Λdi Λdj Λpipi : ℝ) : ℝ :=
  2 * (1 + Real.log (N : ℝ)) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) *
    Real.sqrt ((k : ℝ) * β) /
      (Δ * Real.sqrt Λpipi * min Λdi Λdj)

/-- The bare qubit scale `min{k log N, N}` from Theorem 1.
No implemented estimator's qubit bound is proved here. -/
noncomputable def theorem1QubitScale (N k : ℕ) : ℝ :=
  min ((k : ℝ) * Real.log (N : ℝ)) (N : ℝ)

/-- Conditional circuit model: each instruction is one serial primitive layer.
Initialization, primitive action, the repeated-measurement law, and decoding are
supplied by the caller. Native gate synthesis and the measurement law's physical
realizability must be justified by that caller; this record proves neither. -/
structure EstimatorCircuitModel (Ω : Type*) where
  State : Type
  Instruction : Type
  initial : State
  step : State → Instruction → State
  law : ℕ → State → Ω → ℝ
  decode : Ω → ℝ
  oracleCalls : Instruction → ℕ
  additionalGates : Instruction → ℕ
  width : ℕ

/-- A word in the supplied model that realizes the estimator's law and values.
`calls` and `gates` count totals across repetitions; `depth` counts serial layers
per repetition and `qubits` equals model width. Primitive charges are assumptions
of the model. An empty word cannot certify a nonzero per-repetition depth. -/
structure EstimatorExecution {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (M : EstimatorCircuitModel Ω) where
  word : List M.Instruction
  repetitions_pos : 0 < E.reps
  law_eq : E.prob = M.law E.reps (word.foldl M.step M.initial)
  value_eq : E.value = M.decode
  calls_eq : E.calls = E.reps * (word.map M.oracleCalls).sum
  gates_eq : E.gates = E.reps * (word.map M.additionalGates).sum
  qubits_eq : E.qubits = M.width
  depth_eq : E.depth = word.length

/-- A nonempty implemented word has positive per-repetition depth. -/
theorem EstimatorExecution.depth_pos {Ω : Type*} [Fintype Ω]
    {E : IncoherentEstimator Ω} {M : EstimatorCircuitModel Ω}
    (h : EstimatorExecution E M) (hne : h.word ≠ []) : 0 < E.depth := by
  rw [h.depth_eq]
  exact List.length_pos_iff.mpr hne

/-- Conditional accounting: an implemented repeated word is charged once per
repetition for every oracle call in that very word. No estimator existence follows. -/
theorem estimator_total_calls {Ω : Type*} [Fintype Ω]
    (E : IncoherentEstimator Ω) (M : EstimatorCircuitModel Ω)
    (h : EstimatorExecution E M) :
    E.calls = E.reps * (h.word.map M.oracleCalls).sum := h.calls_eq

/-- **Statement only — not proved in Qatlib.**
An estimator in a supplied circuit model meeting a chosen depth bound and success
target. The budget may be `theorem1DepthBudget`; that formula alone establishes
neither implementation nor success. This is not a proof of Theorem 1. -/
def estimator_statement {Ω : Type*} [Fintype Ω] (M : EstimatorCircuitModel Ω)
    (target δ η depthBudget : ℝ) : Prop :=
  ∃ E : IncoherentEstimator Ω, Nonempty (EstimatorExecution E M) ∧
    EstimatesWithin E target δ η ∧ (E.depth : ℝ) ≤ depthBudget

end

end Qatlib.Papers.StreamlineTDA22.MainResults
