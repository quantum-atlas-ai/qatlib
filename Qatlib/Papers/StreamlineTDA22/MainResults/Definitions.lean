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
analysis with exponentially fewer qubits* (arXiv:2209.12887, accepted in Quantum
2026-02-17; the PDF/plain-text snapshot used here is `2209.12887.pdf` /
`2209.12887.txt` from the qatlas asset cache).

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
  and the cost ledger (`reps`, `calls`, `gates`, `qubits`, `depth`) that the
  paper's complexity statements charge;
* the explicit depth budget of Theorem 1, Eq. (1).

The quantum-circuit *semantics* (that the estimator is produced by the
amplitude-estimation circuit of Appendix B.1/B.2) is the content of the claim
files; this vocabulary only fixes the accounting interface.
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

/-- An incoherent-repetition estimator: a finite outcome space `Ω` with a
probability law, an estimate `value ω` for each outcome, and the resource
ledger charged by the paper (`reps` incoherent repetitions of a circuit with
`calls` oracle calls, `gates` additional single- and two-qubit gates, `qubits`
qubits and `depth` circuit depth). -/
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

/-- A successful estimator: the estimate is within additive `δ` of `target`
with probability at least `1 − η`. -/
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

/-- Theorem 1's depth, Eq. (1):
`Õ( N^{3/2} sqrt(k β^{i,j}_k) / (Δ Λ_{ΠΠ}^{1/2} min(Λ_∂i, Λ_∂j)) )`.
The `Õ` suppresses polylogarithmic factors; the explicit representative used
here carries the factor `(1 + log N)^2` and the constant `2`. -/
noncomputable def theorem1DepthBudget (N k : ℕ) (β Δ Λdi Λdj Λpipi : ℝ) : ℝ :=
  2 * (1 + Real.log (N : ℝ)) ^ 2 * (N : ℝ) ^ (3 / 2 : ℝ) *
    Real.sqrt ((k : ℝ) * β) /
      (Δ * Real.sqrt Λpipi * min Λdi Λdj)

/-- Theorem 1's qubit count, `O(min{k log N, N})` (the constant is folded into
the contract's existential, so this is the bare scale). -/
noncomputable def theorem1QubitScale (N k : ℕ) : ℝ :=
  min ((k : ℝ) * Real.log (N : ℝ)) (N : ℝ)

end

end Qatlib.Papers.StreamlineTDA22.MainResults
