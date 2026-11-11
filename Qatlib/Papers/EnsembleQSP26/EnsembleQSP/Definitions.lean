/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnsembleQSP26.EnsembleQSP.SourceModel
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# EnsembleQSP26 — shared definitions for the algorithmic claims

Fixed version: arXiv:2601.20073v1 (first submitted 2026-01-27).

These definitions support the statements of Theorems 13, 14, 15 and the
application theorems 17, 18, 19:

* `topLeftBlock r0 U` extracts the top-left block of a matrix acting on
  `S × Rb` at ancilla state `r0` (the paper's `⟨0|_anc · |0⟩_anc` block);
* `empiricalAverage Pe` is the sample mean of `M` iid noisy reduction blocks
  (the estimator run by Algorithms 2 and 4);
* `probEvent_mono`, `expect_add_const`, `avg_add_const` are the elementary
  probability facts used by the concentration statements.

No claim is stated here; only re-usable definitions and elementary lemmas.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix BigOperators

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Papers.EnsembleQSP26.EnsembleQSP

/-- The top-left block of `U` acting on `S × Rb` at ancilla state `r0`. -/
def topLeftBlock {S Rb : Type*} (r0 : Rb) (U : Matrix (S × Rb) (S × Rb) ℂ) : Matrix S S ℂ :=
  fun i j => U (i, r0) (j, r0)

/-- The sample mean of `M` iid noisy reduction blocks `Pe`. -/
noncomputable def empiricalAverage {S X : Type*} [Fintype S] {M : ℕ}
    (Pe : X → Matrix S S ℂ) : (Fin M → X) → Matrix S S ℂ :=
  fun seeds i j => (1 / (M : ℂ)) * ∑ m, Pe (seeds m) i j

section ProbFacts

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The expectation of `f + c` is the expectation of `f` shifted by `c`. -/
theorem expect_add_const (p : FinDist X) (f : X → ℝ) (c : ℝ) :
    p.expect (fun x => f x + c) = p.expect f + c := by
  unfold FinDist.expect
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_mul, p.sum_one, one_mul]

/-- The empirical average of `f + c` is the empirical average of `f` shifted by `c`
(the sample size is positive). -/
theorem avg_add_const {L : ℕ} (hL : 0 < L) (f : X → ℝ) (c : ℝ) (ω : Fin L → X) :
    FinDist.avg (fun x => f x + c) ω = FinDist.avg f ω + c := by
  unfold FinDist.avg
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, add_div]
  congr 1
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  exact mul_div_cancel_left₀ c hL'

/-- Monotonicity of the event probability in the event. -/
theorem probEvent_mono {L : ℕ} (p : FinDist X) {E E' : (Fin L → X) → Prop}
    [DecidablePred E] [DecidablePred E'] (h : ∀ ω, E ω → E' ω) :
    p.probEvent E ≤ p.probEvent E' := by
  simp only [FinDist.probEvent]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, h ω hω.2⟩
  · intro ω _ _
    simp only [FinDist.probOf]
    exact Finset.prod_nonneg (fun i _ => p.nonneg (ω i))

end ProbFacts

end Qatlib.Papers.EnsembleQSP26.EnsembleQSP
