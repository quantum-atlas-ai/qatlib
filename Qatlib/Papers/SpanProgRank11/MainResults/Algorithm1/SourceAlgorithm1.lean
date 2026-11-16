/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

@[expose] public section


/-!
The legacy rank-algorithm record, its witness arithmetic, and an omniscient zero-cost inhabitant. The negative-witness cost probe diagnoses the promoted model. Gaussian span-program construction and source oracle-cost bridge remain deferred.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.SpanProgRank11.MainResults

namespace Qatlib.Papers.SpanProgRank11.MainResults.Algorithm1

open Qatlib.Papers.SpanProgRank11.MainResults
open Matrix
open scoped BigOperators ENNReal

/-- The positive-witness-size bound derived in the proof of Algorithm 1
(Sec. 4.2, p. 9): `‖w‖² = O((n−r+1) r L²)` with probability `5/6`, via
`E‖x‖² = s c(Ṽ)² = O(s)`, `E[t'ᵢ²] = 1 + E‖x‖² = O(1+s)`, and
`E‖w‖² = Σ_i (1/σ_i²) E[t'ᵢ²] = O((1+s) r c_r(A)²)` followed by Markov. -/
def rankPositiveWitnessBound (n r : ℕ) (L : ℝ) : ℝ :=
  ((n - r + 1 : ℕ) : ℝ) * (r : ℝ) * L ^ 2

/-- The negative-witness-size bound `O(1)` of the proof of Algorithm 1
(Sec. 4.2, p. 9): a negative instance has witness size `1/t₁²`, which is `O(1)`
with probability `5/6`. -/
def rankNegativeWitnessBound : ℝ := 1

/-- The witness-size-to-query-count arithmetic of Algorithm 1: if the rank span
program has positive witness size `O((n−r+1) r L²)` and negative witness size
`O(1)`, its geometric-mean witness size is `O(√(r(n−r+1)) L)`.

This is the `wsize` computation after which Theorem 11 gives the
`O(√(r(n−r+1)) L T)` query bound (Sec. 4.2, p. 9–10). -/
theorem source_algorithm1_witness_arithmetic (n r : ℕ) (L : ℝ)
    (hr : 0 < r) (_hrn : r ≤ n) (hL : 0 ≤ L) :
    geometricWitnessSize (rankPositiveWitnessBound n r L) rankNegativeWitnessBound
      ≤ Real.sqrt ((r : ℝ) * ((n - r + 1 : ℕ) : ℝ)) * L := by
  unfold geometricWitnessSize rankPositiveWitnessBound rankNegativeWitnessBound
  have hcast : ((n - r + 1 : ℕ) : ℝ) * (r : ℝ) * L ^ 2 * 1
      = ((r : ℝ) * ((n - r + 1 : ℕ) : ℝ)) * L ^ 2 := by ring
  rw [hcast, Real.sqrt_mul (by positivity) (L ^ 2), Real.sqrt_sq hL]

/-- The promise of the rank problem in Algorithm 1 (Sec. 1, p. 2): every entry
is bounded by `1` in absolute value, and every matrix of rank `≥ r` satisfies
`c_r(A) ≤ L`.  `rank A ≥ r` is `σ_r(A) > 0` (the `(r−1)`-th zero-indexed
singular value is the paper's `σ_r`). -/
def RankPromise (n m r : ℕ) (L : ℝ) (A : SourceMatrix n m) : Prop :=
  (∀ i j, |A i j| ≤ 1) ∧
    (sourceSingularValue A (r - 1) > 0 → sourceCr A r ≤ ENNReal.ofReal L)

/-- Observable data of a promised-rank query algorithm: its query count `T·L·…`
and its answer function, which must decide `rank A ≥ r` on the promise. -/
structure RankAlgorithmModel (n m r : ℕ) (L : ℝ) where
  /-- The number of quantum queries of the algorithm. -/
  queryCount : ℝ
  /-- The algorithm's decision on each input matrix. -/
  answer : SourceMatrix n m → Bool
  /-- Correctness on the promised inputs (Sec. 4.2, p. 9). -/
  correctOnPromise : ∀ A : SourceMatrix n m,
    RankPromise n m r L A → (answer A = true ↔ sourceSingularValue A (r - 1) > 0)

/-- The legacy free-field model admits a zero-cost omniscient answer.
This does not implement a matrix oracle algorithm. -/
theorem source_algorithm1 (n m r : ℕ) (L T : ℝ) (hr : 0 < r) (_hrn : r ≤ n)
    (hL : 0 ≤ L) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∃ alg : RankAlgorithmModel n m r L,
      alg.queryCount ≤ C * Real.sqrt ((r : ℝ) * ((n - r + 1 : ℕ) : ℝ)) * L * T := by
  classical
  refine ⟨1, one_pos, { queryCount := 0, answer := fun A => decide (sourceSingularValue A (r - 1) > 0), correctOnPromise := ?_ }, ?_⟩
  · intro A hA
    simp
  · positivity

/-- The promoted negative-witness cost vanishes on every negative witness.
The source paper instead measures the squared norm of the witness itself. -/
theorem negative_cost_zero {n m : ℕ} (P : HighLevelSpanProgram n m)
    (A : SourceMatrix n m) (w : Fin n → ℝ) (hw : w ∈ negativeWitnessSet P A) :
    negWitnessSize A w = 0 := by
  obtain ⟨_, ha, _⟩ := hw
  unfold negWitnessSize
  apply Finset.sum_eq_zero
  intro j hj
  rw [ha j]
  norm_num

end Qatlib.Papers.SpanProgRank11.MainResults.Algorithm1
