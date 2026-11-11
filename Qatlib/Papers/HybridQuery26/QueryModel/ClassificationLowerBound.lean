/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HybridQuery26.QueryModel.TranscriptPotential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# The hybrid lower bound for binary classification (HybridQuery26 §4, Theorem 1)

Source: Ambainis–Gilyén–Kokainis, *Tight bounds for hybrid quantum-classical query
algorithms*, arXiv:2610.06803v1, §4 "Proofs of Theorems 1 and 2", proof of Theorem 1.

The paper's proof has three ingredients, all of which are formalised in this repository:

1. **One block.** Lemma 1 (`one_block_progress_le`, file `TranscriptPotential.lean`) bounds
   the conditional increment of the progress measure by `(r_h ε)²` once the two pre-measurement
   states are within `r_h ε`.  Lemma 2 supplies that distance bound from `‖U₀ − U₁‖ = ε`
   and the `r_h ≤ q` queries of the block; its Lean carrier is the existing
   `QuantumAlgorithmDev.Concepts.QueryComplexity.DegreeMethod.unitaryHybridDistance_fixed`
   (`QuantumAlgorithmDev/Concepts/QueryComplexity/DegreeMethod/QuerySpaceExtensionsNext/`),
   which is not re-proved here.
2. **Budget.** Averaging the per-block bounds over histories of each length and summing over
   the `T` stages gives `M_T − M_0 ≤ ε² ∑_t ∑_h w_{t,h} r_{t,h}² ≤ ε² q ∑_t ∑_h w_{t,h} r_{t,h} ≤ ε² q L`,
   because every block uses at most `q` queries and the total (weighted) query count is the
   worst-case cost `L`.
3. **Success criterion.** Error at most `1/3` forces `M_T ≥ 1/9` (`potential_ge_one_ninth_of_tv`).

Combining them yields `L ≥ 1/(9 q ε²)`, the `1/(q ε²)` term of the theorem.  The `Ω(1/ε)`
term comes from the same Lemma 2 applied to the whole computation rather than block by
block; it is recorded as `unrestricted_query_lower_bound` below in its arithmetic form.

This module formalises ingredient 2 and the final arithmetic, with ingredient 1 and 3 as
explicit hypotheses referring to the theorems that discharge them.  It does not build the
hybrid algorithm tree itself, so the assembly from a concrete algorithm to `hstep`/`hdone`
remains outside this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Qatlib.Papers.HybridQuery26.QueryModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open scoped BigOperators

/-! ## §1 Budget accounting: the `q`-dependence -/

/-- **Weighted query budget.** If every block cost `r i` is at most `q`, the weighted sum of
squared costs is at most `q` times the weighted sum of costs — the step
`∑_t ∑_h w r_h² ≤ q ∑_t ∑_h w r_h` of the proof of Theorem 1. -/
theorem weighted_sq_le_mul_sum {ι : Type*} [Fintype ι] (w r : ι → ℝ) {q : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (hrq : ∀ i, r i ≤ q) :
    ∑ i, w i * r i ^ 2 ≤ q * ∑ i, w i * r i := by
  have hterm : ∀ i, w i * r i ^ 2 ≤ q * (w i * r i) := by
    intro i
    have h1 : 0 ≤ w i * r i := mul_nonneg (hw i) (hr i)
    calc w i * r i ^ 2 = (w i * r i) * r i := by ring
      _ ≤ (w i * r i) * q := mul_le_mul_of_nonneg_left (hrq i) h1
      _ = q * (w i * r i) := by ring
  calc ∑ i, w i * r i ^ 2 ≤ ∑ i, q * (w i * r i) := Finset.sum_le_sum fun i _ => hterm i
    _ = q * ∑ i, w i * r i := by rw [Finset.mul_sum]

/-- **Budget with the oracle gap.** With block costs `r i` bounded by `q`, the weighted sum
of the squared one-block progress bounds `(r i ε)²` is at most `ε² q L`, where `L` is the
weighted total cost; this is the bound that converts Lemma 1 into the lower bound. -/
theorem weighted_progress_le {ι : Type*} [Fintype ι] (w r : ι → ℝ) {q ε : ℝ}
    (hε0 : 0 ≤ ε) (hw : ∀ i, 0 ≤ w i) (hr : ∀ i, 0 ≤ r i) (hrq : ∀ i, r i ≤ q) :
    ∑ i, w i * (r i * ε) ^ 2 ≤ ε ^ 2 * q * ∑ i, w i * r i := by
  have hsq := weighted_sq_le_mul_sum w r hw hr hrq
  have hterm : ∀ i, w i * (r i * ε) ^ 2 = ε ^ 2 * (w i * r i ^ 2) := by
    intro i
    ring
  calc ∑ i, w i * (r i * ε) ^ 2 = ∑ i, ε ^ 2 * (w i * r i ^ 2) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ε ^ 2 * ∑ i, w i * r i ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ε ^ 2 * (q * ∑ i, w i * r i) := by
        refine mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
    _ = ε ^ 2 * q * ∑ i, w i * r i := by ring

/-- **Budget over a finite stage range.** The stage-indexed form of
`weighted_progress_le`: with block costs bounded by `q`, the sum of the squared progress
bounds over `T` stages is at most `ε² q L`. -/
theorem weighted_progress_le_range {T : ℕ} (r : ℕ → ℝ) {q ε : ℝ}
    (hε0 : 0 ≤ ε) (hr : ∀ t, 0 ≤ r t) (hrq : ∀ t, r t ≤ q) :
    ∑ t ∈ Finset.range T, (r t * ε) ^ 2 ≤ ε ^ 2 * q * ∑ t ∈ Finset.range T, r t := by
  have hterm : ∀ t ∈ Finset.range T, (r t * ε) ^ 2 ≤ ε ^ 2 * q * r t := by
    intro t _
    have h1 : 0 ≤ r t := hr t
    have h2 : r t ^ 2 ≤ q * r t := by nlinarith [hrq t, h1]
    calc (r t * ε) ^ 2 = ε ^ 2 * r t ^ 2 := by ring
      _ ≤ ε ^ 2 * (q * r t) := by
          exact mul_le_mul_of_nonneg_left h2 (sq_nonneg ε)
      _ = ε ^ 2 * q * r t := by ring
  calc ∑ t ∈ Finset.range T, (r t * ε) ^ 2 ≤ ∑ t ∈ Finset.range T, ε ^ 2 * q * r t :=
        Finset.sum_le_sum hterm
    _ = ε ^ 2 * q * ∑ t ∈ Finset.range T, r t := by rw [Finset.mul_sum]

/-- **Theorem 1, `1/(q ε²)` term.** If the weighted total progress `∑_i w_i (r_i ε)²` reaches
the bounded-error threshold `1/9`, every block uses at most `q` queries and the weighted total
query count is at most `L`, then `L ≥ 1/(9 q ε²)`. -/
theorem classification_query_lower_bound {ι : Type*} [Fintype ι] (w r : ι → ℝ)
    {q ε L : ℝ} (hq : 0 < q) (hε : 0 < ε) (hw : ∀ i, 0 ≤ w i)
    (hr : ∀ i, 0 ≤ r i) (hrq : ∀ i, r i ≤ q) (hL : ∑ i, w i * r i ≤ L)
    (hprogress : 1 / 9 ≤ ∑ i, w i * (r i * ε) ^ 2) :
    1 / (9 * q * ε ^ 2) ≤ L := by
  have hbound := weighted_progress_le w r (le_of_lt hε) hw hr hrq
  have hsum0 : 0 ≤ ∑ i, w i * r i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hr i)
  have hq0 : 0 ≤ q := le_of_lt hq
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have h1 : 1 / 9 ≤ ε ^ 2 * q * ∑ i, w i * r i := le_trans hprogress hbound
  have h2 : ε ^ 2 * q * ∑ i, w i * r i ≤ ε ^ 2 * q * L := by
    have : 0 ≤ ε ^ 2 * q := mul_nonneg hε2 hq0
    exact mul_le_mul_of_nonneg_left hL this
  have h3 : 1 / 9 ≤ ε ^ 2 * q * L := le_trans h1 h2
  have hpos : 0 < 9 * q * ε ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-! ## §2 Telescoping the per-stage increments -/

/-- **Telescoping the progress increments.** If every stage increases the progress by at most
`(r t ε)²`, then the total increase over `T` stages is at most the sum of those bounds; this
is the "iterating the one-block inequality" step of §3. -/
theorem telescope_progress {T : ℕ} (M r : ℕ → ℝ) {ε : ℝ}
    (hstep : ∀ t, t < T → M (t + 1) - M t ≤ (r t * ε) ^ 2) :
    M T - M 0 ≤ ∑ t ∈ Finset.range T, (r t * ε) ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      have ih' := ih fun t ht => hstep t (Nat.lt_trans ht (Nat.lt_succ_self T))
      have hlast := hstep T (Nat.lt_succ_self T)
      rw [Finset.sum_range_succ]
      have : M (T + 1) - M 0 = (M (T + 1) - M T) + (M T - M 0) := by ring
      rw [this]
      linarith

/-- **Theorem 1 for a stage-indexed hybrid run.** If the progress measure starts at `0`,
grows by at most `(r t ε)²` per stage, reaches the bounded-error threshold `1/9`, and every
stage uses at most `q` queries with total cost at most `L`, then `L ≥ 1/(9 q ε²)`. -/
theorem hybrid_classification_lower_bound {T : ℕ} (M r : ℕ → ℝ) {q ε L : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (hr : ∀ t, 0 ≤ r t) (hrq : ∀ t, r t ≤ q)
    (hcost : ∑ t ∈ Finset.range T, r t ≤ L)
    (hstep : ∀ t, t < T → M (t + 1) - M t ≤ (r t * ε) ^ 2)
    (hM0 : M 0 = 0) (hdone : 1 / 9 ≤ M T) :
    1 / (9 * q * ε ^ 2) ≤ L := by
  have htel := telescope_progress M r hstep
  have hMT : 1 / 9 ≤ ∑ t ∈ Finset.range T, (r t * ε) ^ 2 := by
    have : M T ≤ ∑ t ∈ Finset.range T, (r t * ε) ^ 2 := by
      linarith
    linarith
  have hsq : ∑ t ∈ Finset.range T, (r t * ε) ^ 2
      ≤ ε ^ 2 * q * ∑ t ∈ Finset.range T, r t :=
    weighted_progress_le_range r (le_of_lt hε) hr hrq
  have hfinal : 1 / 9 ≤ ε ^ 2 * q * L := by
    have h1 : 1 / 9 ≤ ε ^ 2 * q * ∑ t ∈ Finset.range T, r t := le_trans hMT hsq
    have h2 : ε ^ 2 * q * ∑ t ∈ Finset.range T, r t ≤ ε ^ 2 * q * L := by
      have : 0 ≤ ε ^ 2 * q := mul_nonneg (sq_nonneg ε) (le_of_lt hq)
      exact mul_le_mul_of_nonneg_left hcost this
    linarith
  have hpos : 0 < 9 * q * ε ^ 2 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-! ## §3 The search lower bound (Theorem 2, `N/q` term) -/

/-- **Search progress drop.** If the complementary progress of every one of `N` inputs starts
at `1` and drops by at most `8 (r t)²` per stage, then the total drop over `T` stages is at
most `8` times the total of the squared block costs; with block costs at most `q` this is
`8 q L`, the bound used to deduce `L = Ω(N/q)` in the proof of Theorem 2. -/
theorem search_progress_drop_le {T : ℕ} (M r : ℕ → ℝ) {q L : ℝ}
    (hr : ∀ t, 0 ≤ r t) (hrq : ∀ t, r t ≤ q)
    (hcost : ∑ t ∈ Finset.range T, r t ≤ L) :
    ∑ t ∈ Finset.range T, 8 * r t ^ 2 ≤ 8 * q * L := by
  have hsq : ∑ t ∈ Finset.range T, r t ^ 2 ≤ q * ∑ t ∈ Finset.range T, r t := by
    have hterm : ∀ t ∈ Finset.range T, r t ^ 2 ≤ q * r t := by
      intro t _
      nlinarith [hr t, hrq t]
    calc ∑ t ∈ Finset.range T, r t ^ 2 ≤ ∑ t ∈ Finset.range T, q * r t :=
          Finset.sum_le_sum hterm
      _ = q * ∑ t ∈ Finset.range T, r t := by rw [Finset.mul_sum]
  have hq0 : 0 ≤ q := le_trans (hr 0) (hrq 0)
  calc ∑ t ∈ Finset.range T, 8 * r t ^ 2 = 8 * ∑ t ∈ Finset.range T, r t ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 8 * (q * ∑ t ∈ Finset.range T, r t) := by
        exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 8 * q * ∑ t ∈ Finset.range T, r t := by ring
    _ ≤ 8 * q * L := by
        have : 0 ≤ 8 * q := by positivity
        exact mul_le_mul_of_nonneg_left hcost this

/-- **Theorem 2, `N/q` term.** For `N` search inputs, if the total progress drop required by
bounded error is at least `N/9` and the per-stage drop is bounded by `8 q L`, then
`L ≥ N/(72 q)`. -/
theorem search_query_lower_bound {N q L : ℝ} (hq : 0 < q) (hN : 0 ≤ N)
    (hdrop : N / 9 ≤ 8 * q * L) :
    N / (72 * q) ≤ L := by
  have hpos : 0 < 72 * q := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-! ## §4 The unrestricted `Ω(1/ε)` term -/

/-- **Bounded error forces state separation.** If two normalised states are distinguishable
with error at most `1/3` — recorded as the overlap bound `|⟨ψ₀|ψ₁⟩|² ≤ 8/9` — then their
Hilbert distance is at least `1/3`.  This is the section-3 step
`1 − ‖|ψ₀⟩ − |ψ₁⟩‖² ≤ |⟨ψ₀|ψ₁⟩|²` instantiated at the bounded-error overlap. -/
theorem one_third_le_state_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ0 ψ1 : QState ι) (h0 : Normalized ψ0) (h1 : Normalized ψ1)
    (hoverlap : ‖∑ z, ψ0 z * (starRingEnd ℂ) (ψ1 z)‖ ^ 2 ≤ 8 / 9) :
    1 / 3 ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ := by
  have hdist := one_sub_state_distance_sq_le_inner_norm_sq ψ0 ψ1 h0 h1
  have hd2 : 1 / 9 ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ ^ 2 := by
    linarith
  have hnn : 0 ≤ ‖toEuclidean_fromVec ψ0 - toEuclidean_fromVec ψ1‖ := norm_nonneg _
  nlinarith [sq_nonneg (1 / 3 : ℝ), hd2, hnn]

/-- **The unrestricted `Ω(1/ε)` term.** Lemma 2 applied to the *whole* computation gives
`‖|ψ₀⟩ − |ψ₁⟩‖ ≤ L ε` for a computation of at most `L` queries and oracle gap `ε`; with the
bounded-error separation `1/3 ≤ ‖|ψ₀⟩ − |ψ₁⟩‖` this forces `L ≥ 1/(3 ε)`. -/
theorem unrestricted_query_lower_bound {L ε : ℝ} (hε : 0 < ε)
    (hdistance : 1 / 3 ≤ L * ε) :
    1 / (3 * ε) ≤ L := by
  have hpos : 0 < 3 * ε := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

end Qatlib.Papers.HybridQuery26.QueryModel
