/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.InteractionPictureDefs
import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreCompleteWindow

/-!
# Interaction-picture resource bounds and index sorting

This module proves cutoff identities, segment and sparse-program resource counts, and
failure-budget bounds for interaction-picture simulation, related to [LowWiebe2018]. It also
verifies index swapping and comparison schedules, derives exact bitonic-network lengths and
endpoint bounds, and shows both that the bitonic schedule can exceed the specified comparator
budget and that a bare comparator is not injective.

## Main statements

* `ip25_sort_schedule_count_le_budget`: The generated index-sort schedule fits within
  `ip25SortingComparators k`.
* `clause26_endpoint`: Collects segment resource counts, error and failure budgets, the eventual
  Dyson query-rate bound, auxiliary bit bounds, and exact logarithmic rate and cutoff
  identities.
* `ip25BitonicSort_exceeds_budget`: For m ≥ 5, the bitonic sort schedule on 2ᵐ positions exceeds
  `ip25SortingComparators (2 ^ m)`.
* `ip25_index_compare_not_injective`: The ascending compare operation on two-entry vectors with
  values in `Fin 2` is not injective.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace Qatlib.Concepts.AmpTransform.LegendreWindow

open Matrix
open Qatlib
open MeasureTheory
open Filter
open Set
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The printed interaction-picture cutoff equals `ip25CorrectedCutoff`. -/
theorem ip25_printed_cutoff_correction (ε : ℝ) :
    ipPrintedCutoff ε = ip25CorrectedCutoff ε := by
  rw [ipPrintedCutoff_simplified]
  rfl

/-- The corrected cutoff is at least two for accuracies satisfying `ipPrintedRange`. -/
theorem ip25_corrected_cutoff_ge_two (ε : ℝ) (h : ipPrintedRange ε) :
    2 ≤ ip25CorrectedCutoff ε := by
  rw [← ip25_printed_cutoff_correction]
  exact ipPrintedCutoff_ge_two ε h

/-- The dyadic accuracy 2⁻ᵏ is strictly positive. -/
theorem ip25_dyadic_accuracy_pos (k : ℕ) : 0 < ip25DyadicAccuracy k := by
  unfold ip25DyadicAccuracy
  positivity

/-- The dyadic accuracy 2⁻ᵏ is at most one. -/
theorem ip25_dyadic_accuracy_le_one (k : ℕ) : ip25DyadicAccuracy k ≤ 1 := by
  unfold ip25DyadicAccuracy
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := (inv_le_one₀ hpos).mpr hone
  linarith

/-- The closed-form grid size bounds both 16t²(χ+Λ²)2ᵏ and the square of the closed-form cutoff,
assuming the first quantity is nonnegative. -/
theorem ip25_grid_condition_at_dyadic (t Λ χ : ℝ) (k : ℕ)
    (h : 0 ≤ 16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k) :
    ipSourceGridCondition t Λ χ k :=
  ipSourceGridCondition_holds t Λ χ k h

/-- For 0 ≤ x ≤ log 2 and K = `ipClosedFormK k`, the truncation term 2x^(K+1)/(K+1)! is at most
2⁻ᵏ/2. -/
theorem ip25_truncation_tail (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.log 2) :
    ipTruncationTail k x :=
  ipTruncationTail_holds k x hx0 hx

/-- Applying the index transposition exchanging i and j twice returns the original position. -/
theorem ip25_index_transposition_involutive {k : ℕ} (i j : Fin k) (p : Fin k) :
    ip25IndexTransposition i j (ip25IndexTransposition i j p) = p := by
  by_cases hpi : p = i
  · rw [hpi]
    have h1 : ip25IndexTransposition i j i = j := by simp [ip25IndexTransposition]
    simp only [h1]
    by_cases hji : j = i
    · rw [hji]
      simp [ip25IndexTransposition]
    · simp [ip25IndexTransposition, hji]
  · by_cases hpj : p = j
    · rw [hpj]
      by_cases hji : j = i
      · rw [hji]
        simp [ip25IndexTransposition]
      · have h1 : ip25IndexTransposition i j j = i := by simp [ip25IndexTransposition, hji]
        simp only [h1]
        have h2 : ip25IndexTransposition i j i = j := by simp [ip25IndexTransposition]
        simp only [h2]
    · have h1 : ip25IndexTransposition i j p = p := by
        simp [ip25IndexTransposition, hpi, hpj]
      simp only [h1]

/-- The index transposition exchanging i and j is injective. -/
theorem ip25_index_transposition_injective {k : ℕ} (i j : Fin k) :
    Function.Injective (ip25IndexTransposition i j) := by
  intro a b hab
  have h := congrArg (ip25IndexTransposition i j) hab
  rw [ip25_index_transposition_involutive, ip25_index_transposition_involutive] at h
  exact h

/-- Swapping positions i and j places the original value at j in position i. -/
theorem ip25_index_swap_apply_i {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ip25IndexSwap i j v i = v j := by
  simp [ip25IndexSwap, ip25IndexTransposition]

/-- Swapping positions i and j places the original value at i in position j. -/
theorem ip25_index_swap_apply_j {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ip25IndexSwap i j v j = v i := by
  by_cases hji : j = i
  · rw [hji]
    simp [ip25IndexSwap, ip25IndexTransposition]
  · simp [ip25IndexSwap, ip25IndexTransposition, hji]

/-- Swapping positions i and j preserves the value at every other position. -/
theorem ip25_index_swap_apply_other {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M)
    (p : Fin k) (hpi : p ≠ i) (hpj : p ≠ j) :
    ip25IndexSwap i j v p = v p := by
  simp [ip25IndexSwap, ip25IndexTransposition, hpi, hpj]

/-- Applying the same index swap twice restores the input vector. -/
theorem ip25_index_swap_involutive {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ip25IndexSwap i j (ip25IndexSwap i j v) = v := by
  funext p
  simp [ip25IndexSwap, ip25_index_transposition_involutive]

/-- Swapping indices is precomposition with the corresponding index transposition. -/
theorem ip25_index_swap_eq_transposition {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ip25IndexSwap i j v = fun p => v (ip25IndexTransposition i j p) := rfl

/-- The compare operation orders the values at positions i and j. -/
theorem ip25_index_compare_order {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    (ip25IndexCompare i j v) i ≤ (ip25IndexCompare i j v) j := by
  by_cases h : v i ≤ v j
  · simp [ip25IndexCompare, h]
  · have hne : v j < v i := lt_of_not_ge h
    have hij : i ≠ j := by
      intro hc
      subst hc
      exact h (le_refl _)
    rw [show ip25IndexCompare i j v = ip25IndexSwap i j v by simp [ip25IndexCompare, h]]
    rw [ip25_index_swap_apply_i, ip25_index_swap_apply_j]
    exact le_of_lt hne

/-- The index compare operation is idempotent. -/
theorem ip25_index_compare_idem {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ip25IndexCompare i j (ip25IndexCompare i j v) = ip25IndexCompare i j v := by
  have hcond : (ip25IndexCompare i j v) i ≤ (ip25IndexCompare i j v) j :=
    ip25_index_compare_order i j v
  show (if (ip25IndexCompare i j v) i ≤ (ip25IndexCompare i j v) j
      then ip25IndexCompare i j v else ip25IndexSwap i j (ip25IndexCompare i j v))
    = ip25IndexCompare i j v
  rw [if_pos hcond]

/-- For each input vector, the compare operation acts by an involutive permutation of its
positions. -/
theorem ip25_index_compare_is_permutation {M k : ℕ} (i j : Fin k) (v : Fin k → Fin M) :
    ∃ σ : Fin k → Fin k, (∀ p, σ (σ p) = p) ∧
      ip25IndexCompare i j v = fun p => v (σ p) := by
  by_cases h : v i ≤ v j
  · refine ⟨(fun p => p), ?_, ?_⟩
    · intro p
      rfl
    · simp [ip25IndexCompare, h]
  · refine ⟨ip25IndexTransposition i j, ?_, ?_⟩
    · intro p
      exact ip25_index_transposition_involutive i j p
    · rw [show ip25IndexCompare i j v = ip25IndexSwap i j v by simp [ip25IndexCompare, h]]
      exact ip25_index_swap_eq_transposition i j v

/-- Reversing the index vector twice restores the input vector. -/
theorem ip25_index_reverse_involutive {M k : ℕ} (v : Fin k → Fin M) :
    ip25IndexReverse (ip25IndexReverse v) = v := by
  funext p
  simp only [ip25IndexReverse]
  congr 1
  apply Fin.ext
  show k - 1 - (k - 1 - p.val) = p.val
  omega

/-- The reversal gate count `ip25ReverseGates k` equals k. -/
theorem ip25_reverse_gates_eq_length (k : ℕ) : ip25ReverseGates k = k := rfl

/-- The repeated-index cube decomposes into the injective-index cube and the collision cube. -/
theorem ip25_repeated_cube_split {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) :
    ipRepeatedCube H t M k = ipInjectiveCube H t M k + ipCollisionCube H t M k :=
  ipRepeatedCube_split H t M k

/-- The sorted index list retains the original length k. -/
theorem ip25_sorted_index_length (M k : ℕ) (v : Fin k → Fin M) :
    (ipSortedIndexList M k v).length = k := by
  have hperm := ipSortedIndexList_perm M k v
  rw [List.Perm.length_eq hperm]
  simp

/-- The sorting comparator budget is at least the input length k. -/
theorem ip25_sorting_budget_ge_length (k : ℕ) : k ≤ ip25SortingComparators k := by
  unfold ip25SortingComparators
  cases k with
  | zero => simp
  | succ k =>
      have h1 : 1 ≤ Nat.log2 (k + 1) + 1 := by
        omega
      have h2 : 0 ≤ Nat.log2 (k + 1) + 1 := by omega
      calc (k + 1) = (k + 1) * 1 := by simp
        _ ≤ (k + 1) * (Nat.log2 (k + 1) + 1) := Nat.mul_le_mul_left _ h1

/-- The segment gate count is twice `ipSegmentCopies p`. -/
theorem ip26_segment_gate_count (p : EffectiveSegmentParameters) :
    2 * ipSegmentCopies p = ip26SegmentGateCount p := rfl

/-- The total query count is the segment count times the number of copies per segment. -/
theorem ip26_total_queries_exact (p : EffectiveSegmentParameters) :
    ipTotalQueries p = ipSegmentCount p * ipSegmentCopies p := rfl

/-- The total gate count is the segment count times twice the local segment copy count. -/
theorem ip26_total_gates_exact (p : EffectiveSegmentParameters) :
    ipTotalGates p = ipSegmentCount p * (ipSegmentCopies (effectiveLongLocal p) +
      ipSegmentCopies (effectiveLongLocal p)) := rfl

/-- The total qubit count is the local segment width plus the ceiling binary logarithm of the
segment count. -/
theorem ip26_total_qubits_exact (p : EffectiveSegmentParameters) :
    ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + Nat.clog 2 (ipSegmentCount p) := rfl

/-- For L > 0, the sum of L equal segment error budgets equals the total budget ε. -/
theorem ip26_segment_budget_sum (L : ℕ) (ε : ℝ) (hL : 0 < L) :
    (L : ℝ) * ipSegmentBudget L ε = ε :=
  ipSegmentBudget_total L ε hL

/-- For 0 ≤ δ ≤ 1, the total failure bound is at most L times the per-segment failure bound. -/
theorem ip26_total_failure_le (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ipTotalFailure L δ ≤ (L : ℝ) * ipPerSegmentFailure δ :=
  ipTotalFailure_le L δ hδ hδ1

/-- The total failure bound is at most one whenever the linear per-segment failure budget is at
most one. -/
theorem ip26_total_failure_le_one (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hbudget : (L : ℝ) * ipPerSegmentFailure δ ≤ 1) :
    ipTotalFailure L δ ≤ 1 := by
  have h := ip26_total_failure_le L δ hδ hδ1
  linarith

/-- The total query count equals the segment count times `ip26SegmentQueryRate` at the chosen
precision. -/
theorem ip26_actual_query_count (p : EffectiveSegmentParameters) :
    ipTotalQueries p = ipSegmentCount p * ip26SegmentQueryRate p.precision := by
  simp [ipTotalQueries, ipSegmentCount, ip26SegmentQueryRate, ipSegmentQueries, effectiveSegmentK]

/-- For each segment parameter, the computed Dyson cutoff times the ceiling binary logarithm is
eventually bounded by a constant times k+2, with the segment-count factor included. -/
theorem ip26_query_rate_logloglog (p : EffectiveSegmentParameters) :
    ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
      (ipSegmentCount p * computedDysonCutoff (k + 8)) * Nat.clog 2 (k + 2)
        ≤ C * (k + 2) * ipSegmentCount p := by
  obtain ⟨C, m0, hC⟩ := effectiveDysonCutoff_clog_rate
  refine ⟨C, m0, fun k hk => ?_⟩
  calc
    (ipSegmentCount p * computedDysonCutoff (k + 8)) * Nat.clog 2 (k + 2)
        = ipSegmentCount p * (computedDysonCutoff (k + 8) * Nat.clog 2 (k + 2)) := by ring
    _ ≤ ipSegmentCount p * (C * (k + 2)) := Nat.mul_le_mul_left _ (hC k hk)
    _ = C * (k + 2) * ipSegmentCount p := by ring

/-- The auxiliary bit rate is ⌈log₂ L⌉, suffices to encode L values, and is at most `Nat.log 2 L
+ 1`. -/
theorem ip26_aux_bit_rate (L : ℕ) :
    ip26AuxBitRate L = Nat.clog 2 L ∧
      L ≤ 2 ^ (ip26AuxBitRate L) ∧ ip26AuxBitRate L ≤ Nat.log 2 L + 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_refl (Nat.clog 2 L))
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    have hlt : L < 2 ^ (Nat.log 2 L).succ := Nat.lt_pow_succ_log_self (by decide : 1 < 2) L
    have hexp : (Nat.log 2 L).succ = Nat.log 2 L + 1 := by omega
    rw [hexp] at hlt
    exact le_of_lt hlt

/-- The total qubit count is the local segment width plus `ip26AuxBitRate` of the segment count. -/
theorem ip26_actual_aux_bits (p : EffectiveSegmentParameters) :
    ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + ip26AuxBitRate (ipSegmentCount p) := by
  simp [ipTotalQubits, ip26AuxBitRate]

/-- The corrected cutoff is the natural ceiling of `ip26NonBinaryRate ε`. -/
theorem ip26_rate_is_cutoff (ε : ℝ) :
    ip25CorrectedCutoff ε = Nat.ceil (ip26NonBinaryRate ε) := by
  rfl

/-- For a positive nonbinary rate, the corrected cutoff lies between that rate and that rate
plus one, with strict upper inequality. -/
theorem ip26_rate_ceiling_bounds (ε : ℝ) (h : 0 < ip26NonBinaryRate ε) :
    ip26NonBinaryRate ε ≤ (ip25CorrectedCutoff ε : ℝ) ∧
      (ip25CorrectedCutoff ε : ℝ) < ip26NonBinaryRate ε + 1 := by
  have hceil : ip25CorrectedCutoff ε = Nat.ceil (ip26NonBinaryRate ε) := by rfl
  rw [hceil]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one h.le⟩

/-- The nonbinary query rate is positive on `ipPrintedRange`. -/
theorem ip26_rate_pos (ε : ℝ) (h : ipPrintedRange ε) :
    0 < ip26NonBinaryRate ε := by
  have hε : 0 < ε := h.1
  have hε' : ε ≤ 1 / 2 - 1 / Real.exp 1 := h.2
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hone : 1 / 3 < 1 / Real.exp 1 :=
    one_div_lt_one_div_of_lt (Real.exp_pos 1) hexp
  have hbound : ε ≤ 1 / 6 := by linarith
  have h2ε : 12 ≤ 2 / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hlogpos : 0 < Real.log (2 / ε) := Real.log_pos (by linarith)
  have hlog1 : 1 < Real.log (2 / ε) := by
    have hexple : Real.exp 1 < 2 / ε := by linarith
    have h1 := Real.log_lt_log (Real.exp_pos 1) hexple
    rwa [Real.log_exp 1] at h1
  have hden : 0 < Real.log (Real.log (2 / ε)) := Real.log_pos hlog1
  have hnum : 0 < 2 * Real.log (2 / ε) := by positivity
  simp only [ip26NonBinaryRate]
  exact div_pos hnum hden

/-- The nonbinary query rate is greater than one on `ipPrintedRange`. -/
theorem ip26_rate_gt_one (ε : ℝ) (h : ipPrintedRange ε) :
    1 < ip26NonBinaryRate ε := by
  have hpos := ip26_rate_pos ε h
  have hcut : 2 ≤ ip25CorrectedCutoff ε := ip25_corrected_cutoff_ge_two ε h
  have hcut' : (2 : ℝ) ≤ (ip25CorrectedCutoff ε : ℝ) := by exact_mod_cast hcut
  obtain ⟨hle, hlt⟩ := ip26_rate_ceiling_bounds ε hpos
  linarith

/-- For ε > 0, the nonbinary rate equals 2(log(1/ε)+log 2)/log(log(1/ε)+log 2). -/
theorem ip26_rate_in_log_terms (ε : ℝ) (hε : 0 < ε) :
    ip26NonBinaryRate ε
      = 2 * (Real.log (1 / ε) + Real.log 2) / Real.log (Real.log (1 / ε) + Real.log 2) := by
  have h2 : 0 < 1 / ε := by positivity
  have hlog : Real.log (2 / ε) = Real.log (1 / ε) + Real.log 2 := by
    have heq : 2 / ε = 2 * (1 / ε) := by ring
    rw [heq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h2), add_comm]
  simp only [ip26NonBinaryRate]
  rw [hlog]

/-- At dyadic accuracy 2⁻ᵏ, the nonbinary rate equals 2(k+1)log 2/log((k+1)log 2). -/
theorem ip26_rate_dyadic (k : ℕ) :
    ip26NonBinaryRate (ip25DyadicAccuracy k)
      = 2 * ((k + 1) * Real.log 2) / Real.log ((k + 1) * Real.log 2) := by
  have heq : 2 / ip25DyadicAccuracy k = 2 * (2 : ℝ) ^ k := by
    simp only [ip25DyadicAccuracy]
    rw [div_eq_mul_inv, inv_inv]
  have hlog : Real.log (2 / ip25DyadicAccuracy k) = (k + 1) * Real.log 2 := by
    rw [heq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ k ≠ 0),
      Real.log_pow 2 k]
    ring
  simp only [ip26NonBinaryRate]
  rw [hlog]

/-- Collects the exact query and auxiliary-qubit counts and the dyadic nonbinary-rate and
ceiling-cutoff identities. -/
theorem ip26_rate_ledger (p : EffectiveSegmentParameters) :
    (ipTotalQueries p = ipSegmentCount p * ip26SegmentQueryRate p.precision) ∧
    (ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + ip26AuxBitRate (ipSegmentCount p)) ∧
    (ip26NonBinaryRate (ip25DyadicAccuracy p.precision)
      = 2 * ((p.precision + 1) * Real.log 2) / Real.log ((p.precision + 1) * Real.log 2)) ∧
    (ip25CorrectedCutoff (ip25DyadicAccuracy p.precision)
      = Nat.ceil (ip26NonBinaryRate (ip25DyadicAccuracy p.precision))) := by
  refine ⟨ip26_actual_query_count p, ip26_actual_aux_bits p, ip26_rate_dyadic p.precision, ?_⟩
  exact ip26_rate_is_cutoff _

/-- The sparse program's step-list length equals `ip27SparseStepCount p`. -/
theorem ip27_sparse_step_count (p : EffectiveSparseParameters) :
    (ipSparseProgram p).steps.length = ip27SparseStepCount p := by
  unfold ip27SparseStepCount ipSparseProgram
  rfl

/-- The sparse program's width equals `ip27SparseWidth p`. -/
theorem ip27_sparse_width (p : EffectiveSparseParameters) :
    (ipSparseProgram p).width = ip27SparseWidth p := by
  unfold ip27SparseWidth ipSparseProgram
  rfl

/-- The sparse construction uses two queries. -/
theorem ip27_sparse_queries (p : EffectiveSparseParameters) :
    ipSparseQueries p = 2 := rfl

/-- Expands `ipLchsThreeFactor` into the two outer Hamiltonian evolutions and the middle ordered
evolution of the interaction-picture generator. -/
theorem ip27_three_factor_exact (L H : Matrix I I ℂ) (k t : ℝ) :
    ipLchsThreeFactor I L H k t
      = HamiltonianEvolution (k • L) t *
        orderedEvolution (fun u => Complex.I • interactionGenerator (k • L) (fun _ => H) u) 0 t *
        HamiltonianEvolution (-(k • L)) t := rfl

/-- The sparse program's counted queries equal `ipSparseQueries p`. -/
theorem ip27_program_query_count (p : EffectiveSparseParameters) :
    ip27ProgramQueries (ipSparseProgram p) = ipSparseQueries p := by
  simp [ip27ProgramQueries, ipSparseProgram, ipSparseQueries]

/-- The diagonal-augmented program's step-list length equals `ip27DiagonalTotalGates p`. -/
theorem ip27_diagonal_step_count (p : EffectiveSparseParameters) :
    (ip27DiagonalProgram p).steps.length = ip27DiagonalTotalGates p := by
  simp [ip27DiagonalProgram, ip27DiagonalTotalGates, ip27DiagonalGateCount]

/-- Adding the diagonal phase steps preserves the sparse program's query count, and the diagonal
contribution uses zero queries. -/
theorem ip27_diagonal_queries (p : EffectiveSparseParameters) :
    ip27ProgramQueries (ip27DiagonalProgram p) = ip27ProgramQueries (ipSparseProgram p) ∧
      ip27DiagonalQueries p = 0 := by
  constructor
  · simp [ip27ProgramQueries, ip27DiagonalProgram, ipSparseProgram]
  · rfl

/-- The diagonal-augmented program has the same width as the sparse program. -/
theorem ip27_diagonal_width (p : EffectiveSparseParameters) :
    (ip27DiagonalProgram p).width = (ipSparseProgram p).width := by
  simp [ip27DiagonalProgram, ipSparseProgram]

/-- With sufficient fuel, the merge runner returns the accumulated prefix followed by
`List.merge` of the two input lists. -/
theorem ip25_merge_run_eq_merge {α : Type} (le : α → α → Bool) (off : ℕ) :
    ∀ (fuel : ℕ) (res a b : List α), a.length + b.length ≤ fuel →
      (ip25MergeRun le off fuel res a b).1 = res ++ List.merge a b le := by
  intro fuel
  induction fuel with
  | zero =>
      intro res a b h
      have ha : a.length = 0 := by omega
      have hb : b.length = 0 := by omega
      simp [ip25MergeRun, List.eq_nil_of_length_eq_zero ha,
        List.eq_nil_of_length_eq_zero hb]
  | succ fuel ih =>
      intro res a b h
      cases a with
      | nil => simp [ip25MergeRun]
      | cons x xs =>
          cases b with
          | nil => simp [ip25MergeRun]
          | cons y ys =>
              simp only [ip25MergeRun]
              split
              · next hxy =>
                  rw [ih (res ++ [x]) xs (y :: ys)]
                  · simp [hxy]
                  · simp only [List.length_cons] at h ⊢
                    omega
              · next hxy =>
                  rw [ih (res ++ [y]) (x :: xs) ys]
                  · simp [hxy]
                  · simp only [List.length_cons] at h ⊢
                    omega

/-- With sufficient fuel, the merge runner records at most the combined length of the two input
lists in comparisons. -/
theorem ip25_merge_run_count {α : Type} (le : α → α → Bool) (off : ℕ) :
    ∀ (fuel : ℕ) (res a b : List α), a.length + b.length ≤ fuel →
      (ip25MergeRun le off fuel res a b).2.length ≤ a.length + b.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro res a b h
      have ha : a.length = 0 := by omega
      have hb : b.length = 0 := by omega
      simp [ip25MergeRun, List.eq_nil_of_length_eq_zero ha,
        List.eq_nil_of_length_eq_zero hb]
  | succ fuel ih =>
      intro res a b h
      cases a with
      | nil => simp [ip25MergeRun]
      | cons x xs =>
          cases b with
          | nil => simp [ip25MergeRun]
          | cons y ys =>
              simp only [List.length_cons] at h
              simp only [ip25MergeRun]
              split
              · next hxy =>
                  have hrec := ih (res ++ [x]) xs (y :: ys)
                    (by simp only [List.length_cons]; omega)
                  simp only [List.length_cons] at hrec
                  simp only [Prod.fst, Prod.snd, List.length_cons]
                  omega
              · next hxy =>
                  have hrec := ih (res ++ [y]) (x :: xs) ys
                    (by simp only [List.length_cons]; omega)
                  simp only [List.length_cons] at hrec
                  simp only [Prod.fst, Prod.snd, List.length_cons]
                  omega

/-- With sufficient fuel, the sorting runner returns `List.mergeSort` of the input list. -/
theorem ip25_sort_run_eq_mergeSort {α : Type} (le : α → α → Bool) :
    ∀ (off : ℕ) (fuel : ℕ) (xs : List α), xs.length ≤ fuel →
      (ip25SortRunAt le off fuel xs).1 = List.mergeSort xs le := by
  intro off fuel
  induction fuel generalizing off with
  | zero =>
      intro xs h
      have hxs : xs.length = 0 := by omega
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hxs
      simp [ip25SortRunAt, hnil, List.mergeSort]
  | succ fuel ih =>
      intro xs h
      cases xs with
      | nil => simp [ip25SortRunAt, List.mergeSort]
      | cons a xs =>
          cases xs with
          | nil => simp [ip25SortRunAt, List.mergeSort]
          | cons b xs =>
              have hn : (a :: b :: xs).length ≤ fuel + 1 := by simpa using! h
              have hpos : 2 ≤ fuel + 1 := by simp at hn; omega
              have hl : ((a :: b :: xs).take (((a :: b :: xs).length + 1) / 2)).length ≤ fuel := by
                simp only [List.length_take]
                have hhalf : (a :: b :: xs).length + 1 ≤ fuel + 2 := by omega
                omega
              have hr : ((a :: b :: xs).drop (((a :: b :: xs).length + 1) / 2)).length ≤ fuel := by
                simp only [List.length_drop]
                have hhalf : (a :: b :: xs).length + 1 ≤ fuel + 2 := by omega
                omega
              simp only [ip25SortRunAt]
              rw [ih _ _ hl, ih _ _ hr]
              rw [ip25_merge_run_eq_merge le off]
              · simp [List.mergeSort, List.MergeSort.Internal.splitInTwo, List.splitAt_eq]
              · rw [List.length_mergeSort, List.length_mergeSort]

/-- The natural ceiling binary logarithm is monotone. -/
theorem ip25_clog_mono {m n : ℕ} (h : m ≤ n) : Nat.clog 2 m ≤ Nat.clog 2 n := by
  refine Nat.clog_le_of_le_pow ?_
  have := Nat.le_pow_clog (by decide : 1 < 2) n
  omega

/-- The natural ceiling binary logarithm is at most the binary floor logarithm plus one. -/
theorem ip25_clog_le_log2 (n : ℕ) : Nat.clog 2 n ≤ Nat.log2 n + 1 := by
  refine Nat.clog_le_of_le_pow ?_
  have hlt := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  rw [← Nat.log2_eq_log_two] at hlt
  have hmul : n < 2 ^ Nat.log2 n * 2 := by simpa [Nat.pow_succ] using! hlt
  rw [Nat.pow_succ]
  omega

/-- For n ≥ 2, the ceiling binary logarithm of ⌊(n+1)/2⌋ is at most the ceiling binary logarithm
of n minus one. -/
theorem ip25_clog_half (n : ℕ) (h : 2 ≤ n) :
    Nat.clog 2 ((n + 1) / 2) ≤ Nat.clog 2 n - 1 := by
  have hc : 1 ≤ Nat.clog 2 n := by
    by_contra hn
    have h0 : Nat.clog 2 n ≤ 0 := by omega
    have h1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp h0
    omega
  have hle : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide : 1 < 2) n
  refine Nat.clog_le_of_le_pow ?_
  rw [Nat.div_le_iff_le_mul_add_pred (by decide : (0 : ℕ) < 2)]
  have hpow : 2 ^ (Nat.clog 2 n - 1) * 2 = 2 ^ Nat.clog 2 n := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have htwo : 2 * 2 ^ (Nat.clog 2 n - 1) = 2 ^ Nat.clog 2 n := by
    rw [Nat.mul_comm, hpow]
  rw [htwo]
  omega

/-- With sufficient fuel, the sorting runner records at most length times ceiling binary
logarithm of length in comparisons. -/
theorem ip25_sort_run_count {α : Type} (le : α → α → Bool) :
    ∀ (off : ℕ) (fuel : ℕ) (xs : List α), xs.length ≤ fuel →
      (ip25SortRunAt le off fuel xs).2.length ≤ xs.length * Nat.clog 2 xs.length := by
  intro off fuel
  induction fuel generalizing off with
  | zero =>
      intro xs h
      have hxs : xs.length = 0 := by omega
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hxs
      simp [ip25SortRunAt, hnil]
  | succ fuel ih =>
      intro xs h
      cases xs with
      | nil => simp [ip25SortRunAt]
      | cons a xs =>
          cases xs with
          | nil => simp [ip25SortRunAt]
          | cons b xs =>
              have hn : (a :: b :: xs).length ≤ fuel + 1 := by simpa using! h
              have h2 : 2 ≤ (a :: b :: xs).length := by simp
              set n : ℕ := (a :: b :: xs).length with hn_eq
              set m : ℕ := (n + 1) / 2 with hm_eq
              set lt1 : List α := (a :: b :: xs).take m with hlt1
              set lt2 : List α := (a :: b :: xs).drop m with hlt2
              have hml : m ≤ n := by
                rw [hm_eq]
                exact (Nat.div_le_iff_le_mul_add_pred (by decide : (0 : ℕ) < 2)).2 (by omega)
              have hl1 : lt1.length = m := by
                rw [hlt1, List.length_take, Nat.min_eq_left hml]
              have hl2 : lt2.length = n - m := by rw [hlt2, List.length_drop]
              have hml2 : n - m ≤ m := by
                have hmod := Nat.div_add_mod (n + 1) 2
                have hmod1 : (n + 1) % 2 ≤ 1 := by
                  have := Nat.mod_lt (n + 1) (by decide : (0 : ℕ) < 2)
                  omega
                omega
              have hl : lt1.length ≤ fuel := by
                have hmle : m ≤ fuel := by
                  rw [hm_eq]
                  exact (Nat.div_le_iff_le_mul_add_pred (by decide : (0 : ℕ) < 2)).2 (by omega)
                omega
              have hr : lt2.length ≤ fuel := by
                omega
              have hclog1 : Nat.clog 2 lt1.length ≤ Nat.clog 2 n - 1 := by
                rw [hl1, hm_eq]
                exact ip25_clog_half n h2
              have hclog2 : Nat.clog 2 lt2.length ≤ Nat.clog 2 n - 1 := by
                refine le_trans (ip25_clog_mono ?_) hclog1
                rw [hl2, hl1]
                exact hml2
              simp only [ip25SortRunAt, List.length_append]
              rw [← hn_eq, ← hm_eq, ← hlt1, ← hlt2]
              have hcor1 := ip25_sort_run_eq_mergeSort le off fuel lt1 hl
              have hcor2 := ip25_sort_run_eq_mergeSort le (off + lt1.length) fuel lt2 hr
              rw [hcor1, hcor2]
              have hmerge := ip25_merge_run_count le off (lt1.length + lt2.length) []
                (lt1.mergeSort le) (lt2.mergeSort le)
                (by rw [List.length_mergeSort, List.length_mergeSort])
              simp only [List.length_mergeSort, List.length_mergeSort] at hmerge
              have hrec1 := ih off lt1 hl
              have hrec2 := ih (off + lt1.length) lt2 hr
              have hc : 1 ≤ Nat.clog 2 n := by
                by_contra hn
                have h0 : Nat.clog 2 n ≤ 0 := by omega
                have h1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp h0
                omega
              have hid1 : lt1.length * (Nat.clog 2 n - 1) + lt1.length = lt1.length * Nat.clog 2 n := by
                have h1 : Nat.clog 2 n - 1 + 1 = Nat.clog 2 n := by omega
                calc
                  lt1.length * (Nat.clog 2 n - 1) + lt1.length
                      = lt1.length * (Nat.clog 2 n - 1 + 1) := by rw [Nat.mul_succ]
                  _ = lt1.length * Nat.clog 2 n := by rw [h1]
              have hid2 : lt2.length * (Nat.clog 2 n - 1) + lt2.length = lt2.length * Nat.clog 2 n := by
                have h1 : Nat.clog 2 n - 1 + 1 = Nat.clog 2 n := by omega
                calc
                  lt2.length * (Nat.clog 2 n - 1) + lt2.length
                      = lt2.length * (Nat.clog 2 n - 1 + 1) := by rw [Nat.mul_succ]
                  _ = lt2.length * Nat.clog 2 n := by rw [h1]
              have hsum : lt1.length + lt2.length = n := by
                rw [hl1, hl2]
                omega
              have hid3 : (lt1.length + lt2.length) * Nat.clog 2 n = n * Nat.clog 2 n := by
                rw [hsum]
              calc
                (ip25SortRunAt le off fuel lt1).2.length
                    + (ip25SortRunAt le (off + lt1.length) fuel lt2).2.length
                    + (ip25MergeRun le off (lt1.length + lt2.length) []
                        (lt1.mergeSort le) (lt2.mergeSort le)).2.length
                    ≤ lt1.length * Nat.clog 2 lt1.length + lt2.length * Nat.clog 2 lt2.length
                        + (lt1.length + lt2.length) := by omega
                _ ≤ lt1.length * (Nat.clog 2 n - 1) + lt2.length * (Nat.clog 2 n - 1)
                    + (lt1.length + lt2.length) := by
                      have hmul1 : lt1.length * Nat.clog 2 lt1.length
                          ≤ lt1.length * (Nat.clog 2 n - 1) := by
                        exact Nat.mul_le_mul_left _ (by omega)
                      have hmul2 : lt2.length * Nat.clog 2 lt2.length
                          ≤ lt2.length * (Nat.clog 2 n - 1) := by
                        exact Nat.mul_le_mul_left _ (by omega)
                      omega
                _ = (lt1.length + lt2.length) * Nat.clog 2 n := by
                  calc
                    lt1.length * (Nat.clog 2 n - 1) + lt2.length * (Nat.clog 2 n - 1)
                        + (lt1.length + lt2.length)
                        = (lt1.length * (Nat.clog 2 n - 1) + lt1.length)
                            + (lt2.length * (Nat.clog 2 n - 1) + lt2.length) := by omega
                    _ = lt1.length * Nat.clog 2 n + lt2.length * Nat.clog 2 n := by rw [hid1, hid2]
                    _ = (lt1.length + lt2.length) * Nat.clog 2 n := by
                      rw [Nat.mul_comm, Nat.mul_comm, ← Nat.add_mul, Nat.mul_comm]
                _ ≤ n * Nat.clog 2 n := by rw [hid3]

/-- Every position recorded by the merge runner is below the offset plus the total length of the
accumulated prefix and input lists. -/
theorem ip25_merge_run_positions_lt {α : Type} (le : α → α → Bool) (off : ℕ) :
    ∀ (fuel : ℕ) (res a b : List α),
      ∀ p ∈ (ip25MergeRun le off fuel res a b).2,
        p.1 < off + res.length + a.length + b.length ∧
        p.2 < off + res.length + a.length + b.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro res a b p hp
      simp [ip25MergeRun] at hp
  | succ fuel ih =>
      intro res a b p hp
      cases a with
      | nil => simp [ip25MergeRun] at hp
      | cons x xs =>
          cases b with
          | nil => simp [ip25MergeRun] at hp
          | cons y ys =>
              simp only [ip25MergeRun] at hp
              split at hp
              · next hxy =>
                  rcases List.mem_cons.mp hp with hhead | htail
                  · have h1 : p.1 = off + res.length := congrArg Prod.fst hhead
                    have h2 : p.2 = off + res.length + (x :: xs).length := congrArg Prod.snd hhead
                    simp only [List.length_cons] at h1 h2 ⊢
                    constructor <;> omega
                  · have hb := ih (res ++ [x]) xs (y :: ys) p htail
                    simp only [List.length_cons, List.length_nil, List.length_append] at hb ⊢
                    omega
              · next hxy =>
                  rcases List.mem_cons.mp hp with hhead | htail
                  · have h1 : p.1 = off + res.length := congrArg Prod.fst hhead
                    have h2 : p.2 = off + res.length + (x :: xs).length := congrArg Prod.snd hhead
                    simp only [List.length_cons] at h1 h2 ⊢
                    constructor <;> omega
                  · have hb := ih (res ++ [y]) (x :: xs) ys p htail
                    simp only [List.length_cons, List.length_nil, List.length_append] at hb ⊢
                    omega

/-- Sorting the index vector with the comparison runner yields `ipSortedIndexList M k v`. -/
theorem ip25_sort_run_eq_sorted_index_list {M k : ℕ} (v : Fin k → Fin M) :
    (ip25SortRun (fun a b => decide (a ≤ b)) 0 (List.ofFn v)).1 = ipSortedIndexList M k v := by
  have h := ip25_sort_run_eq_mergeSort (fun a b => decide (a ≤ b)) 0 (List.ofFn v).length
    (List.ofFn v) (by simp)
  simpa [ip25SortRun, ipSortedIndexList] using! h

/-- The generated index-sort schedule fits within `ip25SortingComparators k`. -/
theorem ip25_sort_schedule_count_le_budget {M k : ℕ} (v : Fin k → Fin M) :
    (ip25SortSchedule v).length ≤ ip25SortingComparators k := by
  have h := ip25_sort_run_count (fun a b => decide (a ≤ b)) 0 (List.ofFn v).length
    (List.ofFn v) (by simp)
  have h2 := ip25_clog_le_log2 k
  have hmul : k * Nat.clog 2 k ≤ k * (Nat.log2 k + 1) := Nat.mul_le_mul_left _ h2
  have h' : (ip25SortSchedule v).length ≤ k * Nat.clog 2 k := by
    simpa [ip25SortSchedule, ip25SortRun, List.length_ofFn] using! h
  simp only [ip25SortingComparators]
  omega

/-- The generated index-sort schedule has at most k · ⌈log₂ k⌉ comparisons. -/
theorem ip25_sort_schedule_count_le_clog {M k : ℕ} (v : Fin k → Fin M) :
    (ip25SortSchedule v).length ≤ k * Nat.clog 2 k := by
  have h := ip25_sort_run_count (fun a b => decide (a ≤ b)) 0 (List.ofFn v).length
    (List.ofFn v) (by simp)
  simpa [ip25SortSchedule, ip25SortRun, List.length_ofFn] using! h

/-- Collects the corrected cutoff and dyadic accuracy facts, index-operation identities,
sorted-list length, and comparison-runner correctness and schedule bounds. -/
theorem clause25_interactionPicture_endpoint :
    (∀ ε : ℝ, ipPrintedCutoff ε = ip25CorrectedCutoff ε) ∧
    (∀ ε : ℝ, ipPrintedRange ε → 2 ≤ ip25CorrectedCutoff ε) ∧
    (∀ k : ℕ, 0 < ip25DyadicAccuracy k) ∧
    (∀ k : ℕ, ip25DyadicAccuracy k ≤ 1) ∧
    (∀ (M k : ℕ) (v : Fin k → Fin M), (ipSortedIndexList M k v).length = k) ∧
    (∀ k : ℕ, k ≤ ip25SortingComparators k) ∧
    (∀ (M k : ℕ) (i j : Fin k) (v : Fin k → Fin M),
      ip25IndexSwap i j (ip25IndexSwap i j v) = v) ∧
    (∀ (M k : ℕ) (i j : Fin k) (v : Fin k → Fin M),
      (ip25IndexCompare i j v) i ≤ (ip25IndexCompare i j v) j) ∧
    (∀ (M k : ℕ) (i j : Fin k) (v : Fin k → Fin M),
      ip25IndexCompare i j (ip25IndexCompare i j v) = ip25IndexCompare i j v) ∧
    (∀ (M k : ℕ) (i j : Fin k) (v : Fin k → Fin M),
      ∃ σ : Fin k → Fin k, (∀ p, σ (σ p) = p) ∧ ip25IndexCompare i j v = fun p => v (σ p)) ∧
    (∀ (M k : ℕ) (v : Fin k → Fin M), ip25IndexReverse (ip25IndexReverse v) = v) ∧
    (∀ (M k : ℕ) (v : Fin k → Fin M),
      (ip25SortSchedule v).length ≤ ip25SortingComparators k) ∧
    (∀ (M k : ℕ) (v : Fin k → Fin M),
      (ip25SortRun (fun a b => decide (a ≤ b)) 0 (List.ofFn v)).1 = ipSortedIndexList M k v) ∧
    (∀ (M k : ℕ) (v : Fin k → Fin M),
      (ip25SortSchedule v).length ≤ k * Nat.clog 2 k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ε
    exact ip25_printed_cutoff_correction ε
  · intro ε h
    exact ip25_corrected_cutoff_ge_two ε h
  · intro k
    exact ip25_dyadic_accuracy_pos k
  · intro k
    exact ip25_dyadic_accuracy_le_one k
  · intro M k v
    exact ip25_sorted_index_length M k v
  · intro k
    exact ip25_sorting_budget_ge_length k
  · intro M k i j v
    exact ip25_index_swap_involutive i j v
  · intro M k i j v
    exact ip25_index_compare_order i j v
  · intro M k i j v
    exact ip25_index_compare_idem i j v
  · intro M k i j v
    exact ip25_index_compare_is_permutation i j v
  · intro M k v
    exact ip25_index_reverse_involutive v
  · intro M k v
    exact ip25_sort_schedule_count_le_budget v
  · intro M k v
    exact ip25_sort_run_eq_sorted_index_list v
  · intro M k v
    exact ip25_sort_schedule_count_le_clog v

/-- Collects segment resource counts, error and failure budgets, the eventual Dyson query-rate
bound, auxiliary bit bounds, and exact logarithmic rate and cutoff identities. -/
theorem clause26_endpoint :
    (∀ p : EffectiveSegmentParameters, 2 * ipSegmentCopies p = ip26SegmentGateCount p) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQueries p = ipSegmentCount p * ipSegmentCopies p) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + Nat.clog 2 (ipSegmentCount p)) ∧
    (∀ (L : ℕ) (ε : ℝ), 0 < L → (L : ℝ) * ipSegmentBudget L ε = ε) ∧
    (∀ (L : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 →
      ipTotalFailure L δ ≤ (L : ℝ) * ipPerSegmentFailure δ) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQueries p = ipSegmentCount p * ip26SegmentQueryRate p.precision) ∧
    (∀ p : EffectiveSegmentParameters, ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
      (ipSegmentCount p * computedDysonCutoff (k + 8)) * Nat.clog 2 (k + 2)
        ≤ C * (k + 2) * ipSegmentCount p) ∧
    (∀ L : ℕ, ip26AuxBitRate L = Nat.clog 2 L ∧ L ≤ 2 ^ (ip26AuxBitRate L) ∧
      ip26AuxBitRate L ≤ Nat.log 2 L + 1) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p) + ip26AuxBitRate (ipSegmentCount p)) ∧
    (∀ ε : ℝ, ip25CorrectedCutoff ε = Nat.ceil (ip26NonBinaryRate ε)) ∧
    (∀ ε : ℝ, 0 < ip26NonBinaryRate ε →
      ip26NonBinaryRate ε ≤ (ip25CorrectedCutoff ε : ℝ) ∧
        (ip25CorrectedCutoff ε : ℝ) < ip26NonBinaryRate ε + 1) ∧
    (∀ ε : ℝ, ipPrintedRange ε → 0 < ip26NonBinaryRate ε) ∧
    (∀ ε : ℝ, ipPrintedRange ε → 1 < ip26NonBinaryRate ε) ∧
    (∀ ε : ℝ, 0 < ε →
      ip26NonBinaryRate ε
        = 2 * (Real.log (1 / ε) + Real.log 2) / Real.log (Real.log (1 / ε) + Real.log 2)) ∧
    (∀ k : ℕ, ip26NonBinaryRate (ip25DyadicAccuracy k)
      = 2 * ((k + 1) * Real.log 2) / Real.log ((k + 1) * Real.log 2)) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQueries p = ipSegmentCount p * ip26SegmentQueryRate p.precision) ∧
    (∀ p : EffectiveSegmentParameters,
      ipTotalQubits p = ipSegmentWidth (effectiveLongLocal p)
        + ip26AuxBitRate (ipSegmentCount p)) ∧
    (∀ p : EffectiveSegmentParameters,
      ip26NonBinaryRate (ip25DyadicAccuracy p.precision)
        = 2 * ((p.precision + 1) * Real.log 2) / Real.log ((p.precision + 1) * Real.log 2)) ∧
    (∀ p : EffectiveSegmentParameters,
      ip25CorrectedCutoff (ip25DyadicAccuracy p.precision)
        = Nat.ceil (ip26NonBinaryRate (ip25DyadicAccuracy p.precision))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact ip26_segment_gate_count p
  · intro p
    exact ip26_total_queries_exact p
  · intro p
    exact ip26_total_qubits_exact p
  · intro L ε hL
    exact ip26_segment_budget_sum L ε hL
  · intro L δ hδ hδ1
    exact ip26_total_failure_le L δ hδ hδ1
  · intro p
    exact ip26_actual_query_count p
  · intro p
    exact ip26_query_rate_logloglog p
  · intro L
    exact ip26_aux_bit_rate L
  · intro p
    exact ip26_actual_aux_bits p
  · intro ε
    exact ip26_rate_is_cutoff ε
  · intro ε h
    exact ip26_rate_ceiling_bounds ε h
  · intro ε h
    exact ip26_rate_pos ε h
  · intro ε h
    exact ip26_rate_gt_one ε h
  · intro ε hε
    exact ip26_rate_in_log_terms ε hε
  · intro k
    exact ip26_rate_dyadic k
  · intro p
    exact ip26_actual_query_count p
  · intro p
    exact ip26_actual_aux_bits p
  · intro p
    exact ip26_rate_dyadic p.precision
  · intro p
    exact ip26_rate_is_cutoff _

/-- Collects the sparse and diagonal-augmented programs' step counts, widths, and query counts. -/
theorem clause27_endpoint :
    (∀ p : EffectiveSparseParameters,
      (ipSparseProgram p).steps.length = ip27SparseStepCount p) ∧
    (∀ p : EffectiveSparseParameters,
      (ipSparseProgram p).width = ip27SparseWidth p) ∧
    (∀ p : EffectiveSparseParameters, ipSparseQueries p = 2) ∧
    (∀ p : EffectiveSparseParameters, ip27ProgramQueries (ipSparseProgram p) = ipSparseQueries p) ∧
    (∀ p : EffectiveSparseParameters,
      (ip27DiagonalProgram p).steps.length = ip27DiagonalTotalGates p) ∧
    (∀ p : EffectiveSparseParameters,
      ip27ProgramQueries (ip27DiagonalProgram p) = ip27ProgramQueries (ipSparseProgram p) ∧
        ip27DiagonalQueries p = 0) ∧
    (∀ p : EffectiveSparseParameters,
      (ip27DiagonalProgram p).width = (ipSparseProgram p).width) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact ip27_sparse_step_count p
  · intro p
    exact ip27_sparse_width p
  · intro p
    exact ip27_sparse_queries p
  · intro p
    exact ip27_program_query_count p
  · intro p
    exact ip27_diagonal_step_count p
  · intro p
    exact ip27_diagonal_queries p
  · intro p
    exact ip27_diagonal_width p

/-- Twice 2ⁿ equals 2ⁿ⁺¹. -/
private theorem ip25_two_pow' (n : ℕ) : 2 * 2 ^ n = 2 ^ (n + 1) := by
  rw [Nat.mul_comm, Nat.pow_succ]

/-- For m > 0, 2ᵐ equals twice 2ᵐ⁻¹. -/
private theorem ip25_two_pow (m : ℕ) (hm : 0 < m) : 2 ^ m = 2 ^ (m - 1) * 2 := by
  calc 2 ^ m = 2 ^ ((m - 1) + 1) := by
          congr 1
          omega
    _ = 2 ^ (m - 1) * 2 := Nat.pow_succ _ _

/-- The bitonic merge schedule on 2ˢ positions has s · 2ˢ⁻¹ gates. -/
theorem ip25BitonicMerge_length : ∀ (s : ℕ) (up : Bool),
    (ip25BitonicMerge s up).length = s * 2 ^ (s - 1) := by
  intro s
  induction s with
  | zero =>
      intro up
      simp [ip25BitonicMerge]
  | succ k ih =>
      intro up
      rw [ip25BitonicMerge]
      simp only [List.length_append, List.length_map, List.length_range]
      rw [ih up]
      by_cases hk : k = 0
      · subst hk
        simp
      · have h2 := ip25_two_pow k (by omega)
        have h3 : 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
          rw [← Nat.mul_two, h2]
        calc 2 ^ k + (k * 2 ^ (k - 1) + k * 2 ^ (k - 1))
            = 2 ^ k + k * (2 ^ (k - 1) + 2 ^ (k - 1)) := by ring
          _ = 2 ^ k + k * 2 ^ k := by rw [h3]
          _ = (k + 1) * 2 ^ k := by ring

/-- For m ≥ 2, the directed bitonic sort schedule on 2ᵐ positions has 2ᵐ⁻²m(m+1) gates. -/
theorem ip25BitonicSortDir_length : ∀ (m : ℕ) (up : Bool), 2 ≤ m →
    (ip25BitonicSortDir m up).length = 2 ^ (m - 2) * m * (m + 1) := by
  intro m
  induction m with
  | zero =>
      intro up hm
      omega
  | succ m ih =>
      intro up hm
      rw [ip25BitonicSortDir]
      simp only [List.length_append, List.length_map]
      rw [ip25BitonicMerge_length]
      by_cases hm2 : 2 ≤ m
      · rw [ih (!up) hm2, ih up hm2]
        have hP : 2 ^ (m - 1) = 2 ^ (m - 2) * 2 := by
          calc 2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by
                  congr 1
                  omega
            _ = 2 ^ (m - 2) * 2 := Nat.pow_succ _ _
        have hQ : 2 ^ m = 2 ^ (m - 2) * 4 := by
          calc 2 ^ m = 2 ^ ((m - 2) + 2) := by
                  congr 1
                  omega
            _ = 2 ^ (m - 2) * 2 ^ 2 := Nat.pow_add _ _ _
            _ = 2 ^ (m - 2) * 4 := by norm_num
        rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega, hP, hQ]
        ring
      · have hm1 : m = 1 := by omega
        subst hm1
        simp only [ip25BitonicSortDir, ip25BitonicMerge, List.length_append,
          List.length_map, List.length_range]
        norm_num

/-- For m ≥ 2, the bitonic sort schedule on 2ᵐ positions has 2ᵐ⁻²m(m+1) gates. -/
theorem ip25BitonicSort_length : ∀ m : ℕ, 2 ≤ m →
    (ip25BitonicSort m).length = 2 ^ (m - 2) * m * (m + 1) := by
  intro m hm
  exact ip25BitonicSortDir_length m true hm

/-- Both endpoints of every gate in a bitonic merge schedule lie below 2ˢ. -/
theorem ip25BitonicMerge_positions_lt : ∀ (s : ℕ) (up : Bool),
    ∀ g ∈ ip25BitonicMerge s up, g.i < 2 ^ s ∧ g.j < 2 ^ s := by
  intro s
  induction s with
  | zero =>
      intro up g hg
      simp [ip25BitonicMerge] at hg
  | succ k ih =>
      intro up g hg
      rw [ip25BitonicMerge] at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨i, hi, hfi⟩ := List.mem_map.mp hg
        subst hfi
        have hi' : i < 2 ^ k := List.mem_range.mp hi
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
        constructor
        · show i < 2 ^ (k + 1)
          omega
        · show i + 2 ^ k < 2 ^ (k + 1)
          omega
      · rcases List.mem_append.mp hg with hg | hg
        · have h := ih up g hg
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
          constructor
          · show g.i < 2 ^ (k + 1)
            omega
          · show g.j < 2 ^ (k + 1)
            omega
        · obtain ⟨g', hg', hfg⟩ := List.mem_map.mp hg
          subst hfg
          have h := ih up g' hg'
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
          constructor
          · show g'.i + 2 ^ k < 2 ^ (k + 1)
            omega
          · show g'.j + 2 ^ k < 2 ^ (k + 1)
            omega

/-- Both endpoints of every gate in a directed bitonic sort schedule lie below 2ᵐ. -/
theorem ip25BitonicSortDir_positions_lt : ∀ (m : ℕ) (up : Bool) (g : Ip25BitonicGate),
    g ∈ ip25BitonicSortDir m up → g.i < 2 ^ m ∧ g.j < 2 ^ m := by
  intro m
  induction m with
  | zero =>
      intro up g hg
      simp [ip25BitonicSortDir] at hg
  | succ k ih =>
      intro up g hg
      rw [ip25BitonicSortDir] at hg
      rcases List.mem_append.mp hg with hg | hg
      · have h := ih (!up) g hg
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
        constructor
        · show g.i < 2 ^ (k + 1)
          omega
        · show g.j < 2 ^ (k + 1)
          omega
      · rcases List.mem_append.mp hg with hg | hg
        · obtain ⟨g', hg', hfg⟩ := List.mem_map.mp hg
          subst hfg
          have h := ih up g' hg'
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
          constructor
          · show g'.i + 2 ^ k < 2 ^ (k + 1)
            omega
          · show g'.j + 2 ^ k < 2 ^ (k + 1)
            omega
        · have h := ip25BitonicMerge_positions_lt (k + 1) up g hg
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := (ip25_two_pow' k).symm
          constructor <;> omega

/-- Both endpoints of every gate in a bitonic sort schedule lie below 2ᵐ. -/
theorem ip25BitonicSort_positions_lt : ∀ (m : ℕ) (g : Ip25BitonicGate),
    g ∈ ip25BitonicSort m → g.i < 2 ^ m ∧ g.j < 2 ^ m := by
  intro m g hg
  exact ip25BitonicSortDir_positions_lt m true g hg

/-- Every bitonic merge gate has its first endpoint strictly below its second. -/
theorem ip25BitonicMerge_gate_ordered : ∀ (s : ℕ) (up : Bool),
    ∀ g ∈ ip25BitonicMerge s up, g.i < g.j := by
  intro s
  induction s with
  | zero =>
      intro up g hg
      simp [ip25BitonicMerge] at hg
  | succ k ih =>
      intro up g hg
      rw [ip25BitonicMerge] at hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨i, hi, hfi⟩ := List.mem_map.mp hg
        subst hfi
        have hp : 0 < 2 ^ k := by positivity
        show i < i + 2 ^ k
        omega
      · rcases List.mem_append.mp hg with hg | hg
        · exact ih up g hg
        · obtain ⟨g', hg', hfg⟩ := List.mem_map.mp hg
          subst hfg
          have h := ih up g' hg'
          show g'.i + 2 ^ k < g'.j + 2 ^ k
          omega

/-- Every directed bitonic sort gate has its first endpoint strictly below its second. -/
theorem ip25BitonicSortDir_gate_ordered : ∀ (m : ℕ) (up : Bool) (g : Ip25BitonicGate),
    g ∈ ip25BitonicSortDir m up → g.i < g.j := by
  intro m
  induction m with
  | zero =>
      intro up g hg
      simp [ip25BitonicSortDir] at hg
  | succ k ih =>
      intro up g hg
      rw [ip25BitonicSortDir] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ih (!up) g hg
      · rcases List.mem_append.mp hg with hg | hg
        · obtain ⟨g', hg', hfg⟩ := List.mem_map.mp hg
          subst hfg
          have h := ih up g' hg'
          show g'.i + 2 ^ k < g'.j + 2 ^ k
          omega
        · exact ip25BitonicMerge_gate_ordered (k + 1) up g hg

/-- Every bitonic sort gate has its first endpoint strictly below its second. -/
theorem ip25BitonicSort_gate_ordered : ∀ (m : ℕ) (g : Ip25BitonicGate),
    g ∈ ip25BitonicSort m → g.i < g.j := by
  intro m g hg
  exact ip25BitonicSortDir_gate_ordered m true g hg

/-- Applies an ascending or descending compare operation at a bitonic gate's bounded endpoints
according to the gate direction. -/
def ip25BitonicComparator {M m : ℕ} (g : Ip25BitonicGate)
    (hg : g.i < 2 ^ m ∧ g.j < 2 ^ m) (v : Fin (2 ^ m) → Fin M) :
    Fin (2 ^ m) → Fin M :=
  if g.up then ip25IndexCompare ⟨g.i, hg.1⟩ ⟨g.j, hg.2⟩ v
  else ip25IndexCompare ⟨g.j, hg.2⟩ ⟨g.i, hg.1⟩ v

/-- An ascending bitonic comparator orders the first endpoint's value below or equal to the
second endpoint's value. -/
theorem ip25BitonicComparator_ascending {M m : ℕ} (g : Ip25BitonicGate)
    (hg : g.i < 2 ^ m ∧ g.j < 2 ^ m) (v : Fin (2 ^ m) → Fin M) (hup : g.up) :
    (ip25BitonicComparator g hg v) ⟨g.i, hg.1⟩ ≤ (ip25BitonicComparator g hg v) ⟨g.j, hg.2⟩ := by
  simp [ip25BitonicComparator, hup]
  exact ip25_index_compare_order _ _ _

/-- A descending bitonic comparator orders the second endpoint's value below or equal to the
first endpoint's value. -/
theorem ip25BitonicComparator_descending {M m : ℕ} (g : Ip25BitonicGate)
    (hg : g.i < 2 ^ m ∧ g.j < 2 ^ m) (v : Fin (2 ^ m) → Fin M) (hup : ¬ g.up) :
    (ip25BitonicComparator g hg v) ⟨g.j, hg.2⟩ ≤ (ip25BitonicComparator g hg v) ⟨g.i, hg.1⟩ := by
  simp [ip25BitonicComparator, hup]
  exact ip25_index_compare_order _ _ _

/-- For each input vector, a bitonic comparator acts by an involutive permutation of positions. -/
theorem ip25BitonicComparator_is_permutation {M m : ℕ} (g : Ip25BitonicGate)
    (hg : g.i < 2 ^ m ∧ g.j < 2 ^ m) (v : Fin (2 ^ m) → Fin M) :
    ∃ σ : Fin (2 ^ m) → Fin (2 ^ m), (∀ p, σ (σ p) = p) ∧
      ip25BitonicComparator g hg v = fun p => v (σ p) := by
  by_cases hup : g.up
  · rw [show ip25BitonicComparator g hg v
        = ip25IndexCompare ⟨g.i, hg.1⟩ ⟨g.j, hg.2⟩ v by simp [ip25BitonicComparator, hup]]
    exact ip25_index_compare_is_permutation _ _ _
  · rw [show ip25BitonicComparator g hg v
        = ip25IndexCompare ⟨g.j, hg.2⟩ ⟨g.i, hg.1⟩ v by simp [ip25BitonicComparator, hup]]
    exact ip25_index_compare_is_permutation _ _ _

/-- For m ≥ 5, the bitonic sort schedule on 2ᵐ positions exceeds `ip25SortingComparators (2 ^
m)`. -/
theorem ip25BitonicSort_exceeds_budget (m : ℕ) (hm : 5 ≤ m) :
    (ip25BitonicSort m).length > ip25SortingComparators (2 ^ m) := by
  have hlen : (ip25BitonicSort m).length = 2 ^ (m - 2) * m * (m + 1) :=
    ip25BitonicSort_length m (by omega)
  have hlog : (2 ^ m).log2 = m := Nat.log2_two_pow
  have h2 : 2 ^ m = 2 ^ (m - 2) * 4 := by
    calc 2 ^ m = 2 ^ ((m - 2) + 2) := by
            congr 1
            omega
      _ = 2 ^ (m - 2) * 2 ^ 2 := Nat.pow_add _ _ _
      _ = 2 ^ (m - 2) * 4 := by norm_num
  rw [hlen]
  simp only [ip25SortingComparators, Nat.log2_two_pow]
  calc 2 ^ (m - 2) * m * (m + 1)
      = 2 ^ (m - 2) * (m * (m + 1)) := by ring
    _ > 2 ^ (m - 2) * (4 * (m + 1)) := by
        have hpos : 0 < 2 ^ (m - 2) := by positivity
        have hlt : 4 * (m + 1) < m * (m + 1) := by
          calc 4 * (m + 1) = (m + 1) * 4 := Nat.mul_comm _ _
            _ < (m + 1) * m :=
              Nat.mul_lt_mul_of_pos_left (by omega : 4 < m) (by omega : 0 < m + 1)
            _ = m * (m + 1) := Nat.mul_comm _ _
        simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using!
          (Nat.mul_lt_mul_right hpos).mpr hlt
    _ = 2 ^ m * (m + 1) := by rw [h2]; ring

/-- Every gate of the bitonic sort schedule has strictly ordered endpoints within the input
range. -/
theorem ip25_bitonic_network_endpoint : ∀ (m : ℕ) (g : Ip25BitonicGate),
    g ∈ ip25BitonicSort m →
    g.i < g.j ∧ g.i < 2 ^ m ∧ g.j < 2 ^ m := by
  intro m g hg
  have hpos := ip25BitonicSort_positions_lt m g hg
  have hord := ip25BitonicSort_gate_ordered m g hg
  exact ⟨hord, hpos.1, hpos.2⟩

/-- The proposition that neither endpoint of g' is an endpoint of g. -/
def Ip25GatesAvoid (g g' : Ip25BitonicGate) : Prop :=
  g'.i ≠ g.i ∧ g'.i ≠ g.j ∧ g'.j ≠ g.i ∧ g'.j ≠ g.j

/-- If `Ip25GatesAvoid g g'` holds, both endpoints of g' differ from the first endpoint of g. -/
theorem ip25GatesAvoid_lower {g g' : Ip25BitonicGate} (h : Ip25GatesAvoid g g') :
    g'.i ≠ g.i ∧ g'.j ≠ g.i := ⟨h.1, h.2.2.1⟩

/-- If `Ip25GatesAvoid g g'` holds, both endpoints of g' differ from the second endpoint of g. -/
theorem ip25GatesAvoid_upper {g g' : Ip25BitonicGate} (h : Ip25GatesAvoid g g') :
    g'.i ≠ g.j ∧ g'.j ≠ g.j := ⟨h.2.1, h.2.2.2⟩

/-- A Boolean comparator gate preserves any position distinct from both endpoints. -/
theorem ip25BoolGate_apply_of_ne (g : Ip25BitonicGate) (v : ℕ → Bool) (j : ℕ)
    (h1 : g.i ≠ j) (h2 : g.j ≠ j) : ip25BoolGate g v j = v j := by
  simp [ip25BoolGate, Ne.symm h1, Ne.symm h2]

/-- A Boolean gate sequence preserves every position that is untouched by all its gates. -/
theorem ip25BoolRun_of_not_mem : ∀ (gs : List Ip25BitonicGate) (v : ℕ → Bool) (j : ℕ),
    (∀ g ∈ gs, g.i ≠ j ∧ g.j ≠ j) → ip25BoolRun gs v j = v j := by
  intro gs
  induction gs with
  | nil =>
      intro v j _
      rfl
  | cons g rest ih =>
      intro v j hj
      have hrw : ip25BoolRun (g :: rest) v = ip25BoolRun rest (ip25BoolGate g v) := rfl
      rw [hrw]
      have hrest : ∀ g' ∈ rest, g'.i ≠ j ∧ g'.j ≠ j := by
        intro g' hg'
        exact hj g' (List.mem_cons_of_mem g hg')
      rw [ih (ip25BoolGate g v) j hrest]
      exact ip25BoolGate_apply_of_ne g v j (hj g (List.mem_cons_self)).1
        (hj g (List.mem_cons_self)).2

/-- Two Boolean inputs agreeing at a position untouched by every gate yield equal outputs at
that position. -/
theorem ip25BoolRun_congr : ∀ (gs : List Ip25BitonicGate) (v w : ℕ → Bool) (j : ℕ),
    (∀ g ∈ gs, g.i ≠ j ∧ g.j ≠ j) → v j = w j →
    ip25BoolRun gs v j = ip25BoolRun gs w j := by
  intro gs
  induction gs with
  | nil =>
      intro v w j _ heq
      exact heq
  | cons g rest ih =>
      intro v w j hj heq
      have hrw : ip25BoolRun (g :: rest) v = ip25BoolRun rest (ip25BoolGate g v) := rfl
      have hrw' : ip25BoolRun (g :: rest) w = ip25BoolRun rest (ip25BoolGate g w) := rfl
      rw [hrw, hrw']
      have hrest : ∀ g' ∈ rest, g'.i ≠ j ∧ g'.j ≠ j := by
        intro g' hg'
        exact hj g' (List.mem_cons_of_mem g hg')
      rw [ih (ip25BoolGate g v) (ip25BoolGate g w) j hrest]
      have hg : g.i ≠ j ∧ g.j ≠ j := hj g (List.mem_cons_self)
      have h1 : ip25BoolGate g v j = v j := ip25BoolGate_apply_of_ne g v j hg.1 hg.2
      have h2 : ip25BoolGate g w j = w j := ip25BoolGate_apply_of_ne g w j hg.1 hg.2
      rw [h1, h2]
      exact heq

/-- If all surrounding gates avoid a given gate, its two final endpoint values are the original
Boolean minimum and maximum in the order selected by its direction. -/
theorem ip25BoolRun_get : ∀ (pre post : List Ip25BitonicGate) (v : ℕ → Bool)
    (g : Ip25BitonicGate),
    g.i ≠ g.j →
    (∀ g' ∈ pre, Ip25GatesAvoid g g') →
    (∀ g' ∈ post, Ip25GatesAvoid g g') →
    (ip25BoolRun (pre ++ g :: post) v) g.i =
      (if g.up then v g.i && v g.j else v g.i || v g.j) ∧
    (ip25BoolRun (pre ++ g :: post) v) g.j =
      (if g.up then v g.i || v g.j else v g.i && v g.j) := by
  intro pre
  induction pre with
  | nil =>
      intro post v g hgij hpre hpost
      simp only [List.nil_append]
      have e1 : ip25BoolRun post (ip25BoolGate g v) g.i = ip25BoolGate g v g.i :=
        ip25BoolRun_of_not_mem post _ g.i (fun g' hg' => ip25GatesAvoid_lower (hpost g' hg'))
      have e2 : ip25BoolRun post (ip25BoolGate g v) g.j = ip25BoolGate g v g.j :=
        ip25BoolRun_of_not_mem post _ g.j (fun g' hg' => ip25GatesAvoid_upper (hpost g' hg'))
      have hrw : ip25BoolRun (g :: post) v = ip25BoolRun post (ip25BoolGate g v) := rfl
      rw [hrw, e1, e2]
      simp [ip25BoolGate, Ne.symm hgij, Bool.or_comm, Bool.and_comm]
  | cons g' pre' ih =>
      intro post v g hgij hpre hpost
      have hpre' : ∀ g'' ∈ pre', Ip25GatesAvoid g g'' := by
        intro g'' hg''
        exact hpre g'' (List.mem_cons_of_mem g' hg'')
      have hg' : Ip25GatesAvoid g g' := hpre g' (List.mem_cons_self)
      have hrw : ip25BoolRun ((g' :: pre') ++ g :: post) v
          = ip25BoolRun (pre' ++ g :: post) (ip25BoolGate g' v) := rfl
      have e1 : ip25BoolGate g' v g.i = v g.i :=
        ip25BoolGate_apply_of_ne g' v g.i (ip25GatesAvoid_lower hg').1 (ip25GatesAvoid_lower hg').2
      have e2 : ip25BoolGate g' v g.j = v g.j :=
        ip25BoolGate_apply_of_ne g' v g.j (ip25GatesAvoid_upper hg').1 (ip25GatesAvoid_upper hg').2
      rw [hrw]
      obtain ⟨h1, h2⟩ := ih post (ip25BoolGate g' v) g hgij hpre' hpost
      rw [h1, h2, e1, e2]
      constructor <;> rfl

/-- Distinct gates in the Boolean half-cleaner schedule have disjoint endpoint sets. -/
theorem ip25BoolHalfCleanerGates_disjoint (h : ℕ) :
    ∀ g ∈ ip25BoolHalfCleanerGates h, ∀ g' ∈ ip25BoolHalfCleanerGates h, g' ≠ g →
      g'.i ≠ g.i ∧ g'.i ≠ g.j ∧ g'.j ≠ g.i ∧ g'.j ≠ g.j := by
  intro g hg g' hg' hne
  obtain ⟨j, hj, hgj⟩ := List.mem_map.mp hg
  obtain ⟨j', hj', hgj'⟩ := List.mem_map.mp hg'
  have hgi : g.i = j := (congrArg (fun s : Ip25BitonicGate => s.i) hgj).symm
  have hgjE : g.j = j + h := (congrArg (fun s : Ip25BitonicGate => s.j) hgj).symm
  have hgi' : g'.i = j' := (congrArg (fun s : Ip25BitonicGate => s.i) hgj').symm
  have hgj'E : g'.j = j' + h := (congrArg (fun s : Ip25BitonicGate => s.j) hgj').symm
  have hne' : (⟨j', j' + h, true⟩ : Ip25BitonicGate) ≠ ⟨j, j + h, true⟩ := by
    intro hcon
    apply hne
    calc g' = ⟨j', j' + h, true⟩ := hgj'.symm
      _ = ⟨j, j + h, true⟩ := hcon
      _ = g := hgj
  have hjj : j' ≠ j := by
    intro hcon
    apply hne'
    rw [hcon]
  have hjlt : j < h := List.mem_range.mp hj
  have hj'lt : j' < h := List.mem_range.mp hj'
  rw [hgi, hgjE, hgi', hgj'E]
  constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · omega

/-- The ascending compare operation on two-entry vectors with values in `Fin 2` is not
injective. -/
theorem ip25_index_compare_not_injective :
    ¬ Function.Injective (ip25IndexCompare (M := 2) (0 : Fin 2) 1) := by
  intro h
  let v : Fin 2 → Fin 2 := fun i => i
  let w : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
  have heq : ip25IndexCompare (0 : Fin 2) 1 v = ip25IndexCompare (0 : Fin 2) 1 w := by
    funext i
    fin_cases i <;> norm_num [v, w, ip25IndexCompare, ip25IndexSwap, ip25IndexTransposition]
  have hzero := congrFun (h heq) (0 : Fin 2)
  norm_num [v, w] at hzero

end Qatlib.Concepts.AmpTransform.LegendreWindow
