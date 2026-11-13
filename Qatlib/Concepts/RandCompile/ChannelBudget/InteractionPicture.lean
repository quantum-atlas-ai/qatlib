/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPictureDefs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Interaction picture cutoffs and program resources

This module proves cutoff, grid, and resource identities for finite interaction picture
simulation in the setting of [LowWiebe2018]. It relates the printed logarithmic cutoff to the
computed Dyson order and splits repeated grid-index sums into injective and collision
contributions.

The program results identify segment query and phase lists, sparse-program width and step count,
accumulated failure bounds, and dyadic-time gate-cost estimates. The sorted-word lemmas make the
multiplication order explicit.

## Main statements

* `ipRepeatedCube_split`: separate injective and colliding grid-index contributions.
* `ipSegmentProgram_queries`: identify the segment program query count.
* `ipGateRateTotal`: sum a logarithmic per-time cost bound over dyadic evolution times.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The printed interaction picture cutoff equals the natural ceiling of `2 log(2 / ε) /
log(log(2 / ε))`. -/
theorem ipPrintedCutoff_simplified (ε : ℝ) :
    ipPrintedCutoff ε = Nat.ceil (2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε))) := by
  unfold ipPrintedCutoff
  congr 1
  ring

/-- In the printed tolerance range, `log(2 / ε)` is greater than one. -/
theorem ipPrintedRange_log_pos (ε : ℝ) (h : ipPrintedRange ε) :
    1 < Real.log (2 / ε) := by
  have hε0 : 0 < ε := h.1
  have hε1 : ε ≤ 1 / 2 - 1 / Real.exp 1 := h.2
  have hexp : Real.exp 1 < 6 := by
    have h := Real.exp_one_lt_d9
    linarith
  have hmul : ε * Real.exp 1 < 2 := by
    have hid : (1 / 2 - 1 / Real.exp 1) * Real.exp 1 = Real.exp 1 / 2 - 1 := by
      field_simp
    have h1 : ε * Real.exp 1 ≤ (1 / 2 - 1 / Real.exp 1) * Real.exp 1 :=
      mul_le_mul_of_nonneg_right hε1 (Real.exp_pos 1).le
    rw [hid] at h1
    linarith
  have hmul' : Real.exp 1 * ε < 2 := by linarith
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact (lt_div_iff₀ hε0).mpr hmul'

/-- In the printed tolerance range, `log(log(2 / ε))` is positive. -/
theorem ipPrintedRange_loglog_pos (ε : ℝ) (h : ipPrintedRange ε) :
    0 < Real.log (Real.log (2 / ε)) := by
  exact Real.log_pos (ipPrintedRange_log_pos ε h)

/-- In the printed tolerance range, the printed cutoff is at least two. -/
theorem ipPrintedCutoff_ge_two (ε : ℝ) (h : ipPrintedRange ε) :
    2 ≤ ipPrintedCutoff ε := by
  have hL : 1 < Real.log (2 / ε) := ipPrintedRange_log_pos ε h
  have hLpos : 0 < Real.log (2 / ε) := lt_trans zero_lt_one hL
  have hD : 0 < Real.log (Real.log (2 / ε)) := ipPrintedRange_loglog_pos ε h
  have hratio : 1 < 2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε)) := by
    apply (lt_div_iff₀ hD).mpr
    have hloglt : Real.log (Real.log (2 / ε)) < Real.log (2 / ε) := by
      have hh := Real.log_lt_sub_one_of_pos hLpos (by
        intro hc
        linarith)
      linarith
    linarith
  rw [ipPrintedCutoff_simplified]
  have hlt' : ((1 : ℕ) : ℝ) < 2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε)) := by
    linarith
  have hlt : (1 : ℕ) < Nat.ceil (2 * Real.log (2 / ε) / Real.log (Real.log (2 / ε))) :=
    Nat.lt_ceil.mpr hlt'
  omega

/-- The closed-form truncation order equals `computedDysonCutoff k`. -/
theorem ipClosedFormK_eq (k : ℕ) : ipClosedFormK k = computedDysonCutoff k := rfl

/-- The closed-form grid meets `ipSourceGridCondition` whenever the stated real grid-size
expression is nonnegative. -/
theorem ipSourceGridCondition_holds (t Λ χ : ℝ) (k : ℕ)
    (h : 0 ≤ 16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k) :
    ipSourceGridCondition t Λ χ k := by
  have hM : ipClosedFormM t Λ χ k =
      max (max 1 ((ipClosedFormK k) ^ 2))
        (Nat.ceil (16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k)) := by
    unfold ipClosedFormM computedDysonGridSize ipClosedFormK
    rfl
  constructor
  · have hle : (Nat.ceil (16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k) : ℕ)
        ≤ ipClosedFormM t Λ χ k := by
      rw [hM]
      exact le_max_right _ _
    have hceil := Nat.le_ceil (16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k)
    have hle' : (Nat.ceil (16 * t ^ 2 * (χ + Λ ^ 2) * (2 : ℝ) ^ k) : ℝ)
        ≤ (ipClosedFormM t Λ χ k : ℝ) := by
      exact_mod_cast hle
    exact hceil.trans hle'
  · have hle : (ipClosedFormK k) ^ 2 ≤ ipClosedFormM t Λ χ k := by
      rw [hM]
      exact (le_max_right 1 _).trans (le_max_left _ _)
    exact hle

/-- The computed truncation cutoff satisfies `ipTruncationTail k x` for `0 ≤ x ≤ log 2`. -/
theorem ipTruncationTail_holds (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ Real.log 2) :
    ipTruncationTail k x := by
  unfold ipTruncationTail ipClosedFormK
  exact computedDysonCutoff_tail_and_rate.1 k x hx0 hx

/-- The repeated-index cube sum splits into the injective-index contribution and the collision
contribution. -/
theorem ipRepeatedCube_split {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) :
    ipRepeatedCube H t M k = ipInjectiveCube H t M k + ipCollisionCube H t M k := by
  unfold ipRepeatedCube ipInjectiveCube ipCollisionCube
  exact effectiveCubeRaw_partition H t M k

/-- For strictly increasing grid indices, the sorted Hamiltonian word is the product of the
sampled Hamiltonians in reverse index order. -/
theorem ipSortedWord_of_strict {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M k : ℕ) (v : Fin k → Fin M) (hv : StrictMono v) :
    ipSortedWord H t M k v =
      ((List.ofFn (fun i : Fin k => H (t * (v i).val / M))).reverse).prod := by
  unfold ipSortedWord effectiveSortedWord
  have hsort : (List.ofFn v).mergeSort (fun a b => a ≤ b) = List.ofFn v := by
    apply List.mergeSort_of_pairwise
    rw [List.pairwise_ofFn]
    intro i j hij
    simp only [decide_eq_true_eq]
    exact le_of_lt (hv hij)
  rw [hsort]
  have hmap : ((List.ofFn v).reverse).map (fun j => H (t * j.val / M))
      = (List.ofFn (fun i : Fin k => H (t * (v i).val / M))).reverse := by
    rw [List.map_reverse, List.map_ofFn]
    simp [Function.comp_def]
  rw [hmap]

/-- The second-order collision sum is the sum of squared Hamiltonian samples over the grid. -/
theorem ipCollisionCube_two {I : Type} [Fintype I] [DecidableEq I]
    (H : ℝ → Matrix I I ℂ) (t : ℝ) (M : ℕ) :
    ipCollisionCube H t M 2 = ∑ j : Fin M, H (t * j.val / M) * H (t * j.val / M) := by
  classical
  unfold ipCollisionCube effectiveCollisionRaw
  have key : ∀ (w : Fin 2 → Fin M), ¬ Function.Injective w → w 0 = w 1 := by
    intro w hw
    by_cases h : w 0 = w 1
    · exact h
    · exfalso
      apply hw
      intro a b hval
      fin_cases a <;> fin_cases b <;> simp_all [h]
  have hsplit : (∑ v : Fin 2 → Fin M,
      if Function.Injective v then 0 else effectiveSortedWord H t M 2 v)
      = ∑ v ∈ Finset.univ.filter (fun v : Fin 2 → Fin M => v 0 = v 1),
          effectiveSortedWord H t M 2 v := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : Function.Injective v
    · rw [if_pos h]
      have hne : ¬ (v 0 = v 1) := by
        intro hc
        have heq : (0 : Fin 2) = (1 : Fin 2) := h hc
        have hz : ¬ ((0 : Fin 2) = (1 : Fin 2)) := by decide
        exact hz heq
      simp only [if_neg hne]
    · have hne : v 0 = v 1 := key v h
      rw [if_neg h]
      simp only [hne, if_true]
  rw [hsplit]
  refine Finset.sum_bij (fun v _ => v 0) ?_ ?_ ?_ ?_
  · intro v _; simp
  · intro v hv v' hv' hv0
    have hne : v 0 = v 1 := by simpa using! hv
    have hne' : v' 0 = v' 1 := by simpa using! hv'
    have hvv : ∀ i : Fin 2, v i = v 0 := by
      intro i
      fin_cases i
      · rfl
      · exact hne.symm
    have hvv' : ∀ i : Fin 2, v' i = v' 0 := by
      intro i
      fin_cases i
      · rfl
      · exact hne'.symm
    have hv0' : v 0 = v' 0 := by simpa using! hv0
    funext i
    rw [hvv, hvv']
    exact hv0' ▸ rfl
  · intro j _
    refine ⟨fun _ => j, ?_, rfl⟩
    simp [Finset.mem_filter]
  · intro v hv
    have hne : v 0 = v 1 := by simpa using! hv
    have hof : List.ofFn v = [v 0, v 1] := by
      rw [List.ofFn_succ, List.ofFn_succ]
      simp
    have hms : [v 0, v 1].mergeSort (fun a b => a ≤ b) = [v 0, v 1] := by
      apply List.mergeSort_of_pairwise
      simp only [List.pairwise_cons]
      constructor
      · simp [hne]
      · simp [hne]
    simp only [effectiveSortedWord]
    rw [hof, hms]
    simp [hne]

/-- The sorted grid-index list is pairwise nondecreasing. -/
theorem ipSortedIndexList_pairwise (M k : ℕ) (v : Fin k → Fin M) :
    List.Pairwise (fun a b => decide (a ≤ b) = true) (ipSortedIndexList M k v) := by
  classical
  unfold ipSortedIndexList
  refine List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    ?_ ?_ (List.ofFn v)
  · intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  · intro a b
    simp only [decide_eq_true_eq, Bool.or_eq_true, decide_eq_false_iff_not]
    by_cases h : a ≤ b
    · exact Or.inl h
    · exact Or.inr (le_of_not_ge h)

/-- The sorted grid-index list is a permutation of the original index list. -/
theorem ipSortedIndexList_perm (M k : ℕ) (v : Fin k → Fin M) :
    List.Perm (ipSortedIndexList M k v) (List.ofFn v) := by
  classical
  unfold ipSortedIndexList
  exact List.mergeSort_perm (List.ofFn v) (fun a b => decide (a ≤ b))

/-- Sorting a strictly increasing index list leaves the list unchanged. -/
theorem ipSortedIndexList_of_strict (M k : ℕ) (v : Fin k → Fin M) (hv : StrictMono v) :
    ipSortedIndexList M k v = List.ofFn v := by
  classical
  unfold ipSortedIndexList
  apply List.mergeSort_of_pairwise
  rw [List.pairwise_ofFn]
  intro i j hij
  simp only [decide_eq_true_eq]
  exact le_of_lt (hv hij)

/-- Filtering queries from `K` query-phase pairs yields precisely the list of duplicated-wire
queries. -/
theorem ipSegmentQueryList_gen (p : EffectiveSegmentParameters) (K : ℕ) :
    List.filter (fun s => match s with | .query .. => true | _ => false)
      (List.flatMap
        (fun j => [ EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false
          , EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false ])
        (List.range K))
      = (List.range K).map
          (fun j => EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false) := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, ih]
    simp [List.range_succ]

/-- Filtering fixed and phase gates from `K` query-phase pairs yields precisely the list of
phase gates. -/
theorem ipSegmentGateList_gen (p : EffectiveSegmentParameters) (K : ℕ) :
    List.filter (fun s => match s with | .fixed .. | .phase .. => true | _ => false)
      (List.flatMap
        (fun j => [ EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false
          , EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false ])
        (List.range K))
      = (List.range K).map
          (fun j => EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false) := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.filter_append, ih]
    simp [List.range_succ]

/-- The query steps of the segment are exactly the duplicated-wire queries indexed by
`ipSegmentCopies p`. -/
theorem ipSegmentQueryList (p : EffectiveSegmentParameters) :
    List.filter (fun s => match s with | .query .. => true | _ => false) (ipSegmentSteps p)
      = (List.range (ipSegmentCopies p)).map
          (fun j => EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false) := by
  exact ipSegmentQueryList_gen p (ipSegmentCopies p)

/-- The fixed and phase steps of the segment are exactly the phase gates indexed by
`ipSegmentCopies p`. -/
theorem ipSegmentGateList (p : EffectiveSegmentParameters) :
    List.filter (fun s => match s with | .fixed .. | .phase .. => true | _ => false)
        (ipSegmentSteps p)
      = (List.range (ipSegmentCopies p)).map
          (fun j => EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false) := by
  exact ipSegmentGateList_gen p (ipSegmentCopies p)

/-- The segment program's query count equals `ipSegmentQueries p`. -/
theorem ipSegmentProgram_queries (p : EffectiveSegmentParameters) :
    effectiveQueries (ipSegmentProgram p) = ipSegmentQueries p := by
  have h := ipSegmentQueryList p
  simp only [ipSegmentProgram, EffectiveProgram.steps, effectiveQueries, ipSegmentQueries]
  calc (List.filter (fun s => match s with | .query .. => true | _ => false)
        (ipSegmentSteps p)).length
      = ((List.range (ipSegmentCopies p)).map
          (fun j => EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false)).length :=
        congrArg List.length h
    _ = ipSegmentCopies p := by simp
    _ = effectiveSegmentK p := rfl

/-- The segment program's fixed-and-phase gate count equals `ipSegmentCopies p`. -/
theorem ipSegmentProgram_gates (p : EffectiveSegmentParameters) :
    effectiveGates (ipSegmentProgram p) = ipSegmentCopies p := by
  have h := ipSegmentGateList p
  simp only [ipSegmentProgram, EffectiveProgram.steps, effectiveGates, ipSegmentCopies]
  calc (List.filter (fun s => match s with | .fixed .. | .phase .. => true | _ => false)
        (ipSegmentSteps p)).length
      = ((List.range (ipSegmentCopies p)).map
          (fun j => EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false)).length :=
        congrArg List.length h
    _ = ipSegmentCopies p := by simp
    _ = effectiveSegmentK p := rfl

/-- For every index below `effectiveSegmentK p`, the corresponding duplicated-wire query occurs
in the segment program. -/
theorem ipSegmentProgram_hasQuery (p : EffectiveSegmentParameters) (j : ℕ)
    (hj : j < effectiveSegmentK p) :
    EffectiveStep.query 0 (effectiveDuplicatedWires p j) [] false ∈ (ipSegmentProgram p).steps := by
  rw [ipSegmentProgram]
  apply List.mem_flatMap.mpr
  refine ⟨j, ?_, ?_⟩
  · simpa using! hj
  · simp

/-- For every index below `effectiveSegmentK p`, the corresponding phase gate occurs in the
segment program. -/
theorem ipSegmentProgram_hasPhase (p : EffectiveSegmentParameters) (j : ℕ)
    (hj : j < effectiveSegmentK p) :
    EffectiveStep.phase (p.ns + j * (p.na + p.nd) + p.nd) 1 1 false ∈ (ipSegmentProgram p).steps := by
  rw [ipSegmentProgram]
  apply List.mem_flatMap.mpr
  refine ⟨j, ?_, ?_⟩
  · simpa using! hj
  · simp

/-- For `0 ≤ x ≤ 1`, the failure expression `1 - x^L` is at most `L * (1 - x)`. -/
theorem ipGeomFailureBound (x : ℝ) (L : ℕ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    1 - x ^ L ≤ (L : ℝ) * (1 - x) := by
  induction L with
  | zero => simp
  | succ m ih =>
    have hstep : 1 - x ^ (m + 1) = (1 - x) + x * (1 - x ^ m) := by ring
    rw [hstep]
    have hxm : x * (1 - x ^ m) ≤ (m : ℝ) * (1 - x) := by
      have h := ih
      have hnonneg : 0 ≤ 1 - x ^ m := by
        by_cases hp : 0 ≤ m
        · exact sub_nonneg.mpr (pow_le_one₀ h0 h1)
        · omega
      calc x * (1 - x ^ m) ≤ x * ((m : ℝ) * (1 - x)) := by
            gcongr
        _ ≤ (m : ℝ) * (1 - x) := by
          have h1' : 0 ≤ 1 - x := sub_nonneg.mpr h1
          nlinarith [mul_nonneg h1' (Nat.cast_nonneg m)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith

/-- For `0 ≤ δ ≤ 1`, the total failure expression over `L` segments is at most `L` times the
per-segment failure expression. -/
theorem ipTotalFailure_le (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ipTotalFailure L δ ≤ (L : ℝ) * ipPerSegmentFailure δ := by
  unfold ipTotalFailure ipPerSegmentFailure
  have h := ipGeomFailureBound (1 - δ) L (by linarith) (by linarith)
  calc 1 - (1 - δ) ^ L ≤ (L : ℝ) * (1 - (1 - δ)) := h
    _ ≤ (L : ℝ) * (2 * δ) := by
      have h1 : 1 - (1 - δ) ≤ 2 * δ := by linarith
      exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- For a positive segment count, multiplying the per-segment error budget by the count recovers
`ε`. -/
theorem ipSegmentBudget_total (L : ℕ) (ε : ℝ) (hL : 0 < L) :
    (L : ℝ) * ipSegmentBudget L ε = ε := by
  unfold ipSegmentBudget
  field_simp

/-- Eventually, the shifted truncation order times `clog₂(k + 2)` is bounded by a constant times
`k + 2`, as used in interaction picture simulation [LowWiebe2018]. -/
theorem ipLogLogRate : ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
    ipClosedFormK (k + 8) * Nat.clog 2 (k + 2) ≤ C * (k + 2) := by
  obtain ⟨C, m0, hrate⟩ := effectiveDysonCutoff_clog_rate
  refine ⟨C, m0, ?_⟩
  intro k hk
  simpa [ipClosedFormK] using! hrate k hk

/-- Under the stated per-time cost bound, the sum of costs over dyadic times is bounded by twice
the full-time logarithmic cost term plus `nd + 1`. -/
theorem ipGateRateTotal (p : EffectiveSegmentParameters) (gamma : ℝ) (hgamma : 0 < gamma)
    (tau delta : ℚ) (nd : ℕ) (CA : ℝ) (hτ : 0 ≤ tau) (hδ : 0 < delta) (hCA : 0 ≤ CA)
    (cost : ℕ → ℕ)
    (hcost : ∀ j ≤ nd, (cost j : ℝ) ≤
        CA * abs (effectiveIPDyadicTime tau nd j) *
          (1 + Real.log (1 + abs (effectiveIPDyadicTime tau nd j) / (delta : ℝ))) ^ gamma + 1) :
    ((∑ j ∈ Finset.range (nd + 1), cost j) : ℝ) ≤
      2 * CA * (tau : ℝ) * (1 + Real.log (1 + (tau : ℝ) / (delta : ℝ))) ^ gamma + (nd + 1) :=
  effectiveInteractionGateRate gamma hgamma tau delta nd CA cost hτ hδ hCA hcost

/-- The sparse interaction picture program's query count equals `ipSparseQueries p`. -/
theorem ipSparseProgram_queries (p : EffectiveSparseParameters) :
    effectiveQueries (ipSparseProgram p) = ipSparseQueries p := by
  unfold ipSparseProgram effectiveQueries ipSparseQueries
  simp

/-- The sparse interaction picture program has width `p.nd + 2 * p.ns + 2 * p.np` and exactly
three steps. -/
theorem ipSparseProgram_shape (p : EffectiveSparseParameters) :
    (ipSparseProgram p).width = p.nd + 2 * p.ns + 2 * p.np ∧
      (ipSparseProgram p).steps.length = 3 := by
  constructor
  · rfl
  · rfl

end Qatlib.Concepts.RandCompile.ChannelBudget
