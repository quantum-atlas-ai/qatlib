/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder

/-!
# Boolean echelon bases and orthogonal generators

This module converts Boolean pivot rows and kernel rows into linearly independent generating
families over `ZMod 2`. It transfers the correctness and operation bounds of the Boolean echelon
algorithms to the submodule language used by the exact Simon development. These constructions
support the results of [BrassardHoyer1997].

## Main statements

* `proposition1_actual_algorithm`: proves independence, spanning, and operation bounds for pivot
  extraction.
* `proposition2_actual_algorithm`: proves correctness and a polynomial operation bound for the
  orthogonal basis.

## References

* [Brassard and Hoyer, 1997][BrassardHoyer1997]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open scoped Classical
open Finset

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Papers.ExactSimon97.MainResults

/-- The subtype of coordinate indices for which a pivot row is present. -/
abbrev PivotIdx {n : ℕ} (piv : Fin n → Option (Reg n)) : Type :=
  {i : Fin n // (piv i).isSome = true}

/-- The binary vector represented by the pivot row at a present pivot index. -/
def pivotVec {n : ℕ} (piv : Fin n → Option (Reg n)) (p : PivotIdx piv) : BoolVec n :=
  regBooleanEquiv n ((piv p.1).get p.2)

/-- In Boolean echelon form, a later pivot vector vanishes at every earlier pivot coordinate. -/
theorem pivotVec_apply_eq_zero {n : ℕ} {piv : Fin n → Option (Reg n)}
    (hech : IsBooleanEchelon piv) {p q : PivotIdx piv} (hlt : p.1 < q.1) :
    pivotVec piv q p.1 = 0 := by
  have hrow : piv q.1 = some ((piv q.1).get q.2) := (Option.some_get q.2).symm
  have hfalse : ((piv q.1).get q.2) p.1 = false :=
    (hech q.1 _ hrow).2 p.1 hlt
  simp [pivotVec, hfalse]

/-- In Boolean echelon form, a pivot vector has value one at its own pivot coordinate. -/
theorem pivotVec_apply_self {n : ℕ} {piv : Fin n → Option (Reg n)}
    (hech : IsBooleanEchelon piv) (p : PivotIdx piv) :
    pivotVec piv p p.1 = 1 := by
  have hrow : piv p.1 = some ((piv p.1).get p.2) := (Option.some_get p.2).symm
  have htrue : ((piv p.1).get p.2) p.1 = true := (hech p.1 _ hrow).1
  simp [pivotVec, htrue]

/-- The pivot vectors of a Boolean echelon table are linearly independent over `ZMod 2`. -/
theorem pivotVec_linearIndependent {n : ℕ} (piv : Fin n → Option (Reg n))
    (hech : IsBooleanEchelon piv) :
    LinearIndependent (ZMod 2) (pivotVec piv) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  classical
  by_contra hgi
  have hne : (Finset.univ.filter (fun p : PivotIdx piv => g p ≠ 0)).Nonempty :=
    ⟨i, by simp [hgi]⟩
  obtain ⟨p0, hp0mem, hp0min⟩ :=
    Finset.exists_min_image
      (Finset.univ.filter (fun p : PivotIdx piv => g p ≠ 0)) (fun p => p.1) hne
  have hp0ne : g p0 ≠ 0 := (Finset.mem_filter.mp hp0mem).2
  have hcoord := congrFun hsum p0.1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
  have hsingle : (∑ p, g p * pivotVec piv p p0.1) =
      g p0 * pivotVec piv p0 p0.1 := by
    refine Finset.sum_eq_single p0 ?_ ?_
    · intro p _ hneval
      by_cases hlt : p.1 < p0.1
      · have hc0 : g p = 0 := by
          by_contra hc
          have hpmem : p ∈ Finset.univ.filter (fun q : PivotIdx piv => g q ≠ 0) := by
            simp [hc]
          exact absurd hlt (not_lt.mpr (hp0min p hpmem))
        rw [hc0, zero_mul]
      · have hge : p0.1 ≤ p.1 := le_of_not_gt hlt
        have hneval' : p0.1 ≠ p.1 := fun h => hneval (Subtype.ext h.symm)
        have hgt : p0.1 < p.1 := lt_of_le_of_ne hge hneval'
        rw [pivotVec_apply_eq_zero hech hgt, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ p0) hnot
  rw [hsingle, pivotVec_apply_self hech p0, mul_one] at hcoord
  exact hp0ne hcoord

/-- The range of `pivotVec` consists exactly of the vectors represented by present pivot rows. -/
theorem range_pivotVec {n : ℕ} (piv : Fin n → Option (Reg n)) :
    Set.range (pivotVec piv) =
      {v : BooleanVec n | ∃ i row, piv i = some row ∧ v = regBooleanEquiv n row} := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, (piv p.1).get p.2, (Option.some_get p.2).symm, rfl⟩
  · rintro ⟨i, row, hrow, rfl⟩
    have hisSome : (piv i).isSome = true := by rw [hrow]; rfl
    refine ⟨⟨i, hisSome⟩, ?_⟩
    show regBooleanEquiv n ((piv i).get hisSome) = regBooleanEquiv n row
    congr 1
    exact Option.some_injective _ (by
      calc some ((piv i).get hisSome) = piv i := Option.some_get hisSome
        _ = some row := hrow)

/-- The span of the pivot vectors equals the submodule associated with the Boolean pivot span. -/
theorem span_pivotVec {n : ℕ} (piv : Fin n → Option (Reg n)) :
    Submodule.span (ZMod 2) (Set.range (pivotVec piv)) =
      AddSubgroup.toZModSubmodule 2 (booleanPivotSpan piv) := by
  apply SetLike.ext
  intro x
  rw [mem_span_iff_mem_closure_zmod2, AddSubgroup.mem_toZModSubmodule,
    range_pivotVec]
  rfl

/-- The span of the vectors in a row list equals the submodule associated with the Boolean row
span. -/
theorem span_range_get {n : ℕ} (l : List (Reg n)) :
    Submodule.span (ZMod 2)
        (Set.range (fun j : Fin l.length => regBooleanEquiv n (l.get j))) =
      AddSubgroup.toZModSubmodule 2 (booleanRowsSpan l) := by
  apply SetLike.ext
  intro x
  rw [mem_span_iff_mem_closure_zmod2, AddSubgroup.mem_toZModSubmodule]
  have hgen : Set.range (fun j : Fin l.length => regBooleanEquiv n (l.get j)) =
      {v : BooleanVec n | ∃ r, r ∈ l ∧ v = regBooleanEquiv n r} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨l.get j, List.get_mem l j, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hgen]
  rfl

/-- The computed pivot family is independent and spans the input rows, with at most `rows.length
* n` XORs and `rows.length * (4 * n ^ 2 + 4 * n)` bit operations. See [BrassardHoyer1997]. -/
theorem proposition1_actual_algorithm {n : ℕ} (rows : List (Reg n)) :
    LinearIndependent (ZMod 2) (pivotVec (booleanEchelonRun rows).pivots) ∧
      Submodule.span (ZMod 2)
          (Set.range (pivotVec (booleanEchelonRun rows).pivots)) =
        AddSubgroup.toZModSubmodule 2 (booleanRowsSpan rows) ∧
      (booleanEchelonRun rows).xorCount ≤ rows.length * n ∧
      (booleanEchelonRun rows).bitOps ≤ rows.length * (4 * n ^ 2 + 4 * n) := by
  obtain ⟨hech, hspan, hxor⟩ := boolean_gaussian_actual_echelon rows
  have hbit : (booleanEchelonRun rows).bitOps ≤ rows.length * (4 * n ^ 2 + 4 * n) := by
    unfold booleanEchelonRun booleanEchelonContinue
    have h := (booleanEchelonContinue_invariant rows
      ⟨fun _ => none, 0, 0⟩ isBooleanEchelon_none).2.2.2
    simpa using h
  refine ⟨pivotVec_linearIndependent _ hech, ?_, hxor, hbit⟩
  rw [span_pivotVec, hspan]

/-- The finite enumeration of computed pivot vectors is an independent generating family for the
submodule spanned by the input rows. See [BrassardHoyer1997]. -/
theorem proposition1_generating_set {n : ℕ} (rows : List (Reg n)) :
    LinIndep (fun j : Fin (Fintype.card (PivotIdx (booleanEchelonRun rows).pivots)) =>
        pivotVec (booleanEchelonRun rows).pivots
          ((Fintype.equivFin (PivotIdx (booleanEchelonRun rows).pivots)).symm j)) ∧
      Generates
        (fun j : Fin (Fintype.card (PivotIdx (booleanEchelonRun rows).pivots)) =>
          pivotVec (booleanEchelonRun rows).pivots
            ((Fintype.equivFin (PivotIdx (booleanEchelonRun rows).pivots)).symm j))
        (AddSubgroup.toZModSubmodule 2 (booleanRowsSpan rows)) := by
  obtain ⟨hech, hspan, -⟩ := boolean_gaussian_actual_echelon rows
  have hrange : Set.range
      (fun j : Fin (Fintype.card (PivotIdx (booleanEchelonRun rows).pivots)) =>
        pivotVec (booleanEchelonRun rows).pivots
          ((Fintype.equivFin (PivotIdx (booleanEchelonRun rows).pivots)).symm j)) =
      Set.range (pivotVec (booleanEchelonRun rows).pivots) := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨Fintype.equivFin (PivotIdx (booleanEchelonRun rows).pivots) a, by simp⟩
  refine ⟨(pivotVec_linearIndependent _ hech).comp _
    (Fintype.equivFin (PivotIdx (booleanEchelonRun rows).pivots)).symm.injective, ?_⟩
  unfold Generates
  rw [hrange, span_pivotVec, hspan]

/-- The computed kernel list has no duplicates, is linearly independent, spans the orthogonal
row submodule, and has operation count at most `n + n * (n * (2 + 5 * n))`. See
[BrassardHoyer1997]. -/
theorem proposition2_actual_algorithm {n : ℕ} (rows : List (Reg n)) :
    (booleanKernelBasis (booleanEchelonRun rows).pivots).Nodup ∧
      LinearIndependent (ZMod 2)
        (fun j : Fin (booleanKernelBasis (booleanEchelonRun rows).pivots).length =>
          regBooleanEquiv n
            ((booleanKernelBasis (booleanEchelonRun rows).pivots).get j)) ∧
      Submodule.span (ZMod 2)
          (Set.range
            (fun j : Fin (booleanKernelBasis (booleanEchelonRun rows).pivots).length =>
              regBooleanEquiv n
                ((booleanKernelBasis (booleanEchelonRun rows).pivots).get j))) =
        AddSubgroup.toZModSubmodule 2
          (booleanOrthogonal (booleanRowsSpan rows)) ∧
      (booleanKernelBasisFull (booleanEchelonRun rows).pivots).2 ≤
        n + n * (n * (2 + 5 * n)) := by
  obtain ⟨hech, hspan, -⟩ := boolean_gaussian_actual_echelon rows
  obtain ⟨hnodup, hli, hrows, -⟩ :=
    boolean_gaussian_kernel_basis (booleanEchelonRun rows).pivots hech
  refine ⟨hnodup, hli, ?_, booleanKernelBasisFull_snd_le _⟩
  rw [span_range_get, hrows, booleanPivotKernel_eq_booleanOrthogonal_span, hspan]

/-- The computed kernel vectors form an independent generating family for the orthogonal
submodule of the input row span. See [BrassardHoyer1997]. -/
theorem proposition2_ortho_generating_set {n : ℕ} (rows : List (Reg n)) :
    LinIndep
        (fun j : Fin (booleanKernelBasis (booleanEchelonRun rows).pivots).length =>
          regBooleanEquiv n
            ((booleanKernelBasis (booleanEchelonRun rows).pivots).get j)) ∧
      Generates
        (fun j : Fin (booleanKernelBasis (booleanEchelonRun rows).pivots).length =>
          regBooleanEquiv n
            ((booleanKernelBasis (booleanEchelonRun rows).pivots).get j))
        (AddSubgroup.toZModSubmodule 2
          (booleanOrthogonal (booleanRowsSpan rows))) := by
  obtain ⟨-, hli, hspan, -⟩ := proposition2_actual_algorithm rows
  exact ⟨hli, hspan⟩

end Qatlib.Papers.ExactSimon97.MainResults
