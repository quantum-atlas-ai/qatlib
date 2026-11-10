/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ParityTester.SampledParity.SampledParityTesterDefs
import Qatlib.Concepts.SparseSyndrome.RowScan
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.SparseSyndrome.RowScan

set_option autoImplicit false

namespace Qatlib.Concepts.ParityTester.SampledParity

open Qatlib.Concepts.ParityTester.SampledParity Qatlib.Concepts.SparseSyndrome.RowScan Matrix
open scoped BigOperators

theorem runSchedule_values_and_reads :
    ∀ (n : ℕ) (rows : List (List (Fin n))) (x : Fin n → ZMod 2)
        (schedule : List (Fin rows.length)),
      (runSchedule rows x schedule).1 = schedule.map (fun i => (parityMatrix rows *ᵥ x) i) ∧
        (runSchedule rows x schedule).2 = schedule.flatMap (fun i => rows.get i) := by
  intro n rows x schedule
  induction schedule with
  | nil => simp [runSchedule]
  | cons i schedule ih =>
    obtain ⟨hv, hl⟩ := scanRow_parity_and_log n x (rows.get i)
    have hm : (scanRow x (rows.get i)).1 = (parityMatrix rows *ᵥ x) i := hv
    constructor
    · change (scanRow x (rows.get i)).1 :: (runSchedule rows x schedule).1 =
        (parityMatrix rows *ᵥ x) i :: schedule.map (fun j => (parityMatrix rows *ᵥ x) j)
      rw [hm, ih.1]
    · change (scanRow x (rows.get i)).2 ++ (runSchedule rows x schedule).2 =
        rows.get i ++ schedule.flatMap (fun j => rows.get j)
      rw [hl, ih.2]

private theorem passes_iff {n : ℕ} (rows : List (List (Fin n)))
    (x : Fin n → ZMod 2) (schedule : List (Fin rows.length)) :
    passes rows x schedule = true ↔ ∀ i ∈ schedule, (parityMatrix rows *ᵥ x) i = 0 := by
  rw [passes, (runSchedule_values_and_reads n rows x schedule).1]
  simp

theorem uniform_schedule_missMass :
    ∀ (n : ℕ) (rows : List (List (Fin n))) (x : Fin n → ZMod 2) (t : ℕ),
      rows ≠ [] →
      missMass rows x t =
        (((rows.length - bitWeight (parityMatrix rows *ᵥ x) : ℕ) : ℚ) /
          (rows.length : ℚ)) ^ t := by
  intro n rows x t _hrows
  classical
  let zeroRows := Finset.univ.filter fun i : Fin rows.length => (parityMatrix rows *ᵥ x) i = 0
  have hpartition : zeroRows.card + bitWeight (parityMatrix rows *ᵥ x) = rows.length := by
    simpa only [Finset.card_univ, Fintype.card_fin] using!
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin rows.length)))
        (fun i => (parityMatrix rows *ᵥ x) i = 0))
  have hz : zeroRows.card = rows.length - bitWeight (parityMatrix rows *ᵥ x) := by omega
  have hschedules : (Finset.univ.filter fun samples : Fin t → Fin rows.length =>
      passes rows x (List.ofFn samples) = true) =
      Fintype.piFinset (fun _ : Fin t => zeroRows) := by
    ext samples
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      passes_iff, List.forall_mem_ofFn_iff]
    simp [zeroRows]
  unfold missMass
  rw [hschedules, Fintype.card_piFinset_const, hz, Nat.cast_pow, div_pow]

private theorem schedule_reads_le {n : ℕ} (rows : List (List (Fin n)))
    (x : Fin n → ZMod 2) (w : ℕ) (hwidth : ∀ row ∈ rows, row.length ≤ w)
    (schedule : List (Fin rows.length)) :
    (runSchedule rows x schedule).2.length ≤ schedule.length * w := by
  rw [(runSchedule_values_and_reads n rows x schedule).2]
  induction schedule with
  | nil => simp
  | cons i schedule ih =>
    have hi := hwidth (rows.get i) (List.get_mem rows i)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem amplified_test_accuracy_and_reads :
    ∀ (n t w : ℕ) (rows : List (List (Fin n))) (x : Fin n → ZMod 2)
        (δ ε : ℚ), rows ≠ [] →
      (∀ row ∈ rows, row.length ≤ w) → 0 ≤ δ → δ ≤ 1 →
      δ ≤ (bitWeight (parityMatrix rows *ᵥ x) : ℚ) / (rows.length : ℚ) →
      (1 - δ) ^ t ≤ ε →
      missMass rows x t ≤ ε ∧
        ∀ samples : Fin t → Fin rows.length,
          (runSchedule rows x (List.ofFn samples)).2.length ≤ t * w := by
  intro n t w rows x δ ε hrows hwidth _hδ hδone hfrac hpower
  have hweight : bitWeight (parityMatrix rows *ᵥ x) ≤ rows.length := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  have hm : (0 : ℚ) < rows.length := by
    exact_mod_cast List.length_pos_iff.mpr hrows
  have hbase : (((rows.length - bitWeight (parityMatrix rows *ᵥ x) : ℕ) : ℚ) /
      (rows.length : ℚ)) = 1 - (bitWeight (parityMatrix rows *ᵥ x) : ℚ) / rows.length := by
    rw [Nat.cast_sub hweight]
    field_simp
  have hnonneg : (0 : ℚ) ≤
      ((rows.length - bitWeight (parityMatrix rows *ᵥ x) : ℕ) : ℚ) / (rows.length : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) hm.le
  refine ⟨?_, fun samples => ?_⟩
  · rw [uniform_schedule_missMass n rows x t hrows]
    exact (pow_le_pow_left₀ hnonneg (by rw [hbase]; linarith) t).trans hpower
  · simpa only [List.length_ofFn] using schedule_reads_le rows x w hwidth (List.ofFn samples)

end Qatlib.Concepts.ParityTester.SampledParity
