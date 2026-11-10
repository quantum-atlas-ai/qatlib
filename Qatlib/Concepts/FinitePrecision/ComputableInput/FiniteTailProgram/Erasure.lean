/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Observed
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram

private theorem table_refines {α : Type} {r : ℕ}
    (is : List (Fin r)) (hi : is = List.finRange r)
    (f : Fin r → Fin r → SavedTable.Observed α) (g : Fin r → Fin r → α)
    (h : ∀ i j, (f i j).arithmetic.value = g i j) :
    (SavedTable.tableUsing is hi f).arithmetic.value = Plain.table is hi g := by
  rw [SavedTable.tableUsing_arithmetic_eq]
  apply Vector.ext
  intro i hbi
  apply Vector.ext
  intro j hbj
  simpa [SavedTable.Structural.table, SavedTable.Structural.tabulate,
    Plain.table, SavedTable.Value.tabulate_eq] using h ⟨i,hbi⟩ ⟨j,hbj⟩

theorem dot_refines {α ι : Type} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (x y : ι → α) (is : List ι) :
    (Metered.dot M x y is).arithmetic.value = Plain.dot K x y is := by
  induction is with
  | nil => exact h.zero_eq
  | cons i is ih =>
    simp only [Metered.dot, Metered.retain, Plain.dot, h.add_eq, h.mul_eq, ih]

theorem sum_refines {α ι : Type} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (x : ι → α) (is : List ι) :
    (Metered.sum M x is).arithmetic.value = Plain.sum K x is := by
  induction is with
  | nil => exact h.zero_eq
  | cons i is ih => simp only [Metered.sum, Metered.retain, Plain.sum, h.add_eq, ih]

theorem conjugates_refines {α : Type} {r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r) (v : Vector α r) :
    (Metered.conjugates M is hi v).arithmetic.value = Plain.conjugates K is hi v := by
  apply SavedTable.tabulateUsing_refines_value
  intro i
  exact h.conj_eq v[i]

theorem adjoints_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k) (A : Vector (Table α r) k) :
    (Metered.adjoints M is hi js hj A).arithmetic.value = Plain.adjoints K is hi js hj A := by
  apply SavedTable.tabulateUsing_refines_value
  intro j
  apply table_refines
  intro i l
  exact h.conj_eq A[j][l][i]

theorem outer_refines {α : Type} {r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r) (v cv : Vector α r) :
    (Metered.outer M is hi v cv).arithmetic.value = Plain.outer K is hi v cv := by
  apply table_refines
  intro i l
  exact h.mul_eq v[i] cv[l]

theorem lefts_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A : Vector (Table α r) k) (Y : Table α r) :
    (Metered.lefts M is hi js hj A Y).arithmetic.value = Plain.lefts K is hi js hj A Y := by
  apply SavedTable.tabulateUsing_refines_value
  intro j
  apply table_refines
  intro i l
  exact dot_refines K M h _ _ is

theorem products_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k) (left adj : Vector (Table α r) k) :
    (Metered.products M is hi js hj left adj).arithmetic.value =
      Plain.products K is hi js hj left adj := by
  apply SavedTable.tabulateUsing_refines_value
  intro j
  apply table_refines
  intro i l
  exact dot_refines K M h _ _ is

theorem letters_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (terms : Vector (Table α r) k) :
    (Metered.letters M is hi js terms).arithmetic.value = Plain.letters K is hi js terms := by
  apply table_refines
  intro i l
  exact sum_refines K M h _ js

theorem step_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (Y : Table α r) :
    (Metered.step M is hi js hj A adj Y).arithmetic.value =
      Plain.step K is hi js hj A adj Y := by
  simp only [Metered.step, Metered.retain, lefts_refines K M h,
    products_refines K M h, letters_refines K M h, Plain.step]

theorem tailAdd_refines {α : Type} {r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r) (X Y : Table α r) :
    (Metered.tailAdd M is hi X Y).arithmetic.value = Plain.tailAdd K is hi X Y := by
  apply table_refines
  intro i l
  exact h.add_eq X[i][l] Y[i][l]

theorem run_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (is : List (Fin r)) (hi : is = List.finRange r)
    (js : List (Fin k)) (hj : js = List.finRange k)
    (A adj : Vector (Table α r) k) (n : ℕ) (Y : Table α r) :
    (Metered.run M is hi js hj A adj n Y).arithmetic.value =
      (Plain.run K is hi js hj A adj n Y).toVector := by
  induction n generalizing Y with
  | zero =>
    simp [Plain.zeroTable, SavedTable.TailPacket.toVector,
      SavedTable.TailPacket.toList, h.zero_eq]
  | succ n ih =>
    simp only [Metered.run_value_succ, Plain.run_succ]
    rw [step_refines K M h, ih, tailAdd_refines K M h]
    simp only [SavedTable.TailPacket.toVector_head, SavedTable.TailPacket.toVector_prepend]

theorem driver_refines {α : Type} {k r : ℕ} (K : Kernel α) (M : ObservedKernel α)
    (h : Refines K M) (v : Vector α r) (A : Vector (Table α r) k) (D : ℕ) :
    (Metered.driver M v A D).arithmetic.value = Plain.driver K v A D := by
  simp only [Metered.driver, Plain.driver, Metered.retain, conjugates_refines K M h,
    adjoints_refines K M h, outer_refines K M h, run_refines K M h]
  rw [← SavedTable.finish_value_eq_plain]
  exact (SavedTable.finish_spec _).1.symm

end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
