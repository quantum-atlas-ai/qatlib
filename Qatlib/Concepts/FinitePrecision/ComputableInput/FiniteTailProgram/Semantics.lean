/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Erasure
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
open Matrix

def algebraKernel (α : Type) [Zero α] [Add α] [Mul α] [Star α] : Kernel α :=
  ⟨0, (· + ·), (· * ·), star⟩

def decode {α : Type} {r : ℕ} (Y : Table α r) : Matrix (Fin r) (Fin r) α :=
  fun i j => Y[i][j]

section Semantics
variable {α : Type} [Semiring α] [Star α]

@[simp] theorem algebraKernel_zero : (algebraKernel α).zero = 0 := rfl

@[simp] theorem algebraKernel_add (x y : α) : (algebraKernel α).add x y = x+y := rfl

@[simp] theorem algebraKernel_mul (x y : α) : (algebraKernel α).mul x y = x*y := rfl

@[simp] theorem algebraKernel_conj (x : α) : (algebraKernel α).conj x = star x := rfl

omit [Semiring α] [Star α] in

@[simp] theorem table_entry {r : ℕ} (is : List (Fin r)) (hi : is = List.finRange r)
    (f : Fin r → Fin r → α) (i j : Fin r) :
    (Plain.table is hi f)[i][j] = f i j := by
  simp [Plain.table, SavedTable.Value.tabulate_eq]

private theorem dot_toFinset {ι : Type} [DecidableEq ι]
    (x y : ι → α) (is : List ι) (hn : is.Nodup) :
    Plain.dot (algebraKernel α) x y is = ∑ i ∈ is.toFinset, x i * y i := by
  induction is with
  | nil => simp [Plain.dot, algebraKernel]
  | cons i is ih =>
    have hi := List.nodup_cons.mp hn
    change x i * y i + Plain.dot (algebraKernel α) x y is = _
    rw [ih hi.2, List.toFinset_cons, Finset.sum_insert (by simpa using hi.1)]

private theorem sum_toFinset {ι : Type} [DecidableEq ι]
    (x : ι → α) (is : List ι) (hn : is.Nodup) :
    Plain.sum (algebraKernel α) x is = ∑ i ∈ is.toFinset, x i := by
  induction is with
  | nil => simp [Plain.sum, algebraKernel]
  | cons i is ih =>
    have hi := List.nodup_cons.mp hn
    change x i + Plain.sum (algebraKernel α) x is = _
    rw [ih hi.2, List.toFinset_cons, Finset.sum_insert (by simpa using hi.1)]

@[simp] theorem dot_finRange {r : ℕ} (x y : Fin r → α) :
    Plain.dot (algebraKernel α) x y (List.finRange r) = ∑ i : Fin r, x i * y i := by
  simpa using dot_toFinset x y (List.finRange r) (List.nodup_finRange r)

@[simp] theorem sum_finRange {r : ℕ} (x : Fin r → α) :
    Plain.sum (algebraKernel α) x (List.finRange r) = ∑ i : Fin r, x i := by
  simpa using sum_toFinset x (List.finRange r) (List.nodup_finRange r)

def transfer {k r : ℕ} (A : Vector (Table α r) k) (Y : Matrix (Fin r) (Fin r) α) :
    Matrix (Fin r) (Fin r) α := ∑ j : Fin k, decode A[j] * Y * (decode A[j])ᴴ

def level {k r : ℕ} (A : Vector (Table α r) k) (v : Vector α r) :
    ℕ → Matrix (Fin r) (Fin r) α
  | 0 => fun i j => v[i] * star v[j]
  | n+1 => transfer A (level A v n)

def tail {k r : ℕ} (A : Vector (Table α r) k) (v : Vector α r) (D s : ℕ) :
    Matrix (Fin r) (Fin r) α := ∑ t ∈ Finset.Ico s D, level A v t

@[simp] theorem adjoints_entry {k r : ℕ} (A : Vector (Table α r) k)
    (j : Fin k) (i l : Fin r) :
    (Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A)[j][i][l] =
      star A[j][l][i] := by
  simp [Plain.adjoints, Plain.table, SavedTable.Value.tabulate_eq]

@[simp] theorem lefts_entry {k r : ℕ} (A : Vector (Table α r) k) (Y : Table α r)
    (j : Fin k) (i l : Fin r) :
    (Plain.lefts (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A Y)[j][i][l] =
      ∑ h : Fin r, A[j][i][h] * Y[h][l] := by
  simp [Plain.lefts, Plain.table, SavedTable.Value.tabulate_eq]

@[simp] theorem products_entry {k r : ℕ} (left adj : Vector (Table α r) k)
    (j : Fin k) (i l : Fin r) :
    (Plain.products (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl left adj)[j][i][l] =
      ∑ h : Fin r, left[j][i][h] * adj[j][h][l] := by
  simp [Plain.products, Plain.table, SavedTable.Value.tabulate_eq]

@[simp] theorem letters_entry {k r : ℕ} (terms : Vector (Table α r) k)
    (i l : Fin r) :
    (Plain.letters (algebraKernel α) (List.finRange r) rfl (List.finRange k) terms)[i][l] =
      ∑ j : Fin k, terms[j][i][l] := by
  simp [Plain.letters, Plain.table, SavedTable.Value.tabulate_eq]

theorem step_decode {k r : ℕ} (A : Vector (Table α r) k) (Y : Table α r) :
    decode (Plain.step (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A
      (Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A) Y) =
      transfer A (decode Y) := by
  ext i l
  simp only [Plain.step, decode, letters_entry, products_entry, lefts_entry,
    adjoints_entry, transfer, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem tailAdd_decode {r : ℕ} (X Y : Table α r) :
    decode (Plain.tailAdd (algebraKernel α) (List.finRange r) rfl X Y) = decode X + decode Y := by
  ext i j
  simp [Plain.tailAdd, Plain.table, SavedTable.Value.tabulate_eq, decode]

theorem outer_decode {k r : ℕ} (v : Vector α r) (A : Vector (Table α r) k) :
    decode (Plain.outer (algebraKernel α) (List.finRange r) rfl v
      (Plain.conjugates (algebraKernel α) (List.finRange r) rfl v)) = level A v 0 := by
  ext i j
  simp [Plain.outer, Plain.conjugates, Plain.table, SavedTable.Value.tabulate_eq,
    decode, level]

private theorem finish_eq_toVector {β : Type} {n : ℕ} (p : SavedTable.TailPacket β n) :
    SavedTable.Value.finish p = p.toVector := by
  rw [← SavedTable.finish_value_eq_plain]
  exact (SavedTable.finish_spec p).1

theorem run_decode {k r : ℕ} (A : Vector (Table α r) k) (v : Vector α r) (n : ℕ) :
    ∀ (start : ℕ) (Y : Table α r), decode Y = level A v start →
    ∀ i : Fin (n+1),
      decode ((Plain.run (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A
        (Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A)
        n Y).toVector[i]) = tail A v (start+n) (start+i) := by
  induction n with
  | zero =>
    intro start Y hY i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    ext a b
    simp [Plain.zeroTable, decode, algebraKernel, SavedTable.TailPacket.toVector,
      SavedTable.TailPacket.toList, tail]
  | succ n ih =>
    intro start Y hY i
    let adj := Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A
    let next := Plain.step (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A adj Y
    have hnext : decode next = level A v (start+1) := by
      rw [show decode next = transfer A (decode Y) from step_decode A Y, hY]
      rfl
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Plain.run_succ, SavedTable.TailPacket.toVector_prepend,
        Fin.getElem_fin, Fin.val_zero, Vector.getElem_insertIdx_self, tailAdd_decode,
        Nat.add_zero]
      have hh := ih (start+1) next hnext 0
      simp only [SavedTable.TailPacket.toVector_head, Fin.getElem_fin,
        Fin.val_zero, Nat.add_zero] at hh
      rw [hY, hh]
      rw [show start+1+n = start+(n+1) by omega]
      exact (Finset.sum_eq_sum_Ico_succ_bot (by omega : start < start+(n+1))
        (level A v)).symm
    · simp only [Plain.run_succ, SavedTable.TailPacket.toVector_prepend,
        Fin.getElem_fin, Fin.val_succ]
      rw [Vector.getElem_insertIdx_of_gt (by omega : (i : ℕ)+1 ≤ n+1)
        (by omega : 0 < (i : ℕ)+1)]
      simp only [Nat.add_sub_cancel]
      have hh := ih (start+1) next hnext i
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem driver_decode {k r : ℕ} (v : Vector α r) (A : Vector (Table α r) k)
    (D : ℕ) (s : Fin (D+1)) :
    decode ((Plain.driver (algebraKernel α) v A D)[s]) = tail A v D s := by
  have h := run_decode A v D 0
    (Plain.outer (algebraKernel α) (List.finRange r) rfl v
      (Plain.conjugates (algebraKernel α) (List.finRange r) rfl v))
    (outer_decode v A) s
  simpa only [Plain.driver, finish_eq_toVector, Nat.zero_add] using h

theorem observed_driver_decode {k r : ℕ} (M : ObservedKernel α)
    (h : Refines (algebraKernel α) M) (v : Vector α r)
    (A : Vector (Table α r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((Metered.driver M v A D).arithmetic.value[s]) = tail A v D s := by
  rw [driver_refines (algebraKernel α) M h]
  exact driver_decode v A D s

end Semantics
end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
