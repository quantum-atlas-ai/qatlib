/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram.Erasure
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Matrix semantics of finite-tail programs

This module interprets vector tables as matrices over a semiring with a star operation. The
transfer map `transfer` sums the products `decode A[j] * Y * (decode A[j])ᴴ`; its iterates
`level` and finite sums `tail` describe the values returned by both the plain and observed
finite-tail drivers.

For background on matrix maps expressed as sums of conjugated products, see [Watrous2018].

## Main statements

* `step_decode`: a plain step decodes to the matrix transfer map.
* `run_decode`: every computed tail has the expected finite-sum semantics.
* `observed_driver_decode`: the observed driver has the same matrix semantics.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
open Matrix

/-- Forms a plain scalar kernel from zero, addition, multiplication, and star operations on `α`. -/
def algebraKernel (α : Type) [Zero α] [Add α] [Mul α] [Star α] : Kernel α :=
  ⟨0, (· + ·), (· * ·), star⟩

/-- Interprets a square vector table as a matrix with the same entries. -/
def decode {α : Type} {r : ℕ} (Y : Table α r) : Matrix (Fin r) (Fin r) α :=
  fun i j => Y[i][j]

section Semantics
variable {α : Type} [Semiring α] [Star α]

/-- The zero field of `algebraKernel` is the scalar zero. -/
@[simp] theorem algebraKernel_zero : (algebraKernel α).zero = 0 := rfl

/-- The addition field of `algebraKernel` is scalar addition. -/
@[simp] theorem algebraKernel_add (x y : α) : (algebraKernel α).add x y = x+y := rfl

/-- The multiplication field of `algebraKernel` is scalar multiplication. -/
@[simp] theorem algebraKernel_mul (x y : α) : (algebraKernel α).mul x y = x*y := rfl

/-- The conjugation field of `algebraKernel` is the star operation. -/
@[simp] theorem algebraKernel_conj (x : α) : (algebraKernel α).conj x = star x := rfl

omit [Semiring α] [Star α] in

/-- Tabulating a function over the full finite index list returns that function at each table
entry. -/
@[simp] theorem table_entry {r : ℕ} (is : List (Fin r)) (hi : is = List.finRange r)
    (f : Fin r → Fin r → α) (i j : Fin r) :
    (Plain.table is hi f)[i][j] = f i j := by
  simp [Plain.table, SavedTable.Value.tabulate_eq]

/-- For a duplicate-free index list, the plain dot product equals the finite sum of pointwise
products over its associated finite set. -/
private theorem dot_toFinset {ι : Type} [DecidableEq ι]
    (x y : ι → α) (is : List ι) (hn : is.Nodup) :
    Plain.dot (algebraKernel α) x y is = ∑ i ∈ is.toFinset, x i * y i := by
  induction is with
  | nil => simp [Plain.dot, algebraKernel]
  | cons i is ih =>
    have hi := List.nodup_cons.mp hn
    change x i * y i + Plain.dot (algebraKernel α) x y is = _
    rw [ih hi.2, List.toFinset_cons, Finset.sum_insert (by simpa using hi.1)]

/-- For a duplicate-free index list, the plain sum equals the finite sum over its associated
finite set. -/
private theorem sum_toFinset {ι : Type} [DecidableEq ι]
    (x : ι → α) (is : List ι) (hn : is.Nodup) :
    Plain.sum (algebraKernel α) x is = ∑ i ∈ is.toFinset, x i := by
  induction is with
  | nil => simp [Plain.sum, algebraKernel]
  | cons i is ih =>
    have hi := List.nodup_cons.mp hn
    change x i + Plain.sum (algebraKernel α) x is = _
    rw [ih hi.2, List.toFinset_cons, Finset.sum_insert (by simpa using hi.1)]

/-- The plain dot product over `List.finRange r` equals the sum of products over `Fin r`. -/
@[simp] theorem dot_finRange {r : ℕ} (x y : Fin r → α) :
    Plain.dot (algebraKernel α) x y (List.finRange r) = ∑ i : Fin r, x i * y i := by
  simpa using dot_toFinset x y (List.finRange r) (List.nodup_finRange r)

/-- The plain sum over `List.finRange r` equals the sum over `Fin r`. -/
@[simp] theorem sum_finRange {r : ℕ} (x : Fin r → α) :
    Plain.sum (algebraKernel α) x (List.finRange r) = ∑ i : Fin r, x i := by
  simpa using sum_toFinset x (List.finRange r) (List.nodup_finRange r)

/-- The matrix transfer map sending `Y` to the sum of `decode A[j] * Y * (decode A[j])ᴴ` over
all letters. -/
def transfer {k r : ℕ} (A : Vector (Table α r) k) (Y : Matrix (Fin r) (Fin r) α) :
    Matrix (Fin r) (Fin r) α := ∑ j : Fin k, decode A[j] * Y * (decode A[j])ᴴ

/-- Iterates the transfer map, starting with the matrix whose entries are `v[i] * star v[j]`. -/
def level {k r : ℕ} (A : Vector (Table α r) k) (v : Vector α r) :
    ℕ → Matrix (Fin r) (Fin r) α
  | 0 => fun i j => v[i] * star v[j]
  | n+1 => transfer A (level A v n)

/-- The sum of transfer levels with indices in the half-open interval from `s` to `D`. -/
def tail {k r : ℕ} (A : Vector (Table α r) k) (v : Vector α r) (D s : ℕ) :
    Matrix (Fin r) (Fin r) α := ∑ t ∈ Finset.Ico s D, level A v t

/-- Each entry of a plain adjoint table is the star of the transposed input entry. -/
@[simp] theorem adjoints_entry {k r : ℕ} (A : Vector (Table α r) k)
    (j : Fin k) (i l : Fin r) :
    (Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A)[j][i][l] =
      star A[j][l][i] := by
  simp [Plain.adjoints, Plain.table, SavedTable.Value.tabulate_eq]

/-- Each entry of a plain left-product table is the corresponding matrix-product sum. -/
@[simp] theorem lefts_entry {k r : ℕ} (A : Vector (Table α r) k) (Y : Table α r)
    (j : Fin k) (i l : Fin r) :
    (Plain.lefts (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A Y)[j][i][l] =
      ∑ h : Fin r, A[j][i][h] * Y[h][l] := by
  simp [Plain.lefts, Plain.table, SavedTable.Value.tabulate_eq]

/-- Each entry of a paired plain table product is the corresponding matrix-product sum. -/
@[simp] theorem products_entry {k r : ℕ} (left adj : Vector (Table α r) k)
    (j : Fin k) (i l : Fin r) :
    (Plain.products (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl left adj)[j][i][l] =
      ∑ h : Fin r, left[j][i][h] * adj[j][h][l] := by
  simp [Plain.products, Plain.table, SavedTable.Value.tabulate_eq]

/-- Each entry of the plain letter sum is the sum of the corresponding entries over all letters. -/
@[simp] theorem letters_entry {k r : ℕ} (terms : Vector (Table α r) k)
    (i l : Fin r) :
    (Plain.letters (algebraKernel α) (List.finRange r) rfl (List.finRange k) terms)[i][l] =
      ∑ j : Fin k, terms[j][i][l] := by
  simp [Plain.letters, Plain.table, SavedTable.Value.tabulate_eq]

/-- A plain step using the computed adjoints decodes to the matrix transfer map applied to the
decoded input. -/
theorem step_decode {k r : ℕ} (A : Vector (Table α r) k) (Y : Table α r) :
    decode (Plain.step (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A
      (Plain.adjoints (algebraKernel α) (List.finRange r) rfl (List.finRange k) rfl A) Y) =
      transfer A (decode Y) := by
  ext i l
  simp only [Plain.step, decode, letters_entry, products_entry, lefts_entry,
    adjoints_entry, transfer, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Decoding plain entrywise table addition gives matrix addition. -/
theorem tailAdd_decode {r : ℕ} (X Y : Table α r) :
    decode (Plain.tailAdd (algebraKernel α) (List.finRange r) rfl X Y) = decode X + decode Y := by
  ext i j
  simp [Plain.tailAdd, Plain.table, SavedTable.Value.tabulate_eq, decode]

/-- The outer table formed from `v` and its computed conjugates decodes to the zeroth transfer
level. -/
theorem outer_decode {k r : ℕ} (v : Vector α r) (A : Vector (Table α r) k) :
    decode (Plain.outer (algebraKernel α) (List.finRange r) rfl v
      (Plain.conjugates (algebraKernel α) (List.finRange r) rfl v)) = level A v 0 := by
  ext i j
  simp [Plain.outer, Plain.conjugates, Plain.table, SavedTable.Value.tabulate_eq,
    decode, level]

/-- Finishing a saved tail packet gives its underlying vector representation. -/
private theorem finish_eq_toVector {β : Type} {n : ℕ} (p : SavedTable.TailPacket β n) :
    SavedTable.Value.finish p = p.toVector := by
  rw [← SavedTable.finish_value_eq_plain]
  exact (SavedTable.finish_spec p).1

/-- Starting from a table decoding to level `start`, the `i`th output of an `n`-step plain run
decodes to the sum of levels from `start + i` up to `start + n` exclusively. -/
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

/-- The `s`th output table of the plain depth-`D` driver decodes to `tail A v D s`. -/
theorem driver_decode {k r : ℕ} (v : Vector α r) (A : Vector (Table α r) k)
    (D : ℕ) (s : Fin (D+1)) :
    decode ((Plain.driver (algebraKernel α) v A D)[s]) = tail A v D s := by
  have h := run_decode A v D 0
    (Plain.outer (algebraKernel α) (List.finRange r) rfl v
      (Plain.conjugates (algebraKernel α) (List.finRange r) rfl v))
    (outer_decode v A) s
  simpa only [Plain.driver, finish_eq_toVector, Nat.zero_add] using h

/-- For an observed kernel refining the algebra kernel, the `s`th arithmetic output table of the
driver decodes to `tail A v D s`. -/
theorem observed_driver_decode {k r : ℕ} (M : ObservedKernel α)
    (h : Refines (algebraKernel α) M) (v : Vector α r)
    (A : Vector (Table α r) k) (D : ℕ) (s : Fin (D+1)) :
    decode ((Metered.driver M v A D).arithmetic.value[s]) = tail A v D s := by
  rw [driver_refines (algebraKernel α) M h]
  exact driver_decode v A D s

end Semantics
end Qatlib.Concepts.FinitePrecision.ComputableInput.FiniteTailProgram
