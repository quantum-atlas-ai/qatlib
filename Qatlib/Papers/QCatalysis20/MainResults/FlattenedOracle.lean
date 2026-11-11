/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCatalysis20.MainResults.MultiplexedLookup

/-!
# Flattened sparse lookup tables

This module turns valid ragged-table addresses into a finite equivalence and constructs a
bit-vector table by inverse flattening, with zero outside the valid range. Choosing the ceiling
binary logarithm of the entry count supplies sufficient address width for
`source_sparse_lookup`. See [VonBurgEtAl2021].

## Main statements

* `addressIndex_bijective`: Flattening valid ragged-table addresses is bijective onto the finite
  total-entry address space.
* `flattenedTable_correct`: If all table entries fit in the address width, querying a flattened
  valid address returns the corresponding ragged-table entry.
* `source_sparse_lookup`: The five-stage lookup with ceiling-logarithmic address width XORs the
  requested ragged-table entry into the target while restoring the zero workspace and preserving
  the dirty register.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Papers.QCatalysis20.MainResults

/-- Flatten a valid dependent row and within-row address into the finite total-entry address
space. -/
def addressIndex (J : ℕ) (K : ℕ→ℕ) (jk : Σj:Fin J,Fin (K j)) : Fin (totalEntries J K) :=
  multiplexedIndexFin J K jk.1 jk.2 jk.1.isLt

/-- Flattening valid ragged-table addresses is bijective onto the finite total-entry address
space. -/
theorem addressIndex_bijective (J : ℕ) (K : ℕ→ℕ) : Function.Bijective (addressIndex J K) := by
  constructor
  · rintro ⟨j,k⟩ ⟨l,h⟩ he
    have hx:=multiplexedIndex_injective (congrArg Fin.val he) k.isLt h.isLt
    have hj : j=l := Fin.ext hx.1
    subst l
    have hk : k=h := Fin.ext hx.2
    subst h
    rfl
  · intro q
    obtain ⟨j,k,hj,hk,he⟩:=multiplexedIndex_surjective J K q.val q.isLt
    exact ⟨⟨⟨j,hj⟩,⟨k,hk⟩⟩,Fin.ext he⟩

/-- The equivalence between valid ragged-table address pairs and flattened finite addresses. -/
def addressEquiv (J : ℕ) (K : ℕ→ℕ) : (Σj:Fin J,Fin (K j))≃Fin (totalEntries J K) :=
  Equiv.ofBijective (addressIndex J K) (addressIndex_bijective J K)

/-- The bit-vector table obtained by inverse flattening valid addresses and returning zero
outside the table. -/
def flattenedTable {J b : ℕ} (K : ℕ→ℕ) (x : (j:Fin J)→Fin (K j)→BitVec b)
    (a : ℕ) (q : BitVec a) : BitVec b :=
  if h:q.toNat<totalEntries J K then
    let jk:=(addressEquiv J K).symm ⟨q.toNat,h⟩
    x jk.1 jk.2
  else 0#b

/-- If all table entries fit in the address width, querying a flattened valid address returns
the corresponding ragged-table entry. -/
theorem flattenedTable_correct {J a b : ℕ} (K : ℕ→ℕ)
    (x : (j:Fin J)→Fin (K j)→BitVec b) (ha : totalEntries J K≤2^a)
    (j : Fin J) (k : Fin (K j)) :
    flattenedTable K x a (BitVec.ofNat a (multiplexedIndex K j.val k.val))=x j k := by
  have ht:=multiplexedIndex_lt_total j.isLt k.isLt
  have hv: (BitVec.ofNat a (multiplexedIndex K j.val k.val)).toNat=multiplexedIndex K j.val k.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (ht.trans_le ha)]
  unfold flattenedTable
  rw [dif_pos (by rw [hv];exact ht)]
  have he : (⟨(BitVec.ofNat a (multiplexedIndex K j.val k.val)).toNat,by rw [hv];exact ht⟩:
      Fin (totalEntries J K))=addressEquiv J K ⟨j,k⟩ := Fin.ext hv
  rw [he,Equiv.symm_apply_apply]

/-- The total entry count is at most two raised to its ceiling binary logarithm. -/
theorem source_lookup_width (J : ℕ) (K : ℕ→ℕ) :
    totalEntries J K≤2^(Nat.clog 2 (totalEntries J K)) :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mp le_rfl

/-- The five-stage lookup with ceiling-logarithmic address width XORs the requested ragged-table
entry into the target while restoring the zero workspace and preserving the dirty register.
See [VonBurgEtAl2021]. -/
theorem source_sparse_lookup {J b d : ℕ} (K : ℕ→ℕ)
    (x : (j:Fin J)→Fin (K j)→BitVec b) (j : Fin J) (k : Fin (K j))
    (z : BitVec b) (dirty : BitVec d) :
    runLookup (flattenedTable K x (Nat.clog 2 (totalEntries J K)))
      (⟨j,k⟩,0#(Nat.clog 2 (totalEntries J K)),z,dirty)=
      (⟨j,k⟩,0#(Nat.clog 2 (totalEntries J K)),z ^^^ x j k,dirty) :=
  actual_five_stage_lookup _ x (flattenedTable_correct K x (source_lookup_width J K)) j k z dirty

end Qatlib.Papers.QCatalysis20.MainResults
