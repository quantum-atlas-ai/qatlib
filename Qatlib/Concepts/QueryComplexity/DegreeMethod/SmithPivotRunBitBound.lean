/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.SmithWholePivotRun

/-!
# Bit bounds for binary Smith runs

This module relates binary relation encodings to entry bounds for a counted Smith reduction. It
bounds decoded magnitudes using code lengths, then combines the resulting matrix bound with peak
Euclidean-input bit sizes and a division-count estimate.

The combined statement `frontier1` also identifies the returned reduction with the binary Smith
run and records that it encodes the input and has Smith form. The quantum-algorithmic context
for this integer postprocessing is exemplified by [Shor1997].

## Main statements

* `smithDecodeNat_lt_pow`: a bit-list value is bounded by its encoding length.
* `smithDecodeRelations_entryBound`: total relation bits bound all decoded matrix entries.
* `frontier1`: the binary Euclidean run satisfies entry, bit-size, division-count, and
  Smith-form guarantees.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false


open Qatlib.Concepts.HspRecovery.ReductionCore

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.SmithPivotRunBitBound

open Matrix
open Qatlib.Concepts.IntWordFraming.WordFraming
set_option warningAsError false

/-- Decoding a Boolean list as a natural number yields a value strictly below two to the list
length. -/
theorem smithDecodeNat_lt_pow (bits : List Bool) : smithDecodeNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [smithDecodeNat]
  | cons b bits ih =>
      change Nat.bit b (smithDecodeNat bits) < 2 ^ (bits.length + 1)
      rw [Nat.pow_succ]
      cases b <;> simp [Nat.bit] <;> omega

/-- The magnitude of a decoded signed integer is at most two to the length of its magnitude
code. -/
theorem smithDecodeInteger_natAbs_le_pow (z : SmithIntegerCode) :
    (smithDecodeInteger z).natAbs ≤ 2 ^ z.2.length := by
  have h := Nat.le_of_lt (smithDecodeNat_lt_pow z.2)
  by_cases hz : z.1
  · simpa [smithDecodeInteger, hz] using! h
  · simpa [smithDecodeInteger, hz] using! h

/-- The magnitude-code length of each relation-table entry is bounded by the total relation bit
count. -/
theorem smithRelationBits_entry_length {m n : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) (i : Fin m) (j : Fin n) :
    (rows[i.val][j.val]).2.length ≤ smithRelationBits rows := by
  rw [smithRelationBits]
  calc
    (rows[i.val][j.val]).2.length ≤ 1 + (rows[i.val][j.val]).2.length := by omega
    _ ≤ ∑ j' : Fin n, (1 + (rows[i.val][j'.val]).2.length) :=
      Finset.single_le_sum (f := fun j' : Fin n => 1 + (rows[i.val][j'.val]).2.length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, (1 + (rows[i'.val][j'.val]).2.length) :=
      Finset.single_le_sum
        (f := fun i' : Fin m => ∑ j' : Fin n, (1 + (rows[i'.val][j'.val]).2.length))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Every entry of the decoded relation matrix has magnitude at most two to the relation bit
count. -/
theorem smithDecodeRelations_entryBound {m n : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) :
    MatrixEntryBound (tableMatrix (smithDecodeRelations rows)) (2 ^ smithRelationBits rows) := by
  intro i j
  simp only [tableMatrix, smithDecodeRelations, Vector.getElem_map]
  exact (smithDecodeInteger_natAbs_le_pow _).trans
    (Nat.pow_le_pow_right (by omega) (smithRelationBits_entry_length rows i j))

namespace output2

/-- For binary-encoded relations, the Euclidean Smith run satisfies the stated reduction-entry,
peak-input-bit, and division-count bounds. It agrees with the binary Smith run and returns
an encoding of the input matrix in Smith form. -/
theorem frontier1 {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    let A := tableMatrix (smithDecodeRelations rows)
    let B := rectangularSup (m+n+2) A (2 ^ smithRelationBits rows)
    ReductionEntryBound (smithRunBinaryEuclid rows).1.1.reduction B ∧
      (smithRunBinaryEuclid rows).2.peakPairInputBits ≤ B.size ∧
      (smithRunBinaryEuclid rows).2.quotRemPairs ≤
        (m+n)*(smithRunBinaryEuclid rows).1.2 .pivotFuelAllocated *
          (2*(smithRunBinaryEuclid rows).2.peakPairInputBits+2) ∧
      (smithRunBinaryEuclid rows).1.1 = smithRunBinary rows ∧
      (smithRunBinaryEuclid rows).1.1.reduction.Encodes A ∧
      SmithForm (smithRunBinaryEuclid rows).1.1.reduction.value := by
  (try dsimp only)
  let A := tableMatrix (smithDecodeRelations rows)
  let B := rectangularSup (m+n+2) A (2 ^ smithRelationBits rows)
  have hA : MatrixEntryBound A (2 ^ smithRelationBits rows) := by
    simpa [A] using! smithDecodeRelations_entryBound rows
  have h := smithRectangularEuclid_entryBound (dim := m+n+2) (by omega) A
    (2 ^ smithRelationBits rows) (by omega) hA Nat.one_le_two_pow
  have he : ReductionEntryBound (smithRunBinaryEuclid rows).1.1.reduction B := by
    simpa [smithRunBinaryEuclid, A, B] using! h.1
  have hp : (smithRunBinaryEuclid rows).2.peakPairInputBits ≤ B.size := by
    simpa [smithRunBinaryEuclid, A, B] using! h.2
  have hdiv := smithRunBinaryEuclid_division_bound rows
  have hvalue : (smithRunBinaryEuclid rows).1.1 = smithRunBinary rows := by simp
  have hrect : (smithRectangularEuclid A).1.1 = rectangularSmith A := by simp
  refine ⟨he, hp, hdiv, hvalue, ?_, ?_⟩
  · change (smithRectangularEuclid A).1.1.Encodes A
    rw [hrect]
    exact rectangularSmith_encodes A
  · change SmithForm (smithRectangularEuclid A).1.1.value
    rw [hrect]
    exact rectangularSmith_form A

end output2

end Qatlib.Concepts.QueryComplexity.DegreeMethod.SmithPivotRunBitBound
