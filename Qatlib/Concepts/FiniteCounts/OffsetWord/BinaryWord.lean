/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FiniteCounts.OffsetWord.UniformRun

/-!
# Binary translation words

This module encodes Boolean lists as least significant bit first natural numbers with
`binaryValue` and as controlled translation words with `binaryWord`. The concatenated
`doubleWord` computes two scalar multiples from a common initial offset.

Correctness of successful checked execution is combined with uniform nonzero-offset failure
bounds. These estimates support the random-offset treatment of exceptional inputs in
elliptic-curve arithmetic described in [RoettelerEtAl2017].

## Main statements

* `binaryWord_correct`: ideal execution adds the encoded scalar multiple.
* `checked_doubleWord_correct`: successful checked execution computes both scalar multiples.
* `source_width_failure_le`: two inputs of width `n + 1` have failure probability at most `8 *
  (n + 1)` divided by the number of nonzero group elements.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The natural number represented by a Boolean list in least significant bit first order. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * binaryValue bs

/-- The controlled translation word whose successive increments are `P`, `2 • P`, and their
iterated doubles. -/
def binaryWord (P : G) : List Bool → List (Instruction G)
  | [] => []
  | b :: bs => (b, P) :: binaryWord (2 • P) bs

omit [DecidableEq G] in

/-- The binary translation word has one instruction for each input bit. -/
theorem binaryWord_length (P : G) (bs : List Bool) : (binaryWord P bs).length = bs.length := by
  induction bs generalizing P with
  | nil => rfl
  | cons b bs ih => simp [binaryWord, ih]

omit [DecidableEq G] in

/-- Ideal execution of a concatenated word equals successive ideal execution of its two parts. -/
theorem idealRun_append (w v : List (Instruction G)) (a : G) :
    idealRun a (w ++ v) = idealRun (idealRun a w) v := by
  induction w generalizing a with
  | nil => rfl
  | cons s w ih =>
    obtain ⟨c,B⟩ := s
    simp only [List.cons_append, idealRun, ih]

omit [DecidableEq G] in

/-- Ideal execution of a binary word adds the scalar multiple encoded by its bits. -/
theorem binaryWord_correct (P a : G) (bs : List Bool) :
    idealRun a (binaryWord P bs) = a + binaryValue bs • P := by
  induction bs generalizing P a with
  | nil => simp [binaryWord, binaryValue, idealRun]
  | cons b bs ih =>
    cases b
    · simp [binaryWord, binaryValue, idealRun, ih, mul_nsmul]
    · simp [binaryWord, binaryValue, idealRun, ih, add_nsmul, mul_nsmul,
        add_assoc]

/-- The concatenation of the binary translation words for `P` and `Q`. -/
def doubleWord (P Q : G) (k l : List Bool) : List (Instruction G) :=
  binaryWord P k ++ binaryWord Q l

omit [DecidableEq G] in

/-- Ideal execution of the double word adds both encoded scalar multiples to the initial offset. -/
theorem doubleWord_correct (P Q a : G) (k l : List Bool) :
    idealRun a (doubleWord P Q k l) =
      a + binaryValue k • P + binaryValue l • Q := by
  rw [doubleWord, idealRun_append, binaryWord_correct, binaryWord_correct]

/-- A successful checked double word returns the initial offset plus both encoded scalar
multiples. -/
theorem checked_doubleWord_correct (P Q a z : G) (k l : List Bool)
    (h : checkedRun a (doubleWord P Q k l) = some z) :
    z = a + binaryValue k • P + binaryValue l • Q := by
  rw [← checkedRun_sound _ a z h]
  exact doubleWord_correct P Q a k l

variable [Fintype G]

/-- For a uniform nonzero offset, the double word fails with probability at most four times the
total bit length divided by the number of nonzero group elements. -/
theorem doubleWord_failure_le (P Q : G) (k l : List Bool)
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a (doubleWord P Q k l) = none}).toReal ≤
      (4 * (k.length + l.length) : ℕ) / (Fintype.card G - 1 : ℕ) := by
  simpa only [doubleWord, List.length_append, binaryWord_length] using
    uniform_failure_le (doubleWord P Q k l) h

/-- For two bit strings of length `n + 1`, the uniform nonzero offset failure probability is at
most `8 * (n + 1)` divided by the number of nonzero group elements. -/
theorem source_width_failure_le (P Q : G) (n : ℕ) (k l : Fin (n+1) → Bool)
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a (doubleWord P Q (List.ofFn k) (List.ofFn l)) = none}).toReal ≤
      (8 * (n+1) : ℕ) / (Fintype.card G - 1 : ℕ) := by
  have hh := doubleWord_failure_le P Q (List.ofFn k) (List.ofFn l) h
  simpa only [List.length_ofFn, show 4 * (n + 1 + (n + 1)) = 8 * (n + 1) by omega] using hh

end Qatlib.Concepts.FiniteCounts.OffsetWord
