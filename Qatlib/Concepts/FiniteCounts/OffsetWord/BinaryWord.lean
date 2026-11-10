/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FiniteCounts.OffsetWord.UniformRun

set_option autoImplicit false

namespace Qatlib.Concepts.FiniteCounts.OffsetWord

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def binaryValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * binaryValue bs

def binaryWord (P : G) : List Bool → List (Instruction G)
  | [] => []
  | b :: bs => (b, P) :: binaryWord (2 • P) bs

omit [DecidableEq G] in

theorem binaryWord_length (P : G) (bs : List Bool) : (binaryWord P bs).length = bs.length := by
  induction bs generalizing P with
  | nil => rfl
  | cons b bs ih => simp [binaryWord, ih]

omit [DecidableEq G] in

theorem idealRun_append (w v : List (Instruction G)) (a : G) :
    idealRun a (w ++ v) = idealRun (idealRun a w) v := by
  induction w generalizing a with
  | nil => rfl
  | cons s w ih =>
    obtain ⟨c,B⟩ := s
    simp only [List.cons_append, idealRun, ih]

omit [DecidableEq G] in

theorem binaryWord_correct (P a : G) (bs : List Bool) :
    idealRun a (binaryWord P bs) = a + binaryValue bs • P := by
  induction bs generalizing P a with
  | nil => simp [binaryWord, binaryValue, idealRun]
  | cons b bs ih =>
    cases b
    · simp [binaryWord, binaryValue, idealRun, ih, mul_nsmul]
    · simp [binaryWord, binaryValue, idealRun, ih, add_nsmul, mul_nsmul,
        add_assoc]

def doubleWord (P Q : G) (k l : List Bool) : List (Instruction G) :=
  binaryWord P k ++ binaryWord Q l

omit [DecidableEq G] in

theorem doubleWord_correct (P Q a : G) (k l : List Bool) :
    idealRun a (doubleWord P Q k l) =
      a + binaryValue k • P + binaryValue l • Q := by
  rw [doubleWord, idealRun_append, binaryWord_correct, binaryWord_correct]

theorem checked_doubleWord_correct (P Q a z : G) (k l : List Bool)
    (h : checkedRun a (doubleWord P Q k l) = some z) :
    z = a + binaryValue k • P + binaryValue l • Q := by
  rw [← checkedRun_sound _ a z h]
  exact doubleWord_correct P Q a k l

variable [Fintype G]

theorem doubleWord_failure_le (P Q : G) (k l : List Bool)
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a (doubleWord P Q k l) = none}).toReal ≤
      (4 * (k.length + l.length) : ℕ) / (Fintype.card G - 1 : ℕ) := by
  simpa only [doubleWord, List.length_append, binaryWord_length] using
    uniform_failure_le (doubleWord P Q k l) h

theorem source_width_failure_le (P Q : G) (n : ℕ) (k l : Fin (n+1) → Bool)
    (h : (Finset.univ.erase (0 : G)).Nonempty) :
    ((PMF.uniformOfFinset (Finset.univ.erase (0 : G)) h).toOuterMeasure
      {a | checkedRun a (doubleWord P Q (List.ofFn k) (List.ofFn l)) = none}).toReal ≤
      (8 * (n+1) : ℕ) / (Fintype.card G - 1 : ℕ) := by
  have hh := doubleWord_failure_le P Q (List.ofFn k) (List.ofFn l) h
  simpa only [List.length_ofFn, show 4 * (n + 1 + (n + 1)) = 8 * (n + 1) by omega] using hh

end Qatlib.Concepts.FiniteCounts.OffsetWord
