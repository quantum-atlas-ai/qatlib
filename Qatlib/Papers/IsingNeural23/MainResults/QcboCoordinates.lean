/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.IsingNeural23.MainResults.SpaceComplexity
import Qatlib.Concepts.BinaryOptEncode.BitCoordinates
import Mathlib.Data.Finite.Prod
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Papers.IsingNeural23.MainResults

def coordinateDomain (n m B H L N : ℕ) : Fin 12 → Type
  | 0 => Fin n × Fin H
  | 1 => Fin H × Fin ((n * 2 ^ (B + 1)).log2 + 1)
  | 2 => Fin (L - 2) × Fin H × Fin H
  | 3 => Fin m × Fin H × Fin ((2 * H).log2 + 1)
  | 4 => Fin m × Fin ((2 * H).log2 + 1)
  | 5 => Fin N × Fin H × Fin ((n * 2 ^ (B + 2)).log2 + 1)
  | 6 => Fin N × Fin (L - 2) × Fin H × Fin ((2 * H).log2 + 1)
  | 7 => Fin N × Fin H × Fin ((3 * n * 2 ^ B).log2 + 1)
  | 8 => Fin N × Fin (L - 2) × Fin H × Fin ((2 * H).log2 + 1)
  | 9 => Fin N × Fin H × Fin ((3 * n * 2 ^ (B + 1)).log2 + 1)
  | 10 => Fin N × Fin (L - 1) × Fin H
  | _ => Fin N × Fin m × Fin ((4 * H).log2 + 1)

instance coordinateDomain_finite (n m B H L N : ℕ) (k : Fin 12) :
    Finite (coordinateDomain n m B H L N k) := by
  unfold coordinateDomain
  split <;> infer_instance

noncomputable instance coordinateDomain_fintype (n m B H L N : ℕ) (k : Fin 12) :
    Fintype (coordinateDomain n m B H L N k) := Fintype.ofFinite _

def QcboBit (n m B H L N : ℕ) := (k : Fin 12) × coordinateDomain n m B H L N k

noncomputable instance qcboBit_fintype (n m B H L N : ℕ) : Fintype (QcboBit n m B H L N) :=
  inferInstanceAs (Fintype (Sigma (coordinateDomain n m B H L N)))

noncomputable instance qcboBit_decidableEq (n m B H L N : ℕ) :
    DecidableEq (QcboBit n m B H L N) := Classical.decEq _

def indexWFirst (n m B H L N : ℕ) (x : Fin n × Fin H) : QcboBit n m B H L N := ⟨0, x⟩

def indexBFirst (n m B H L N : ℕ) (x : Fin H × Fin ((n * 2 ^ (B + 1)).log2 + 1)) :
    QcboBit n m B H L N := ⟨1, x⟩

def indexWMiddle (n m B H L N : ℕ) (x : Fin (L - 2) × Fin H × Fin H) : QcboBit n m B H L N := ⟨2, x⟩

def indexWLast (n m B H L N : ℕ) (x : Fin m × Fin H × Fin ((2 * H).log2 + 1)) :
    QcboBit n m B H L N := ⟨3, x⟩

def indexBLast (n m B H L N : ℕ) (x : Fin m × Fin ((2 * H).log2 + 1)) : QcboBit n m B H L N :=
    ⟨4, x⟩

def indexSFirst (n m B H L N : ℕ) (x : Fin N × Fin H × Fin ((n * 2 ^ (B + 2)).log2 + 1)) :
    QcboBit n m B H L N := ⟨5, x⟩

def indexSMiddle (n m B H L N : ℕ) (x : Fin N × Fin (L - 2) × Fin H × Fin ((2 * H).log2 + 1)) :
    QcboBit n m B H L N := ⟨6, x⟩

def indexRFirst (n m B H L N : ℕ) (x : Fin N × Fin H × Fin ((3 * n * 2 ^ B).log2 + 1)) :
    QcboBit n m B H L N := ⟨7, x⟩

def indexRMiddle (n m B H L N : ℕ) (x : Fin N × Fin (L - 2) × Fin H × Fin ((2 * H).log2 + 1)) :
    QcboBit n m B H L N := ⟨8, x⟩

def indexTFirst (n m B H L N : ℕ) (x : Fin N × Fin H × Fin ((3 * n * 2 ^ (B + 1)).log2 + 1)) :
    QcboBit n m B H L N := ⟨9, x⟩

def indexAAll (n m B H L N : ℕ) (x : Fin N × Fin (L - 1) × Fin H) : QcboBit n m B H L N := ⟨10, x⟩

def indexYHat (n m B H L N : ℕ) (x : Fin N × Fin m × Fin ((4 * H).log2 + 1)) :
    QcboBit n m B H L N := ⟨11, x⟩

theorem qcboBit_card (n m B H L N : ℕ) :
    Fintype.card (QcboBit n m B H L N) = spinCount n m B H L N := by
  change Fintype.card (Sigma (coordinateDomain n m B H L N)) = _
  rw [Qatlib.Concepts.BinaryOptEncode.BitCoordinates.family_card]
  simp [coordinateDomain, Fin.sum_univ_succ, Fintype.card_eq_nat_card, Nat.card_prod, Nat.card_fin,
      spinCount, -Nat.card_eq_fintype_card]
  ring

theorem qcboBit_bound (n m B H L N : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hB : 1 ≤ B) (hH : 2 ≤ H) (hL : 2 ≤ L) (hN : 1 ≤ N) :
    Fintype.card (QcboBit n m B H L N) ≤
      (40 * (2 * n + 2 * m + B + 2)) * eq10Poly H L N := by
  rw [qcboBit_card]
  exact space_complexity_simplified n m B H L N hn hm hB hH hL hN

theorem qcboSpinAssignment_card (n m B H L N : ℕ) :
    Fintype.card (QcboBit n m B H L N →
      Qatlib.Concepts.BinaryOptEncode.BitCoordinates.Spin) =
        2 ^ spinCount n m B H L N := by
  rw [Qatlib.Concepts.BinaryOptEncode.BitCoordinates.spinAssignment_card,
    qcboBit_card]

end Qatlib.Papers.IsingNeural23.MainResults
