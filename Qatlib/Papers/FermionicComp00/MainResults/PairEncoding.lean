/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Pair encoding of registers

`sourcePairEncoding` duplicates each occupation bit into an adjacent equal pair. The module
proves that decoding recovers the input and that the encoding is a bijection onto
`sourcePairSubspace`. It also defines encoding matrices, placement maps, and `pairLift` for
operators supported on the equal-pair basis configurations.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `source_pair_decoding_encoding`: decoding is a left inverse.
* `source_pair_encoding_surjective`: every equal-pair configuration is encoded.
* `pairLift`: lifts a two-bit matrix to the four-bit equal-pair sector.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped Classical BigOperators

namespace Qatlib.Papers.FermionicComp00.MainResults.PairEncoding

variable {m : ℕ}

/-- The register encoding that repeats each input bit in two adjacent positions. -/
def sourcePairEncoding (m : ℕ) (x : Reg m) : Reg (2 * m) :=
  fun t => x ⟨t.val / 2, Nat.div_lt_of_lt_mul t.isLt⟩

/-- Decoding by reading the even-indexed bit of each adjacent pair. -/
def sourcePairDecoding (m : ℕ) (y : Reg (2 * m)) : Reg m :=
  fun j => y ⟨2 * j.val, Nat.mul_lt_mul_of_pos_left j.isLt (by norm_num)⟩

/-- The set of register configurations whose two bits in every adjacent pair agree. -/
def sourcePairSubspace (m : ℕ) : Set (Reg (2 * m)) :=
  {y | ∀ j : Fin m,
    y ⟨2 * j.val, Nat.mul_lt_mul_of_pos_left j.isLt (by norm_num)⟩ =
      y ⟨2 * j.val + 1, by have := j.isLt; omega⟩}

/-- Every pair-encoded register has equal bits within each adjacent pair. -/
theorem source_pair_encoding_mem (x : Reg m) :
    sourcePairEncoding m x ∈ sourcePairSubspace m := by
  intro j
  simp only [sourcePairEncoding]
  refine congrArg x (Fin.ext ?_)
  show 2 * (j : ℕ) / 2 = (2 * (j : ℕ) + 1) / 2
  rw [Nat.mul_div_right _ (by norm_num)]
  omega

/-- Decoding a pair-encoded register recovers the original register. -/
theorem source_pair_decoding_encoding (x : Reg m) :
    sourcePairDecoding m (sourcePairEncoding m x) = x := by
  funext j
  simp [sourcePairDecoding, sourcePairEncoding]

/-- The pair encoding is injective. See [BravyiKitaev2002]. -/
theorem source_pair_encoding_injective (m : ℕ) : Function.Injective (sourcePairEncoding m) := by
  intro x y h
  calc x = sourcePairDecoding m (sourcePairEncoding m x) :=
        (source_pair_decoding_encoding (m := m) x).symm
    _ = sourcePairDecoding m (sourcePairEncoding m y) := by rw [h]
    _ = y := source_pair_decoding_encoding (m := m) y

/-- Every configuration with equal adjacent pairs is the encoding of some input register. See
[BravyiKitaev2002]. -/
theorem source_pair_encoding_surjective (m : ℕ) :
    ∀ y ∈ sourcePairSubspace m, ∃ x, sourcePairEncoding m x = y := by
  intro y hy
  refine ⟨sourcePairDecoding m y, ?_⟩
  funext t
  simp only [sourcePairEncoding, sourcePairDecoding]
  have hlt : t.val / 2 < m := Nat.div_lt_of_lt_mul t.isLt
  have hdm : 2 * (t.val / 2) + t.val % 2 = t.val := Nat.div_add_mod t.val 2
  rcases Nat.mod_two_eq_zero_or_one t.val with h | h
  · have hidx : (⟨2 * (t.val / 2),
        Nat.mul_lt_mul_of_pos_left hlt (by norm_num)⟩ : Fin (2 * m)) = t := by
      refine Fin.ext ?_
      show 2 * (t.val / 2) = t.val
      omega
    rw [hidx]
  · have hyj := hy ⟨t.val / 2, hlt⟩
    have hidx : (⟨2 * (t.val / 2) + 1, by have := t.isLt; omega⟩ : Fin (2 * m)) = t := by
      refine Fin.ext ?_
      show 2 * (t.val / 2) + 1 = t.val
      omega
    calc y ⟨2 * (t.val / 2), Nat.mul_lt_mul_of_pos_left hlt (by norm_num)⟩
        = y ⟨2 * (t.val / 2) + 1, by have := t.isLt; omega⟩ := hyj
      _ = y t := by rw [hidx]

/-- The matrix sending each computational basis vector indexed by `x` to the basis vector
indexed by `J x`. -/
def encodingMatrix {m q : ℕ} (J : Reg m → Reg q) : Matrix (Reg q) (Reg m) ℂ :=
  Matrix.of fun y x => if y = J x then 1 else 0

/-- The intertwining relation expressing that the encoded operator acts compatibly with the
original operator through `encodingMatrix J`. -/
def Represents {m q : ℕ} (J : Reg m → Reg q) (U : Matrix (Reg m) (Reg m) ℂ)
    (U' : Matrix (Reg q) (Reg q) ℂ) : Prop :=
  U' * encodingMatrix J = encodingMatrix J * U

/-- The matrix obtained by applying `G` at the selected positions and requiring all other
register bits to remain unchanged. -/
def applyAt {m p : ℕ} (pos : Fin p → Fin m) (G : Matrix (Reg p) (Reg p) ℂ) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x => G (fun t => y (pos t)) (fun t => x (pos t)) *
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ∉ Finset.univ.image pos)),
      (if y s = x s then (1 : ℂ) else 0)

/-- The position map sending the first two-register index to `j` and the second to `k`. -/
def pairPos2 {m : ℕ} (j k : Fin m) : Fin 2 → Fin m :=
  fun t => if t = 0 then j else k

/-- The position map selecting the two adjacent physical bits for `j`, followed by those for
`k`. -/
def pairPos4 {m : ℕ} (j k : Fin m) : Fin 4 → Fin (2 * m) :=
  fun t =>
    if t = 0 then ⟨2 * j.val, Nat.mul_lt_mul_of_pos_left j.isLt (by norm_num)⟩
    else if t = 1 then ⟨2 * j.val + 1, by have := j.isLt; omega⟩
    else if t = 2 then ⟨2 * k.val, Nat.mul_lt_mul_of_pos_left k.isLt (by norm_num)⟩
    else ⟨2 * k.val + 1, by have := k.isLt; omega⟩

/-- The two-bit register obtained by reading positions 0 and 2 of a four-bit register. -/
def pairClass4 (y : Reg 4) : Reg 2 :=
  fun t => if t = 0 then y 0 else y 2

/-- The four-bit matrix equal to `X` on equal-pair configurations after decoding, with zero
entries whenever either configuration fails the pair constraints. -/
def pairLift (X : Matrix (Reg 2) (Reg 2) ℂ) : Matrix (Reg 4) (Reg 4) ℂ :=
  Matrix.of fun y x =>
    if y 0 = y 1 ∧ y 2 = y 3 then
      (if x 0 = x 1 ∧ x 2 = x 3 then X (pairClass4 y) (pairClass4 x) else 0)
    else 0

end Qatlib.Papers.FermionicComp00.MainResults.PairEncoding
