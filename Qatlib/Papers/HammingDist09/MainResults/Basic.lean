/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Card
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hamming-distance concepts and learning matrices

This module develops the binary-word model for the Hamming-distance concepts studied in
[MeyerPommersheim2009]. It defines `wt`, `dist`, `concept`, and the parity-dependent
transformation `hatX`, then proves the phase identities and character sums used to compute the
learning algorithm's amplitudes.

The later results count `conceptClass`, relate the Gram matrices of `learningMatrix` to Hamming
distance, and constrain distance-dependent Hadamard matrices. The module also defines the
elementary measurement predicates and average success expression used by the measurement
analysis.

## Main statements

* `lemma_3_1_card_ne_one`: counts concepts when the length is not one modulo four.
* `lemma_3_1_card_mod_one`: counts concepts when the length is one modulo four.
* `theorem_3_2`: computes the normalized amplitudes for even word length.
* `theorem_4_2`: rules out distance-dependent Hadamard learning matrices in odd length greater
  than one.
* `corollary_4_3`: represents the remaining Hadamard distance functions by shifted second binary
  digits.

## References

* [Meyer and Pommersheim, 2009][MeyerPommersheim2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HammingDist09.MainResults

/-- Binary words of length `n`, represented as functions from `Fin n` to `ZMod 2`. -/
abbrev Word (n : ℕ) := Fin n → ZMod 2

/-- The Hamming weight of a binary word, counting its nonzero coordinates. -/
def wt {n : ℕ} (x : Word n) : ℕ := ∑ i, if x i = 0 then 0 else 1

/-- The Hamming distance between two binary words, counting coordinates at which they differ. -/
def dist {n : ℕ} (a x : Word n) : ℕ := ∑ i, if a i = x i then 0 else 1

/-- The number of coordinates at which both binary words equal one. -/
def dotCount {n : ℕ} (a x : Word n) : ℕ := ∑ i, if a i = 1 ∧ x i = 1 then 1 else 0

/-- The standard bilinear dot product of binary words with values in `ZMod 2`. -/
def dot {n : ℕ} (a x : Word n) : ZMod 2 := ∑ i, a i * x i

/-- The second least significant binary digit of `d`, given by `(d / 2) % 2`. -/
def b1 (d : ℕ) : ℕ := (d / 2) % 2

/-- The bitwise complement of a binary word, obtained by adding one in each coordinate. -/
def compl {n : ℕ} (a : Word n) : Word n := fun i => a i + 1

/-- The word `x` when its Hamming weight is even, and its bitwise complement otherwise. -/
def hatX {n : ℕ} (x : Word n) : Word n := if wt x % 2 = 0 then x else compl x

/-- The integer sign `(-1) ^ (d / 2)` associated with the second binary digit of `d`. -/
def sign (d : ℕ) : ℤ := (-1) ^ (d / 2)

/-- The Boolean function returning the second binary digit of the Hamming distance from `a`. -/
def concept {n : ℕ} (a : Word n) : Word n → ZMod 2 := fun x => (b1 (dist a x) : ZMod 2)

/-- The set of Boolean functions obtained as `concept a` for binary words `a` of length `n`. -/
def conceptClass (n : ℕ) : Set (Word n → ZMod 2) := Set.range (concept (n := n))

/-- The binary word with every coordinate equal to one. -/
def oneWord {n : ℕ} : Word n := fun _ => 1

/-- The binary word whose only nonzero coordinate is `i`. -/
def unit {n : ℕ} (i : Fin n) : Word n := Pi.single i 1

/-- Every element of `ZMod 2` equals either zero or one. -/
lemma zmod2_eq_zero_or_one (u : ZMod 2) : u = 0 ∨ u = 1 := by
  have hlt : u.val < 2 := ZMod.val_lt u
  have hcast : ((u.val : ℕ) : ZMod 2) = u := ZMod.natCast_zmod_val u
  interval_cases u.val
  · left; rw [← hcast]; norm_num
  · right; rw [← hcast]; norm_num

/-- Adding an element of `ZMod 2` to itself gives zero. -/
lemma zmod2_add_self (u : ZMod 2) : u + u = 0 := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;> decide

/-- The sum of the indicator of a predicate on a finite type equals the cardinality of its
satisfying elements, cast into the target monoid. -/
lemma sum_ite_one_eq_card {ι R : Type*} [Fintype ι] [AddCommMonoidWithOne R]
    (p : ι → Prop) [DecidablePred p] :
    (∑ i, if p i then (1 : R) else 0) = ((Finset.univ.filter p).card : R) := by
  rw [← Finset.natCast_card_filter (s := Finset.univ) (p := p)]

/-- The overlap count equals the cardinality of the coordinates at which both words equal one. -/
lemma dotCount_eq_card {n : ℕ} (a x : Word n) :
    dotCount a x = (Finset.univ.filter (fun i => a i = 1 ∧ x i = 1)).card := by
  simp only [dotCount]
  exact sum_ite_one_eq_card _

/-- The product of two binary elements is one exactly when both factors are one, and zero
otherwise. -/
lemma mul_eq_indicator (u v : ZMod 2) :
    u * v = if u = 1 ∧ v = 1 then (1 : ZMod 2) else 0 := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl <;> norm_num

/-- The binary dot product is the overlap count reduced modulo two. -/
lemma dot_eq_dotCount {n : ℕ} (a x : Word n) : dot a x = (dotCount a x : ZMod 2) := by
  have h : dot a x =
      ((Finset.univ.filter (fun i => a i = 1 ∧ x i = 1)).card : ZMod 2) := by
    simp only [dot]
    rw [show (∑ i, a i * x i) =
        ∑ i, (if a i = 1 ∧ x i = 1 then (1 : ZMod 2) else 0) from
      Finset.sum_congr rfl fun i _ => mul_eq_indicator (a i) (x i)]
    exact sum_ite_one_eq_card _
  rw [h, dotCount_eq_card]

/-- The sum of the coordinates of a binary word equals its Hamming weight reduced modulo two. -/
lemma sum_eq_wt {n : ℕ} (a : Word n) : (∑ i, a i) = (wt a : ZMod 2) := by
  have hsum : (∑ i, a i) = ∑ i, (if a i = 1 then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rcases zmod2_eq_zero_or_one (a i) with h | h <;> rw [h] <;> norm_num
  have hwtNat : wt a = (Finset.univ.filter (fun i => a i = 1)).card := by
    have h : wt a = ∑ i, (if a i = 1 then (1 : ℕ) else 0) := by
      simp only [wt]
      apply Finset.sum_congr rfl
      intro i _
      rcases zmod2_eq_zero_or_one (a i) with h | h <;> rw [h] <;> norm_num
    rw [h]
    exact sum_ite_one_eq_card _
  rw [hsum, sum_ite_one_eq_card, hwtNat]

/-- Bitwise complementation equals addition of the all-ones word. -/
lemma compl_eq_add_one {n : ℕ} (x : Word n) : compl x = x + oneWord := by
  funext i
  simp [compl, oneWord, Pi.add_apply]

/-- The binary dot product is additive in its second argument. -/
lemma dot_add_right {n : ℕ} (a x y : Word n) : dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The dot product with the all-ones word equals the Hamming weight modulo two. -/
lemma dot_oneWord {n : ℕ} (a : Word n) : dot a oneWord = (wt a : ZMod 2) := by
  simp only [dot, oneWord, mul_one]
  exact sum_eq_wt a

/-- The Hamming weight of a word is at most its length. -/
lemma wt_le {n : ℕ} (x : Word n) : wt x ≤ n := by
  rw [wt]
  calc ∑ i : Fin n, (if x i = 0 then 0 else 1) ≤ ∑ _i : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro i _
        split <;> norm_num
    _ = n := by simp

/-- The Hamming distance between words is at most their common length. -/
lemma dist_le {n : ℕ} (a x : Word n) : dist a x ≤ n := by
  rw [dist]
  calc ∑ i : Fin n, (if a i = x i then 0 else 1) ≤ ∑ _i : Fin n, 1 := by
        apply Finset.sum_le_sum
        intro i _
        split <;> norm_num
    _ = n := by simp

/-- Two binary elements differ exactly when their sum is nonzero, expressed as equality of their
distance indicators. -/
lemma dist_indicator (u v : ZMod 2) :
    (if u = v then 0 else 1) = (if u + v = 0 then 0 else 1) := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl <;> decide

/-- The Hamming distance between binary words equals the weight of their sum. -/
lemma dist_eq_wt_add {n : ℕ} (a b : Word n) : dist a b = wt (a + b) := by
  simp only [dist, wt]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Pi.add_apply] using dist_indicator (a i) (b i)

/-- A natural number with remainder zero modulo two casts to zero in `ZMod 2`. -/
lemma natCast_eq_zero_of_mod_two_eq_zero {d : ℕ} (h : d % 2 = 0) :
    (d : ZMod 2) = 0 := by
  have hd : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
  rw [hd, h, Nat.add_zero, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- A natural number with remainder one modulo two casts to one in `ZMod 2`. -/
lemma natCast_eq_one_of_mod_two_eq_one {d : ℕ} (h : d % 2 = 1) :
    (d : ZMod 2) = 1 := by
  have hd : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
  rw [hd, h, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]
  norm_num

/-- Reducing a natural number modulo two does not change its cast into `ZMod 2`. -/
lemma natCast_mod_two (d : ℕ) : ((d % 2 : ℕ) : ZMod 2) = (d : ZMod 2) := by
  have hd : d = 2 * (d / 2) + d % 2 := (Nat.div_add_mod d 2).symm
  conv_rhs => rw [hd]
  rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add]

/-- The sum of the two Hamming weights equals their Hamming distance plus twice their overlap
count. -/
lemma wt_add_wt_eq_dist_add {n : ℕ} (a x : Word n) :
    wt a + wt x = dist a x + 2 * dotCount a x := by
  simp only [wt, dist, dotCount]
  rw [← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases zmod2_eq_zero_or_one (a i) with ha | ha <;>
    rcases zmod2_eq_zero_or_one (x i) with hx | hx <;>
      rw [ha, hx] <;> norm_num

/-- For two binary elements, the distance indicators before and after complementing the first
element sum to one. -/
lemma compl_indicator (u v : ZMod 2) :
    (if u + 1 = v then 0 else 1) + (if u = v then 0 else 1) = 1 := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl <;> decide

/-- The distances from a word and its complement to a fixed word sum to the word length. -/
lemma dist_compl_add {n : ℕ} (a x : Word n) : dist (compl a) x + dist a x = n := by
  have h : ∀ i : Fin n,
      (if compl a i = x i then 0 else 1) + (if a i = x i then 0 else 1) = 1 := by
    intro i
    have := compl_indicator (a i) (x i)
    simpa only [compl] using! this
  calc dist (compl a) x + dist a x
      = ∑ i, ((if compl a i = x i then 0 else 1) + (if a i = x i then 0 else 1)) := by
        simp only [dist, Finset.sum_add_distrib]
    _ = ∑ _i : Fin n, 1 := Finset.sum_congr rfl (fun i _ => h i)
    _ = n := by simp

/-- Complementing the second argument adds the weight of the first argument modulo two to the
binary dot product. -/
lemma dot_compl {n : ℕ} (a x : Word n) :
    dot a (compl x) = dot a x + (wt a : ZMod 2) := by
  rw [compl_eq_add_one, dot_add_right, dot_oneWord]

/-- The dot product with `hatX x` equals the original dot product plus the product of the two
weight parities. [MeyerPommersheim2009]. -/
theorem lemma_3_3 {n : ℕ} (a x : Word n) :
    dot a x + (wt a : ZMod 2) * (wt x : ZMod 2) = dot a (hatX x) := by
  unfold hatX
  split_ifs with hx
  · have hx0 : (wt x : ZMod 2) = 0 := natCast_eq_zero_of_mod_two_eq_zero hx
    rw [hx0, mul_zero, add_zero]
  · have hx1 : (wt x : ZMod 2) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (wt x) with h | h
      · exact absurd h hx
      · exact natCast_eq_one_of_mod_two_eq_one h
    rw [hx1, mul_one, dot_compl]

/-- The integer half of a sum equals the sum of the integer halves plus the product of the two
remainders modulo two. -/
lemma half_add (A X : ℕ) :
    (A + X) / 2 = A / 2 + X / 2 + (A % 2) * (X % 2) := by
  have hA : A = 2 * (A / 2) + A % 2 := (Nat.div_add_mod A 2).symm
  have hX : X = 2 * (X / 2) + X % 2 := (Nat.div_add_mod X 2).symm
  have hbA : A % 2 = 0 ∨ A % 2 = 1 := Nat.mod_two_eq_zero_or_one A
  have hbX : X % 2 = 0 ∨ X % 2 = 1 := Nat.mod_two_eq_zero_or_one X
  rcases hbA with h1 | h1 <;> rcases hbX with h2 | h2 <;>
    simp only [h1, h2, mul_zero, mul_one] <;> omega

/-- If `A + X = D + 2 * C`, then the integer half of `A + X` equals the integer half of `D` plus
`C`. -/
lemma half_of_add_two_mul {A X D C : ℕ} (h : A + X = D + 2 * C) :
    (A + X) / 2 = D / 2 + C := by
  omega

/-- Modulo two, half the Hamming distance equals the sum of the half-weights and the dot product
with `hatX x`. -/
theorem half_dist_eq {n : ℕ} (a x : Word n) :
    ((dist a x / 2 : ℕ) : ZMod 2)
      = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2) + dot a (hatX x) := by
  have hcount : wt a + wt x = dist a x + 2 * dotCount a x := wt_add_wt_eq_dist_add a x
  have hD : (wt a + wt x) / 2 = dist a x / 2 + dotCount a x := half_of_add_two_mul hcount
  have hAX : (wt a + wt x) / 2 = wt a / 2 + wt x / 2 + (wt a % 2) * (wt x % 2) :=
    half_add (wt a) (wt x)
  have hkeyNat : dist a x / 2 + dotCount a x =
      wt a / 2 + wt x / 2 + (wt a % 2) * (wt x % 2) := by
    rw [← hD, hAX]
  have hcast : ((dist a x / 2 : ℕ) : ZMod 2) + (dot a x : ZMod 2)
      = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2)
        + (wt a : ZMod 2) * (wt x : ZMod 2) := by
    have h := congrArg (fun k : ℕ => (k : ZMod 2)) hkeyNat
    push_cast at h
    rw [dot_eq_dotCount]
    rw [natCast_mod_two, natCast_mod_two] at h
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  have hneg : (dot a x : ZMod 2) + dot a x = 0 := zmod2_add_self (dot a x)
  have hmove : ((dist a x / 2 : ℕ) : ZMod 2)
      = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2)
        + (wt a : ZMod 2) * (wt x : ZMod 2) + dot a x := by
    calc ((dist a x / 2 : ℕ) : ZMod 2)
        = ((dist a x / 2 : ℕ) : ZMod 2) + dot a x + dot a x := by
          rw [add_assoc, hneg, add_zero]
      _ = (((dist a x / 2 : ℕ) : ZMod 2) + dot a x) + dot a x := by rw [add_assoc]
      _ = (((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2)
            + (wt a : ZMod 2) * (wt x : ZMod 2)) + dot a x := by rw [hcast]
      _ = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2)
            + (wt a : ZMod 2) * (wt x : ZMod 2) + dot a x := by rw [add_assoc]
  calc ((dist a x / 2 : ℕ) : ZMod 2)
      = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2)
          + (dot a x + (wt a : ZMod 2) * (wt x : ZMod 2)) := by
        rw [hmove, add_comm (dot a x), add_assoc]
    _ = ((wt a / 2 : ℕ) : ZMod 2) + ((wt x / 2 : ℕ) : ZMod 2) + dot a (hatX x) := by
        rw [lemma_3_3]

/-- Natural exponents with equal casts into `ZMod 2` give equal integer powers of minus one. -/
lemma neg_one_pow_eq_of_cast_eq {m k : ℕ} (h : (m : ZMod 2) = (k : ZMod 2)) :
    (-1 : ℤ) ^ m = (-1 : ℤ) ^ k := by
  have hm : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
  have hk : k = 2 * (k / 2) + k % 2 := (Nat.div_add_mod k 2).symm
  have hme : Even (2 * (m / 2)) := ⟨m / 2, by ring⟩
  have hke : Even (2 * (k / 2)) := ⟨k / 2, by ring⟩
  rw [hm, hk, pow_add, pow_add, hme.neg_one_pow, hke.neg_one_pow, one_mul, one_mul]
  have hmod : m % 2 = k % 2 := by
    have h1 : ((m % 2 : ℕ) : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
      rw [natCast_mod_two, natCast_mod_two]
      exact h
    have hm2 : m % 2 < 2 := Nat.mod_lt m (by norm_num)
    have hk2 : k % 2 < 2 := Nat.mod_lt k (by norm_num)
    have h2 := (ZMod.natCast_eq_natCast_iff' (m % 2) (k % 2) 2).mp h1
    rwa [Nat.mod_eq_of_lt hm2, Nat.mod_eq_of_lt hk2] at h2
  rw [hmod]

/-- The sign of a Hamming distance factors into the signs of the two weights and the binary
character determined by `dot a (hatX x)`. [MeyerPommersheim2009]. -/
theorem lemma_3_4 {n : ℕ} (a x : Word n) :
    sign (dist a x) =
      sign (wt a) * sign (wt x) * (-1 : ℤ) ^ (dot a (hatX x)).val := by
  have hcast : (((wt a / 2 + wt x / 2 + (dot a (hatX x)).val : ℕ) : ZMod 2))
      = ((dist a x / 2 : ℕ) : ZMod 2) := by
    rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]
    exact (half_dist_eq a x).symm
  have hsign := neg_one_pow_eq_of_cast_eq hcast
  simp only [sign]
  rw [← hsign, pow_add, pow_add]

/-- The weight of the all-ones word is its length. -/
lemma wt_oneWord {n : ℕ} : wt (oneWord (n := n)) = n := by
  simp [wt, oneWord]

/-- The Hamming distance from a word to itself is zero. -/
lemma dist_self {n : ℕ} (a : Word n) : dist a a = 0 := by
  simp [dist]

/-- Hamming distance is symmetric. -/
lemma dist_comm {n : ℕ} (a b : Word n) : dist a b = dist b a := by
  simp [dist, eq_comm]

/-- The Hamming distance from a word to its complement is its length. -/
lemma dist_compl_self {n : ℕ} (a : Word n) : dist a (compl a) = n := by
  rw [dist_eq_wt_add]
  have h : a + compl a = oneWord := by
    funext i
    show a i + compl a i = (1 : ZMod 2)
    rw [compl]
    rcases zmod2_eq_zero_or_one (a i) with hi | hi <;> rw [hi] <;> decide
  rw [h, wt_oneWord]

/-- The dot product with the coordinate word `unit i` extracts the `i`th coordinate. -/
lemma dot_unit {n : ℕ} (b : Word n) (i : Fin n) : dot b (unit i) = b i := by
  rw [dot, Fintype.sum_eq_single i]
  · simp [unit]
  · intro j hj
    simp [unit, Pi.single_eq_of_ne hj]

/-- The sum of two elements of `ZMod 2` is zero exactly when they are equal. -/
lemma zmod2_add_eq_zero_iff (u v : ZMod 2) : u + v = 0 ↔ u = v := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl <;> decide

/-- Two distinct elements of `ZMod 2` sum to one. -/
lemma zmod2_add_eq_one_of_ne {u v : ZMod 2} (h : u ≠ v) : u + v = 1 := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl <;> simp_all

/-- A coordinate word has Hamming weight one. -/
lemma wt_unit {n : ℕ} (i : Fin n) : wt (unit i) = 1 := by
  unfold wt
  rw [Fintype.sum_eq_single i]
  · simp [unit]
  · intro j hj
    simp [unit, Pi.single_eq_of_ne hj]

/-- Flipping a zero coordinate increases the Hamming weight by one. -/
lemma wt_add_unit_zero {n : ℕ} (v : Word n) (i : Fin n) (h : v i = 0) :
    wt (v + unit i) = wt v + 1 := by
  have hsum : (∑ k ∈ Finset.univ.erase i, (if (v + unit i) k = 0 then 0 else 1))
      = ∑ k ∈ Finset.univ.erase i, (if v k = 0 then 0 else 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkne : k ≠ i := Finset.ne_of_mem_erase hk
    have : (v + unit i) k = v k := by
      rw [Pi.add_apply, unit, Pi.single_eq_of_ne hkne, add_zero]
    rw [this]
  have hi : (if (v + unit i) i = 0 then 0 else 1) = 1 := by
    have hvi : (v + unit i) i = 1 := by
      rw [Pi.add_apply, show unit i i = 1 from by simp [unit], h, zero_add]
    rw [hvi]; decide
  have hi0 : (if v i = 0 then 0 else 1) = 0 := by rw [h]; decide
  unfold wt
  rw [← Finset.add_sum_erase (Finset.univ)
        (fun k => if (v + unit i) k = 0 then 0 else 1) (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (Finset.univ)
        (fun k => if v k = 0 then 0 else 1) (Finset.mem_univ i)]
  rw [hsum, hi, hi0]
  omega

/-- Flipping a coordinate equal to one decreases the Hamming weight by one. -/
lemma wt_add_unit_one {n : ℕ} (v : Word n) (i : Fin n) (h : v i = 1) :
    wt (v + unit i) + 1 = wt v := by
  have hsum : (∑ k ∈ Finset.univ.erase i, (if (v + unit i) k = 0 then 0 else 1))
      = ∑ k ∈ Finset.univ.erase i, (if v k = 0 then 0 else 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkne : k ≠ i := Finset.ne_of_mem_erase hk
    have : (v + unit i) k = v k := by
      rw [Pi.add_apply, unit, Pi.single_eq_of_ne hkne, add_zero]
    rw [this]
  have hi : (if (v + unit i) i = 0 then 0 else 1) = 0 := by
    have hvi : (v + unit i) i = 0 := by
      rw [Pi.add_apply, show unit i i = 1 from by simp [unit], h]
      decide
    rw [hvi]; decide
  have hi0 : (if v i = 0 then 0 else 1) = 1 := by rw [h]; decide
  unfold wt
  rw [← Finset.add_sum_erase (Finset.univ)
        (fun k => if (v + unit i) k = 0 then 0 else 1) (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase (Finset.univ)
        (fun k => if v k = 0 then 0 else 1) (Finset.mem_univ i)]
  rw [hsum, hi, hi0]
  omega

/-- Flipping a coordinate where two words agree increases their Hamming distance by one. -/
lemma dist_add_unit_eq_succ {n : ℕ} (a b : Word n) (i : Fin n) (h : a i = b i) :
    dist b (a + unit i) = dist a b + 1 := by
  rw [dist_eq_wt_add, dist_eq_wt_add]
  have habel : b + (a + unit i) = (a + b) + unit i := by abel
  rw [habel]
  have hv : (a + b) i = 0 := by
    rw [Pi.add_apply, h]
    exact zmod2_add_self (b i)
  exact wt_add_unit_zero (a + b) i hv

/-- Flipping a coordinate where two words differ decreases their Hamming distance by one. -/
lemma dist_add_unit_eq_pred {n : ℕ} (a b : Word n) (i : Fin n) (h : a i ≠ b i) :
    dist b (a + unit i) + 1 = dist a b := by
  rw [dist_eq_wt_add, dist_eq_wt_add]
  have habel : b + (a + unit i) = (a + b) + unit i := by abel
  rw [habel]
  have hv : (a + b) i = 1 := by
    rw [Pi.add_apply]
    exact zmod2_add_eq_one_of_ne (by simpa [eq_comm] using h)
  exact wt_add_unit_one (a + b) i hv

/-- The second binary digit of a natural number is its remainder modulo four divided by two. -/
lemma b1_eq_mod_four (d : ℕ) : b1 d = (d % 4) / 2 := by
  unfold b1
  omega

/-- The second binary digit is zero exactly for remainders zero or one modulo four. -/
lemma b1_eq_zero_iff (d : ℕ) : b1 d = 0 ↔ d % 4 = 0 ∨ d % 4 = 1 := by
  rw [b1_eq_mod_four]
  have hlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
  omega

/-- The second binary digit is one exactly for remainders two or three modulo four. -/
lemma b1_eq_one_iff (d : ℕ) : b1 d = 1 ↔ d % 4 = 2 ∨ d % 4 = 3 := by
  rw [b1_eq_mod_four]
  have hlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
  omega

/-- When `n % 4 = 1` and `d ≤ n`, subtracting `d` from `n` preserves the second binary digit of
`d`. -/
lemma b1_sub_of_mod_four_one {n d : ℕ} (hn : n % 4 = 1) (hd : d ≤ n) :
    b1 (n - d) = b1 d := by
  rw [b1_eq_mod_four, b1_eq_mod_four]
  have hlt : d % 4 < 4 := Nat.mod_lt d (by norm_num)
  have hsub : (n - d) % 4 = (5 - d % 4) % 4 := by omega
  rw [hsub]
  omega

/-- The predecessor of a positive multiple of four has second binary digit one. -/
lemma b1_pred_of_mod_four_zero {d : ℕ} (hd : 0 < d) (h : d % 4 = 0) :
    b1 (d - 1) = 1 := by
  rw [b1_eq_mod_four]
  have h4 : (d - 1) % 4 = 3 := by omega
  rw [h4]

/-- Distinct binary words differ at some coordinate. -/
lemma exists_ne_of_ne {n : ℕ} {a b : Word n} (h : a ≠ b) : ∃ i, a i ≠ b i := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  exact h (funext hc)

/-- Distinct binary words have positive Hamming distance. -/
lemma dist_pos_of_ne {n : ℕ} {a b : Word n} (h : a ≠ b) : 0 < dist a b := by
  obtain ⟨i, hi⟩ := exists_ne_of_ne h
  have hle : (if a i = b i then 0 else 1) ≤ dist a b := by
    rw [dist, ← Finset.add_sum_erase (Finset.univ)
      (fun k => if a k = b k then 0 else 1) (Finset.mem_univ i)]
    have hfi : (if a i = b i then 0 else 1) = 1 := by simp [hi]
    rw [hfi]
    exact Nat.le_add_right 1 _
  simp [hi] at hle
  exact hle

/-- Natural numbers less than two are equal if their casts into `ZMod 2` are equal. -/
lemma b1_eq_of_cast_eq {m k : ℕ} (h : (m : ZMod 2) = (k : ZMod 2))
    (hm : m < 2) (hk : k < 2) : m = k := by
  have h2 := (ZMod.natCast_eq_natCast_iff' m k 2).mp h
  rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hk] at h2

/-- The second binary digit is strictly less than two. -/
lemma b1_lt_two (d : ℕ) : b1 d < 2 := Nat.mod_lt _ (by norm_num)

/-- Distinct words defining the same concept must be complements, and their length is congruent
to one modulo four. -/
theorem concept_eq_of_ne {n : ℕ} {a a' : Word n}
    (hf : concept a = concept a') (hne : a ≠ a') :
    n % 4 = 1 ∧ a' = compl a := by
  have hf' : ∀ x, b1 (dist a x) = b1 (dist a' x) := by
    intro x
    have hx := congrFun hf x
    exact b1_eq_of_cast_eq hx (b1_lt_two _) (b1_lt_two _)
  set d := dist a a' with hd
  have hd0 : b1 d = 0 := by
    have h0 := hf' a
    have hdist : dist a' a = d := by rw [dist_comm, hd]
    rw [dist_self, hdist] at h0
    rw [← h0]
    decide
  obtain ⟨i, hi⟩ := exists_ne_of_ne hne
  have hd1 : b1 (d - 1) = 0 := by
    have h1 := hf' (a + unit i)
    have hdistA : dist a (a + unit i) = 1 := by
      rw [dist_eq_wt_add]
      have hz : a + (a + unit i) = unit i := by
        funext k
        rw [Pi.add_apply, Pi.add_apply, ← add_assoc, zmod2_add_self, zero_add]
      rw [hz, wt_unit]
    have hpred := dist_add_unit_eq_pred a a' i hi
    have hdistB : dist a' (a + unit i) = d - 1 := by
      have hpred' : dist a' (a + unit i) + 1 = d := by rw [hd]; exact hpred
      omega
    rw [hdistA, hdistB] at h1
    rw [← h1]
    decide
  have hdpos : 0 < d := by
    rw [hd]
    exact dist_pos_of_ne hne
  have hd4 : d % 4 = 1 := by
    have h1 := (b1_eq_zero_iff d).mp hd0
    have h2 := (b1_eq_zero_iff (d - 1)).mp hd1
    rcases h1 with h1 | h1
    · have h3 : (d - 1) % 4 = 3 := by omega
      rcases h2 with h2 | h2 <;> omega
    · exact h1
  have hle : a' = compl a := by
    funext j
    by_contra hjj
    have hsame : a' j = a j := by
      rcases zmod2_eq_zero_or_one (a' j) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (a j) with h2 | h2
      · rw [h1, h2]
      · exfalso; apply hjj; rw [h1, compl, h2]; decide
      · exfalso; apply hjj; rw [h1, compl, h2]; decide
      · rw [h1, h2]
    have h1 := hf' (a + unit j)
    have hdistA : dist a (a + unit j) = 1 := by
      rw [dist_eq_wt_add]
      have hz : a + (a + unit j) = unit j := by
        funext k
        rw [Pi.add_apply, Pi.add_apply, ← add_assoc, zmod2_add_self, zero_add]
      rw [hz, wt_unit]
    have hdistB : dist a' (a + unit j) = d + 1 := dist_add_unit_eq_succ a a' j hsame.symm
    rw [hdistA, hdistB] at h1
    have hb1succ : b1 (d + 1) = 1 := by
      rw [b1_eq_mod_four]
      have h4' : (d + 1) % 4 = 2 := by omega
      rw [h4']
    rw [hb1succ] at h1
    have hb10 : b1 1 = 0 := by decide
    rw [hb10] at h1
    exact Nat.zero_ne_one h1
  refine ⟨?_, hle⟩
  have hdn : d = n := by
    rw [hd, hle]
    exact dist_compl_self a
  rw [← hdn]
  exact hd4

/-- The map from words to concepts is injective when the word length is not congruent to one
modulo four. -/
theorem concept_injective_of_mod_four_ne_one {n : ℕ} (h4 : n % 4 ≠ 1) :
    Function.Injective (concept (n := n)) := by
  intro a a' hf
  by_contra hne
  exact h4 (concept_eq_of_ne hf hne).1

/-- When the word length is congruent to one modulo four, complementary words define the same
concept. [MeyerPommersheim2009]. -/
theorem concept_compl {n : ℕ} (h4 : n % 4 = 1) (a : Word n) :
    concept (compl a) = concept a := by
  funext x
  simp only [concept]
  apply congrArg (fun k : ℕ => (k : ZMod 2))
  have hd : dist (compl a) x + dist a x = n := dist_compl_add a x
  have hle : dist a x ≤ n := dist_le a x
  have hsub : dist (compl a) x = n - dist a x := by omega
  rw [hsub]
  exact b1_sub_of_mod_four_one h4 hle

/-- There are `2 ^ n` binary words of length `n`. -/
lemma natCard_word (n : ℕ) : Nat.card (Word n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp [ZMod.card, Fintype.card_fin]

/-- The equivalence between words of length `m + 1` whose first bit is zero and words of length
`m`, obtained by deleting or prepending that bit. -/
def zeroBitEquiv (m : ℕ) : {a : Word (m + 1) // a 0 = 0} ≃ Word m where
  toFun a := Fin.tail a.1
  invFun v := ⟨Fin.cons 0 v, by simp⟩
  left_inv a := by
    apply Subtype.ext
    simpa [a.2] using Fin.cons_self_tail a.1
  right_inv v := by
    funext j
    simp [Fin.tail_cons]

/-- There are `2 ^ m` words of length `m + 1` whose first bit is zero. -/
lemma natCard_subtype_zero_bit (m : ℕ) :
    Nat.card {a : Word (m + 1) // a 0 = 0} = 2 ^ m := by
  rw [Nat.card_congr (zeroBitEquiv m), natCard_word]

/-- The concept class has cardinality `2 ^ n` when `n` is not congruent to one modulo four.
[MeyerPommersheim2009]. -/
theorem lemma_3_1_card_ne_one {n : ℕ} (h4 : n % 4 ≠ 1) :
    (conceptClass n).ncard = 2 ^ n := by
  rw [conceptClass, Set.ncard_range_of_injective (concept_injective_of_mod_four_ne_one h4)]
  exact natCard_word n

/-- The concept class has cardinality `2 ^ (n - 1)` when `n` is congruent to one modulo four.
[MeyerPommersheim2009]. -/
theorem lemma_3_1_card_mod_one {n : ℕ} (h4 : n % 4 = 1) :
    (conceptClass n).ncard = 2 ^ (n - 1) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0] at h4
      norm_num at h4
    · exact hpos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have hrange : conceptClass (m + 1) =
      Set.range (fun a : {a : Word (m + 1) // a 0 = 0} => concept a.1) := by
    ext f
    constructor
    · rintro ⟨a, rfl⟩
      by_cases h0 : a 0 = 0
      · exact ⟨⟨a, h0⟩, rfl⟩
      · refine ⟨⟨compl a, ?_⟩, concept_compl h4 a⟩
        show compl a 0 = 0
        rw [compl]
        have h1 : a 0 = 1 := by
          rcases zmod2_eq_zero_or_one (a 0) with h | h
          · exact absurd h h0
          · exact h
        rw [h1]
        decide
    · rintro ⟨⟨a, _⟩, rfl⟩
      exact ⟨a, rfl⟩
  have hinj : Function.Injective (fun a : {a : Word (m + 1) // a 0 = 0} => concept a.1) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    apply Subtype.ext
    by_contra hne
    obtain ⟨-, hba⟩ := concept_eq_of_ne hab hne
    have hb0 : b 0 = 0 := hb
    have hb0' : compl (a : Word (m + 1)) 0 = 0 := by
      rw [← hba]
      exact hb0
    have ha0 : compl (a : Word (m + 1)) 0 = 1 := by
      rw [compl, ha]
      decide
    rw [ha0] at hb0'
    exact one_ne_zero hb0'
  rw [hrange, Set.ncard_range_of_injective hinj, natCard_subtype_zero_bit]
  simp

/-- The complex sign `(-1) ^ (d / 2)` associated with the second binary digit of `d`. -/
def csign (d : ℕ) : ℂ := (-1 : ℂ) ^ (d / 2)

/-- The natural representative of one in `ZMod 2` is one. -/
lemma zmod2_val_one : (1 : ZMod 2).val = 1 := rfl

/-- The natural representative of zero in `ZMod 2` is zero. -/
lemma zmod2_val_zero : (0 : ZMod 2).val = 0 := rfl

/-- Reducing a natural exponent modulo two leaves the corresponding power of minus one unchanged
in any ring. -/
lemma neg_one_pow_mod_two {R : Type*} [Ring R] (k : ℕ) :
    (-1 : R) ^ (k % 2) = (-1 : R) ^ k := by
  have hk : k = 2 * (k / 2) + k % 2 := by omega
  conv_rhs => rw [hk]
  rw [pow_add, pow_mul, show (-1 : R) ^ 2 = 1 by rw [pow_two, neg_mul_neg, one_mul],
    one_pow, one_mul]

/-- Raising complex minus one to the second binary digit of `d` gives `csign d`. -/
lemma neg_one_pow_b1 (d : ℕ) : (-1 : ℂ) ^ (b1 d) = csign d := by
  unfold b1 csign
  exact neg_one_pow_mod_two (d / 2)

/-- The square of `csign d` is one. -/
lemma csign_sq (d : ℕ) : csign d * csign d = 1 := by
  unfold csign
  rw [← pow_add, show d / 2 + d / 2 = 2 * (d / 2) by ring, pow_mul,
    show (-1 : ℂ) ^ 2 = 1 by norm_num, one_pow]

/-- The product of the weight sign of `z` and the distance sign from `a` to `z` equals the
weight sign of `a` times the character at `hatX z`. -/
lemma csign_mul_dist {n : ℕ} (a z : Word n) :
    csign (wt z) * csign (dist a z)
      = csign (wt a) * (-1 : ℂ) ^ (dot a (hatX z)).val := by
  unfold csign
  have h := congrArg (fun t : ℤ => (t : ℂ)) (lemma_3_4 a z)
  simp only [sign, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
  rw [h]
  have hsq : (-1 : ℂ) ^ (wt z / 2) * (-1 : ℂ) ^ (wt z / 2) = 1 := by
    rw [← pow_add, show wt z / 2 + wt z / 2 = 2 * (wt z / 2) by ring, pow_mul,
      show (-1 : ℂ) ^ 2 = 1 by norm_num, one_pow]
  calc (-1 : ℂ) ^ (wt z / 2)
        * ((-1 : ℂ) ^ (wt a / 2) * (-1 : ℂ) ^ (wt z / 2)
            * (-1 : ℂ) ^ (dot a (hatX z)).val)
      = (-1 : ℂ) ^ (wt a / 2)
          * ((-1 : ℂ) ^ (wt z / 2) * (-1 : ℂ) ^ (wt z / 2))
          * (-1 : ℂ) ^ (dot a (hatX z)).val := by ring
    _ = (-1 : ℂ) ^ (wt a / 2) * (-1 : ℂ) ^ (dot a (hatX z)).val := by
        rw [hsq]; ring

/-- The weight of a complemented word equals its length minus its original weight. -/
lemma wt_compl {n : ℕ} (x : Word n) : wt (compl x) = n - wt x := by
  have h1 : wt (compl x) = dist oneWord x := by
    rw [compl_eq_add_one, add_comm x oneWord, ← dist_eq_wt_add]
  have h2 : dist oneWord x + dist (0 : Word n) x = n := by
    have h := dist_compl_add (0 : Word n) x
    simpa [compl, oneWord] using! h
  have h3 : dist (0 : Word n) x = wt x := by
    rw [dist_eq_wt_add]; simp
  omega

/-- Complementing a binary word twice returns the original word. -/
lemma compl_compl {n : ℕ} (x : Word n) : compl (compl x) = x := by
  funext i
  show x i + 1 + 1 = x i
  rw [add_assoc, zmod2_add_self, add_zero]

/-- For words of even length, `hatX` is an involution. -/
lemma hatX_hatX_of_even {n : ℕ} (hn : Even n) (x : Word n) : hatX (hatX x) = x := by
  unfold hatX
  by_cases hx : wt x % 2 = 0
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx]
    have hwc : wt (compl x) % 2 = 1 := by
      rw [wt_compl]
      obtain ⟨k, hk⟩ := hn
      have hle : wt x ≤ n := wt_le x
      omega
    rw [if_neg (by omega : ¬ wt (compl x) % 2 = 0)]
    exact compl_compl x

/-- The binary dot product is additive in its first argument. -/
lemma dot_add_left {n : ℕ} (a b x : Word n) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The product of the binary characters indexed by `a` and `b` is the character indexed by `a +
b`. -/
lemma neg_one_pow_dot_add {n : ℕ} (a b x : Word n) :
    (-1 : ℂ) ^ (dot a x).val * (-1 : ℂ) ^ (dot b x).val
      = (-1 : ℂ) ^ (dot (a + b) x).val := by
  rw [dot_add_left]
  generalize dot a x = u at *
  generalize dot b x = v at *
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one v with rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · have h : ((1 : ZMod 2) + 1).val = 0 := by decide
    rw [h, zmod2_val_one]
    norm_num

/-- The self-equivalence of binary words that flips coordinate `i`. -/
def addUnitEquiv {n : ℕ} (i : Fin n) : Word n ≃ Word n where
  toFun x := x + unit i
  invFun x := x + unit i
  left_inv x := by
    funext k
    show (x k + unit i k) + unit i k = x k
    rw [add_assoc, zmod2_add_self, add_zero]
  right_inv x := by
    funext k
    show (x k + unit i k) + unit i k = x k
    rw [add_assoc, zmod2_add_self, add_zero]

/-- The sum of a binary character over all words is the number of words for the zero character
and zero otherwise. -/
lemma sum_neg_one_pow_dot {n : ℕ} (b : Word n) :
    (∑ x : Word n, (-1 : ℂ) ^ (dot b x).val)
      = if b = 0 then (Fintype.card (Word n) : ℂ) else 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [if_pos rfl]
    have hzero : ∀ x : Word n, dot (0 : Word n) x = 0 := by
      intro x; simp [dot]
    have hone : ∀ x : Word n, (-1 : ℂ) ^ (dot (0 : Word n) x).val = 1 := by
      intro x
      rw [hzero x, zmod2_val_zero]
      norm_num
    rw [Finset.sum_congr rfl (fun x _ => hone x)]
    simp
  · rw [if_neg hb]
    obtain ⟨i, hi⟩ := exists_ne_of_ne hb
    have hbi : b i = 1 := by
      rcases zmod2_eq_zero_or_one (b i) with h | h
      · exact absurd h hi
      · exact h
    have hσ : ∀ x : Word n, (-1 : ℂ) ^ (dot b (x + unit i)).val
        = - (-1 : ℂ) ^ (dot b x).val := by
      intro x
      have hd : dot b (x + unit i) = dot b x + 1 := by
        rw [dot_add_right, dot_unit, hbi]
      rw [hd]
      rcases zmod2_eq_zero_or_one (dot b x) with h | h
      · rw [h]
        rw [zero_add, zmod2_val_one, zmod2_val_zero]
        norm_num
      · rw [h]
        have h2 : ((1 : ZMod 2) + 1).val = 0 := by decide
        rw [h2, zmod2_val_one]
        norm_num
    have heq : (∑ x : Word n, (-1 : ℂ) ^ (dot b x).val)
        = ∑ x : Word n, (-1 : ℂ) ^ (dot b (x + unit i)).val :=
      (Equiv.sum_comp (addUnitEquiv i) (fun x => (-1 : ℂ) ^ (dot b x).val)).symm
    have hneg : (∑ x : Word n, (-1 : ℂ) ^ (dot b (x + unit i)).val)
        = -(∑ x : Word n, (-1 : ℂ) ^ (dot b x).val) := by
      rw [Finset.sum_congr rfl (fun x _ => hσ x), Finset.sum_neg_distrib]
    have hS : (∑ x : Word n, (-1 : ℂ) ^ (dot b x).val)
        = -(∑ x : Word n, (-1 : ℂ) ^ (dot b x).val) := heq.trans hneg
    have hSS : (∑ x : Word n, (-1 : ℂ) ^ (dot b x).val)
        + (∑ x : Word n, (-1 : ℂ) ^ (dot b x).val) = 0 := by
      nth_rewrite 1 [hS]
      exact neg_add_cancel _
    exact add_self_eq_zero.mp hSS

/-- The unnormalized algorithm amplitude obtained by summing the weight and distance phases
after `hatX`, multiplied by the binary Fourier character indexed by `y`. -/
def algAmp {n : ℕ} (a y : Word n) : ℂ :=
  ∑ x : Word n,
    (-1 : ℂ) ^ (b1 (wt (hatX x)) + b1 (dist a (hatX x)))
      * (-1 : ℂ) ^ (dot y x).val

/-- The algorithm amplitude `algAmp a y` scaled by the inverse of `2 ^ n`. -/
def algNormAmp {n : ℕ} (a y : Word n) : ℂ := ((2 : ℂ) ^ n)⁻¹ * algAmp a y

/-- For even word length, the unnormalized algorithm amplitude vanishes unless `y = a`, where it
equals `2 ^ n` times the weight phase of `a`. [MeyerPommersheim2009]. -/
theorem theorem_3_2_amplitude {n : ℕ} (hn : Even n) (a y : Word n) :
    algAmp a y =
      if y = a then (-1 : ℂ) ^ (b1 (wt a)) * (2 : ℂ) ^ n else 0 := by
  unfold algAmp
  have hterm : ∀ x : Word n,
      (-1 : ℂ) ^ (b1 (wt (hatX x)) + b1 (dist a (hatX x)))
        * (-1 : ℂ) ^ (dot y x).val
      = (-1 : ℂ) ^ (b1 (wt a))
          * ((-1 : ℂ) ^ (dot a x).val * (-1 : ℂ) ^ (dot y x).val) := by
    intro x
    have hL : (-1 : ℂ) ^ (b1 (wt (hatX x)) + b1 (dist a (hatX x)))
        = csign (wt a) * (-1 : ℂ) ^ (dot a x).val := by
      rw [pow_add, neg_one_pow_b1, neg_one_pow_b1, csign_mul_dist, hatX_hatX_of_even hn]
    rw [hL, neg_one_pow_b1]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  have hsum2 : (∑ x : Word n, (-1 : ℂ) ^ (b1 (wt a))
        * ((-1 : ℂ) ^ (dot a x).val * (-1 : ℂ) ^ (dot y x).val))
      = ∑ x : Word n, (-1 : ℂ) ^ (b1 (wt a)) * (-1 : ℂ) ^ (dot (a + y) x).val :=
    Finset.sum_congr rfl (fun x _ => by rw [neg_one_pow_dot_add a y x])
  rw [hsum2, ← Finset.mul_sum]
  by_cases hya : y = a
  · subst y
    rw [if_pos rfl]
    have hzero : a + a = 0 := by
      funext k
      exact zmod2_add_self (a k)
    rw [sum_neg_one_pow_dot (a + a), if_pos hzero]
    congr 1
    rw [show Fintype.card (Word n) = 2 ^ n by
      rw [Fintype.card_fun]; simp [ZMod.card, Fintype.card_fin]]
    push_cast
    ring
  · rw [if_neg hya]
    have hne : a + y ≠ 0 := by
      intro h
      apply hya
      have h1 : a + y = a + a := by
        rw [h]
        funext k
        exact (zmod2_add_self (a k)).symm
      exact add_left_cancel h1
    rw [sum_neg_one_pow_dot (a + y), if_neg hne, mul_zero]

/-- Every natural power of complex minus one has squared norm one. -/
lemma normSq_neg_one_pow (k : ℕ) : Complex.normSq ((-1 : ℂ) ^ k) = 1 := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow, Complex.normSq_one]
  · rw [h.neg_one_pow, Complex.normSq_neg, Complex.normSq_one]

/-- For even word length, the normalized amplitude is supported at `a` with its weight phase,
giving squared norm one at `a` and zero at every other word. [MeyerPommersheim2009]. -/
theorem theorem_3_2 {n : ℕ} (hn : Even n) (a : Word n) :
    (∀ y : Word n, algNormAmp a y = if y = a then (-1 : ℂ) ^ (b1 (wt a)) else 0) ∧
    Complex.normSq (algNormAmp a a) = 1 ∧
    (∀ y : Word n, y ≠ a → Complex.normSq (algNormAmp a y) = 0) := by
  have hamp : ∀ y : Word n,
      algAmp a y = if y = a then (-1 : ℂ) ^ (b1 (wt a)) * (2 : ℂ) ^ n else 0 :=
    fun y => theorem_3_2_amplitude hn a y
  have hpow : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    unfold algNormAmp
    rw [hamp y]
    by_cases h : y = a
    · subst y
      rw [if_pos rfl, if_pos rfl]
      calc ((2 : ℂ) ^ n)⁻¹ * ((-1 : ℂ) ^ (b1 (wt a)) * (2 : ℂ) ^ n)
          = (-1 : ℂ) ^ (b1 (wt a)) * (((2 : ℂ) ^ n)⁻¹ * (2 : ℂ) ^ n) := by ring
        _ = (-1 : ℂ) ^ (b1 (wt a)) := by rw [inv_mul_cancel₀ hpow, mul_one]
    · rw [if_neg h, mul_zero, if_neg h]
  · unfold algNormAmp
    rw [hamp a, if_pos rfl]
    have hcancel : ((2 : ℂ) ^ n)⁻¹ * ((-1 : ℂ) ^ (b1 (wt a)) * (2 : ℂ) ^ n)
        = (-1 : ℂ) ^ (b1 (wt a)) := by
      rw [mul_comm ((-1 : ℂ) ^ (b1 (wt a))) ((2 : ℂ) ^ n), ← mul_assoc,
        inv_mul_cancel₀ hpow, one_mul]
    rw [hcancel, normSq_neg_one_pow]
  · intro y hy
    unfold algNormAmp
    rw [hamp y, if_neg hy]
    simp only [mul_zero, Complex.normSq_zero]

/-- The number of inputs on which two Boolean concepts in the family `f` differ. -/
def hammingDist {X C : Type*} [Fintype X] (f : C → X → ZMod 2) (c c' : C) : ℕ :=
  (Finset.univ.filter (fun x => f c x ≠ f c' x)).card

/-- The integer sign matrix of a Boolean concept family, with entry `(-1) ^ (f c x).val`. -/
def learningMatrix {X C : Type*} [Fintype X] (f : C → X → ZMod 2) : Matrix X C ℤ :=
  fun x c => (-1 : ℤ) ^ (f c x).val

/-- The condition that a matrix has entries in `{1, -1}` and pairwise orthogonal columns whose
squared lengths equal the number of rows. -/
def IsHadamardColumns {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (M : Matrix X C ℤ) : Prop :=
  (∀ x c, M x c = 1 ∨ M x c = -1) ∧
    M.transpose * M = (Fintype.card X : ℤ) • (1 : Matrix C C ℤ)

/-- Multiplying the signs of two binary elements gives the sign of their sum. -/
lemma neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ b.val = (-1 : ℤ) ^ (a + b).val := by
  rw [← pow_add]
  apply neg_one_pow_eq_of_cast_eq
  rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The sum of binary signs equals the size of the domain minus twice the number of nonzero
function values. -/
lemma sum_neg_one_pow_eq {X : Type*} [Fintype X] (g : X → ZMod 2) :
    (∑ x : X, (-1 : ℤ) ^ (g x).val)
      = (Fintype.card X : ℤ) - 2 * ((Finset.univ.filter (fun x => g x ≠ 0)).card : ℤ) := by
  have hterm : ∀ x : X, (-1 : ℤ) ^ (g x).val = 1 - 2 * (if g x = 0 then 0 else 1 : ℤ) := by
    intro x
    rcases zmod2_eq_zero_or_one (g x) with h | h <;> rw [h] <;> decide
  calc (∑ x : X, (-1 : ℤ) ^ (g x).val)
      = ∑ x : X, (1 - 2 * (if g x = 0 then 0 else 1 : ℤ)) :=
        Finset.sum_congr rfl (fun x _ => hterm x)
    _ = (∑ _x : X, (1 : ℤ)) - ∑ x : X, 2 * (if g x = 0 then 0 else 1 : ℤ) := by
        rw [Finset.sum_sub_distrib]
    _ = (Fintype.card X : ℤ) - 2 * ∑ x : X, (if g x = 0 then 0 else 1 : ℤ) := by
        rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
        simp
    _ = (Fintype.card X : ℤ) - 2 * ((Finset.univ.filter (fun x => g x ≠ 0)).card : ℤ) := by
        have hsum : (∑ x : X, (if g x = 0 then 0 else 1 : ℤ))
            = ((Finset.univ.filter (fun x => g x ≠ 0)).card : ℤ) := by
          rw [← sum_ite_one_eq_card (fun x => g x ≠ 0)]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : g x = 0 <;> simp [h]
        rw [hsum]

/-- The inner product of two columns of the learning matrix equals the number of inputs minus
twice their Hamming distance. -/
lemma learningMatrix_col_inner {X C : Type*} [Fintype X] (f : C → X → ZMod 2) (c c' : C) :
    (∑ x : X, (-1 : ℤ) ^ (f c x).val * (-1 : ℤ) ^ (f c' x).val)
      = (Fintype.card X : ℤ) - 2 * (hammingDist f c c' : ℤ) := by
  rw [show (∑ x : X, (-1 : ℤ) ^ (f c x).val * (-1 : ℤ) ^ (f c' x).val)
        = ∑ x : X, (-1 : ℤ) ^ ((f c x + f c' x)).val from
      Finset.sum_congr rfl (fun x _ => neg_one_pow_val_add (f c x) (f c' x))]
  rw [sum_neg_one_pow_eq]
  congr 2
  rw [hammingDist]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _
  exact not_congr (zmod2_add_eq_zero_iff (f c x) (f c' x))

/-- Under the specified vanishing Gram relations with `-1 ≤ lam ≤ 1` and at least two concepts,
all distinct concepts have a common Hamming distance at least half the domain size.
[MeyerPommersheim2009]. -/
theorem lemma_4_1_distance {X C : Type*} [Fintype X]
    (f : C → X → ZMod 2) (lam : ℝ)
    (hN : 0 < Fintype.card X) (hlam : -1 ≤ lam) (hlam1 : lam ≤ 1)
    (hgram : ∀ c c' : C, c ≠ c' →
      (Fintype.card X : ℝ) - (hammingDist f c c' : ℝ)
        + lam * (hammingDist f c c' : ℝ) = 0)
    (hex : ∃ c c' : C, c ≠ c') :
    ∃ d : ℕ, (Fintype.card X : ℝ) / 2 ≤ (d : ℝ) ∧
      ∀ c c' : C, c ≠ c' → hammingDist f c c' = d := by
  obtain ⟨c0, c1, hc01⟩ := hex
  have hN' : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hN
  have h0 := hgram c0 c1 hc01
  refine ⟨hammingDist f c0 c1, ?_, ?_⟩
  · nlinarith [h0, hlam, hlam1, hN']
  · intro c c' hcc'
    have h := hgram c c' hcc'
    have hlamp : lam < 1 := by
      rcases lt_or_eq_of_le hlam1 with hlt | heq
      · exact hlt
      · exfalso
        rw [heq] at h0
        nlinarith [h0, hN']
    have hpos : (0 : ℝ) < 1 - lam := by linarith
    have hreal : (hammingDist f c c' : ℝ) = (hammingDist f c0 c1 : ℝ) := by
      nlinarith [h, h0, hpos]
    exact_mod_cast hreal

/-- For equally many inputs and concepts, with an even domain size greater than two, constant
pairwise distance equal to half the domain size makes the learning matrix have Hadamard
columns. [MeyerPommersheim2009]. -/
theorem lemma_4_1_hadamard {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (f : C → X → ZMod 2) (d : ℕ)
    (hN2 : 2 < Fintype.card X) (hcard : Fintype.card C = Fintype.card X)
    (heven : Even (Fintype.card X))
    (hcode : ∀ c c' : C, c ≠ c' → hammingDist f c c' = d)
    (hd : 2 * d = Fintype.card X) :
    IsHadamardColumns (learningMatrix f) := by
  have := hN2
  have := hcard
  have := heven
  refine ⟨?_, ?_⟩
  · intro x c
    rcases Nat.even_or_odd (f c x).val with h | h
    · left; exact h.neg_one_pow
    · right; exact h.neg_one_pow
  · ext c c'
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, learningMatrix]
    rw [learningMatrix_col_inner f c c']
    by_cases hcc : c = c'
    · subst hcc
      have hzero : hammingDist f c c = 0 := by
        simp [hammingDist]
      rw [hzero]
      simp
    · rw [hcode c c' hcc]
      have hdZ : (2 : ℤ) * (d : ℤ) = (Fintype.card X : ℤ) := by exact_mod_cast hd
      simp [hcc]
      omega

/-- Adding one changes every element of `ZMod 2`. -/
lemma zmod2_add_one_ne (u : ZMod 2) : u + 1 ≠ u := by
  rcases zmod2_eq_zero_or_one u with rfl | rfl <;> decide

/-- If two binary elements are distinct, adding one to the first gives the second. -/
lemma zmod2_add_one_eq_of_ne {u v : ZMod 2} (h : u ≠ v) : u + 1 = v := by
  have huv : u + v = 1 := zmod2_add_eq_one_of_ne h
  calc u + 1 = u + (u + v) := by rw [huv]
    _ = (u + u) + v := by abel
    _ = v := by rw [zmod2_add_self, zero_add]

/-- The inner product of two learning-matrix rows is the sum of the signs of the corresponding
pairwise output sums. -/
lemma learningMatrix_row_inner {X C : Type*} [Fintype X] [Fintype C]
    (f : C → X → ZMod 2) (x y : X) :
    (∑ c : C, learningMatrix f x c * learningMatrix f y c)
      = ∑ c : C, (-1 : ℤ) ^ ((f c x + f c y).val) := by
  apply Finset.sum_congr rfl
  intro c _
  simp only [learningMatrix]
  exact neg_one_pow_val_add (f c x) (f c y)

/-- The product of two binary signs equals minus one exactly when the binary elements differ. -/
lemma neg_one_pow_mul_eq_neg_one_iff (u v : ZMod 2) :
    (-1 : ℤ) ^ u.val * (-1 : ℤ) ^ v.val = -1 ↔ u ≠ v := by
  rw [neg_one_pow_val_add]
  constructor
  · intro h huv
    rw [huv, zmod2_add_self] at h
    norm_num at h
  · intro h
    rw [zmod2_add_eq_one_of_ne h, zmod2_val_one]
    norm_num

/-- The sign of the sum of two binary elements equals minus one exactly when they differ. -/
lemma neg_one_pow_sum_eq_neg_one_iff (u v : ZMod 2) :
    (-1 : ℤ) ^ (u + v).val = -1 ↔ u ≠ v := by
  rw [← neg_one_pow_val_add]
  exact neg_one_pow_mul_eq_neg_one_iff u v

/-- If two binary elements sum to one, the second equals the first plus one. -/
lemma eq_add_one_of_add_eq_one {u v : ZMod 2} (h : u + v = 1) : v = u + 1 := by
  calc v = v + (u + u) := by rw [zmod2_add_self, add_zero]
    _ = (u + v) + u := by abel
    _ = 1 + u := by rw [h]
    _ = u + 1 := by abel

/-- For a square matrix on a nonempty finite type, the Hadamard column condition also gives the
corresponding row Gram identity. -/
lemma hadamard_rows {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {M : Matrix m m ℤ} (hM : IsHadamardColumns M) :
    M * M.transpose = (Fintype.card m : ℤ) • (1 : Matrix m m ℤ) := by
  have hc : M.transpose * M = (Fintype.card m : ℤ) • (1 : Matrix m m ℤ) := hM.2

  let Mq : Matrix m m ℚ := M.map (Int.castRingHom ℚ)
  have hcard : (Fintype.card m : ℚ) ≠ 0 := by
    have hpos : 0 < Fintype.card m := Fintype.card_pos
    have hposq : (0 : ℚ) < (Fintype.card m : ℚ) := by exact_mod_cast hpos
    exact ne_of_gt hposq
  have hcq : Mq.transpose * Mq = (Fintype.card m : ℚ) • (1 : Matrix m m ℚ) := by
    ext x y
    have hentry : (∑ c, M c x * M c y)
        = (Fintype.card m : ℤ) * (if x = y then 1 else 0) := by
      have h := congrFun (congrFun hc x) y
      simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply] using h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      Mq, Matrix.map_apply]
    simp_rw [← map_mul (Int.castRingHom ℚ)]
    rw [← map_sum (Int.castRingHom ℚ), hentry]
    simp
  have hBMq : ((Fintype.card m : ℚ)⁻¹ • Mq.transpose) * Mq = 1 := by
    rw [Matrix.smul_mul, hcq, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hMBq : Mq * ((Fintype.card m : ℚ)⁻¹ • Mq.transpose) = 1 := by
    have := (mul_eq_one_comm (M := Matrix m m ℚ)).mp hBMq
    simpa using this
  have hsq : Mq * Mq.transpose = (Fintype.card m : ℚ) • (1 : Matrix m m ℚ) := by
    have h := congrArg (fun X : Matrix m m ℚ => (Fintype.card m : ℚ) • X) hMBq
    simpa only [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hcard, one_smul] using h
  ext x y
  have h := congrFun (congrFun hsq x) y
  have h' : ((M * M.transpose) x y : ℚ) =
      (((Fintype.card m : ℤ) • (1 : Matrix m m ℤ)) x y : ℚ) := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      Mq] using h
  exact Int.cast_injective (α := ℚ) h'

/-- Distinct rows of a square matrix satisfying the Hadamard column condition have inner product
zero. -/
lemma hadamard_row_dot {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {M : Matrix m m ℤ} (hM : IsHadamardColumns M) {x y : m} (hxy : x ≠ y) :
    (∑ c : m, M x c * M y c) = 0 := by
  have h := congrFun (congrFun (hadamard_rows hM) x) y
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
    hxy] using h

/-- Flipping two distinct coordinates with different bit values preserves the Hamming weight. -/
lemma wt_add_units_of_ne {n : ℕ} (v : Word n) {i j : Fin n} (hij : i ≠ j)
    (h : v i ≠ v j) : wt (v + (unit i + unit j)) = wt v := by
  have hcomm : v + (unit i + unit j) = (v + unit i) + unit j := by abel
  rw [hcomm]
  rcases zmod2_eq_zero_or_one (v i) with hi | hi <;>
    rcases zmod2_eq_zero_or_one (v j) with hj | hj
  · exact absurd (hi.trans hj.symm) h
  · have h1 : wt (v + unit i) = wt v + 1 := wt_add_unit_zero v i hi
    have h2 : (v + unit i) j = 1 := by
      rw [Pi.add_apply, hj]
      simp [unit, Ne.symm hij]
    have h3 : wt ((v + unit i) + unit j) + 1 = wt (v + unit i) :=
      wt_add_unit_one _ j h2
    omega
  · have h1 : wt (v + unit i) + 1 = wt v := wt_add_unit_one v i hi
    have h2 : (v + unit i) j = 0 := by
      rw [Pi.add_apply, hj]
      simp [unit, Ne.symm hij]
    have h3 : wt ((v + unit i) + unit j) = wt (v + unit i) + 1 :=
      wt_add_unit_zero _ j h2
    omega
  · exact absurd (hi.trans hj.symm) h

/-- If two distinct coordinates of `a` differ, its distances to zero and to the sum of the two
coordinate words are equal. -/
lemma dist_zero_eq_dist_units_of_ne {n : ℕ} (a : Word n) {i j : Fin n} (hij : i ≠ j)
    (h : a i ≠ a j) : dist a 0 = dist a (unit i + unit j) := by
  rw [dist_eq_wt_add, dist_eq_wt_add, add_zero]
  exact (wt_add_units_of_ne a hij h).symm

/-- For distinct coordinates `i` and `j` and `d + 2 ≤ n`, there is a weight-`d` word vanishing
there whose distances to zero and to `unit i + unit j` are `d` and `d + 2`. -/
lemma exists_word_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) (d : ℕ) (hd : d + 2 ≤ n) :
    ∃ a : Word n, a i = 0 ∧ a j = 0 ∧ wt a = d ∧ dist a 0 = d ∧
      dist a (unit i + unit j) = d + 2 := by
  classical
  have hcard : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, ht_sub, ht_card⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ.erase i).erase j) (by rw [hcard]; omega : d ≤ ((Finset.univ.erase i).erase j).card)
  let a : Word n := fun k => if k ∈ t then 1 else 0
  have hi_mem : i ∉ t := by
    intro hmem
    have h1 := ht_sub hmem
    rw [Finset.mem_erase] at h1
    exact (Finset.notMem_erase i Finset.univ) h1.2
  have hj_mem : j ∉ t := by
    intro hmem
    have h1 := ht_sub hmem
    rw [Finset.mem_erase] at h1
    exact h1.1 rfl
  have hai : a i = 0 := by simp [a, hi_mem]
  have haj : a j = 0 := by simp [a, hj_mem]
  have hfil : Finset.univ.filter (fun k : Fin n => a k ≠ 0) = t := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, a]
    constructor
    · intro hk
      by_contra hkt
      simp [hkt] at hk
    · intro hkt
      simp [hkt]
  have hwt : wt a = d := by
    have h : wt a = ((Finset.univ.filter (fun k : Fin n => a k ≠ 0)).card : ℕ) := by
      rw [wt]
      rw [show (∑ k : Fin n, if a k = 0 then 0 else 1)
            = ∑ k : Fin n, (if a k ≠ 0 then (1 : ℕ) else 0) from
          Finset.sum_congr rfl (fun k _ => by by_cases hk : a k = 0 <;> simp [hk])]
      exact sum_ite_one_eq_card _
    rw [h, hfil, ht_card]
  have hdist0 : dist a 0 = d := by
    rw [dist_eq_wt_add, add_zero, hwt]
  have hdistz : dist a (unit i + unit j) = d + 2 := by
    have hstep1 : wt (a + unit i) = wt a + 1 := wt_add_unit_zero a i hai
    have hstep2 : (a + unit i) j = 0 := by
      rw [Pi.add_apply, haj]
      simp [unit, Ne.symm hij]
    have hstep3 : wt ((a + unit i) + unit j) = wt (a + unit i) + 1 := wt_add_unit_zero _ j hstep2
    rw [dist_eq_wt_add, show a + (unit i + unit j) = (a + unit i) + unit j by abel,
      hstep3, hstep1, hwt]
  exact ⟨a, hai, haj, hwt, hdist0, hdistz⟩

/-- For word length at least two, the Hadamard condition for a distance-dependent learning
matrix forces `h (d + 2) = h d + 1` whenever `d + 2 ≤ n`. -/
lemma alternation_of_hadamard {n : ℕ} (hn : 2 ≤ n) (h : ℕ → ZMod 2)
    (hHad : IsHadamardColumns (learningMatrix (fun a x : Word n => h (dist a x)))) :
    ∀ d, d + 2 ≤ n → h (d + 2) = h d + 1 := by
  classical
  set g : Word n → Word n → ZMod 2 := fun a x => h (dist a x) with hg
  have hHad' : IsHadamardColumns (learningMatrix g) := hHad
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro hc
    have := congrArg Fin.val hc
    simp [i, j] at this
  let z : Word n := unit i + unit j
  have hne0z : (0 : Word n) ≠ z := by
    intro hc
    have h1 : z i = 1 := by simp [z, unit, i, j]
    have h2 : (0 : Word n) i = 0 := rfl
    rw [hc, h1] at h2
    exact one_ne_zero h2
  have hzero : (∑ a : Word n, learningMatrix g 0 a * learningMatrix g z a) = 0 :=
    hadamard_row_dot hHad' hne0z
  rw [learningMatrix_row_inner] at hzero
  let T : Word n → ℤ := fun a => (-1 : ℤ) ^ ((g a 0 + g a z).val)
  change (∑ a : Word n, T a) = 0 at hzero
  let s : Finset (Word n) := Finset.univ.filter (fun a => a i = a j)
  let t : Finset (Word n) := Finset.univ.filter (fun a => ¬ a i = a j)
  have hsum_univ : (∑ a ∈ s, T a) + (∑ a ∈ t, T a) = ∑ a : Word n, T a := by
    simpa only [s, t] using (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Word n))) (p := fun a => a i = a j) (f := T))
  have hsplit : (∑ a ∈ s, T a) + (∑ a ∈ t, T a) = 0 := hsum_univ.trans hzero
  have hcomp : ∀ a : Word n, ¬(a i = a j) → T a = 1 := by
    intro a ha
    have hgg : g a 0 = g a z := by
      simp only [g, z]
      rw [dist_zero_eq_dist_units_of_ne a hij ha]
    simp only [T]
    rw [hgg, zmod2_add_self]
    norm_num
  let τ : Word n → Word n := fun a => a + unit i
  have hττ : ∀ a, τ (τ a) = a := by
    intro a
    funext k
    simp only [τ, Pi.add_apply]
    rw [add_assoc]
    rcases zmod2_eq_zero_or_one ((unit i) k) with hk | hk
    · rw [hk, add_zero, add_zero]
    · rw [hk, zmod2_add_self, add_zero]
  have hmem : ∀ a : Word n, (a ∈ t ↔ τ a ∈ s) := by
    intro a
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and, τ]
    have hi : (a + unit i) i = a i + 1 := by simp [unit]
    have hj : (a + unit i) j = a j := by
      rw [Pi.add_apply]
      simp [unit, Ne.symm hij]
    constructor
    · intro ha
      rw [hi, hj]
      exact zmod2_add_one_eq_of_ne ha
    · intro ha hcontra
      rw [hi, hj] at ha
      rw [hcontra] at ha
      exact zmod2_add_one_ne (a j) ha
  have hswap : (∑ a ∈ t, T a) = ∑ a ∈ s, T (τ a) := by
    refine Finset.sum_bij' (fun a _ => τ a) (fun a _ => τ a) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact (hmem a).mp ha
    · intro a ha
      exact (hmem (τ a)).mpr (by simpa [hττ a] using ha)
    · intro a ha
      exact hττ a
    · intro a ha
      exact hττ a
    · intro a ha
      show T a = T (τ (τ a))
      rw [hττ a]
  have hcomp_sum : (∑ a ∈ t, T a) = (s.card : ℤ) := by
    rw [hswap]
    rw [Finset.sum_congr rfl (fun b hb => ?_), Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : τ b ∈ t := (hmem (τ b)).mpr (by simpa [hττ b] using hb)
    exact hcomp (τ b) (by simpa [t] using hbt)
  have hsum2 : (∑ a ∈ s, (T a + 1)) = 0 := by
    have h1 : (∑ a ∈ s, (T a + 1)) = (∑ a ∈ s, T a) + (s.card : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [h1, ← hcomp_sum]
    exact hsplit
  have hnonneg : ∀ a ∈ s, (0 : ℤ) ≤ T a + 1 := by
    intro a ha
    have hsign : T a = 1 ∨ T a = -1 := by
      have h1 := hHad'.1 0 a
      have h2 := hHad'.1 z a
      have hprod : T a = (-1 : ℤ) ^ (g a 0).val * (-1 : ℤ) ^ (g a z).val := by
        simp only [T]
        rw [neg_one_pow_val_add]
      rw [hprod]
      simp only [learningMatrix] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> norm_num
    rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  have hpoint : ∀ a ∈ s, T a = -1 := by
    intro a ha
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum2 a ha
    linarith
  intro d hd
  obtain ⟨a, hai, haj, hwt, hdist0, hdistz⟩ := exists_word_pair hij d hd
  have hamem : a ∈ s := by simp [s, hai, haj]
  have hexp : g a 0 + g a z = h d + h (d + 2) := by
    simp only [g, z]
    rw [hdist0, hdistz]
  have hterm : (-1 : ℤ) ^ ((h d + h (d + 2)).val) = -1 := by
    rw [← hexp]
    simpa only [T] using hpoint a hamem
  have hne := (neg_one_pow_sum_eq_neg_one_iff (h d) (h (d + 2))).mp hterm
  exact eq_add_one_of_add_eq_one (zmod2_add_eq_one_of_ne hne)

/-- Adding two to the input toggles the second binary digit modulo two. -/
lemma b1_add_two_zmod (d : ℕ) :
    (b1 (d + 2) : ZMod 2) = (b1 d : ZMod 2) + 1 := by
  have hdiv : (d + 2) / 2 = d / 2 + 1 := by omega
  unfold b1
  rw [hdiv]
  simp only [ZMod.natCast_mod]
  push_cast
  ring

/-- Adding two before any fixed natural offset toggles the second binary digit modulo two. -/
lemma b1_add_two_add (s d : ℕ) :
    (b1 (d + 2 + s) : ZMod 2) = (b1 (d + s) : ZMod 2) + 1 := by
  rw [show d + 2 + s = d + s + 2 by omega]
  exact b1_add_two_zmod (d + s)

/-- A function satisfying the two-step alternation relation has value `h 0 + k` modulo two at
each even input `2 * k ≤ n`. -/
lemma even_values_of_alternation {n : ℕ} {h : ℕ → ZMod 2}
    (halt : ∀ d, d + 2 ≤ n → h (d + 2) = h d + 1) :
    ∀ k, 2 * k ≤ n → h (2 * k) = h 0 + (k : ZMod 2) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : 2 * k ≤ n := by omega
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        halt (2 * k) (by omega), ih hk']
      push_cast
      ring

/-- A function satisfying the two-step alternation relation has value `h 1 + k` modulo two at
each odd input `2 * k + 1 ≤ n`. -/
lemma odd_values_of_alternation {n : ℕ} {h : ℕ → ZMod 2}
    (halt : ∀ d, d + 2 ≤ n → h (d + 2) = h d + 1) :
    ∀ k, 2 * k + 1 ≤ n → h (2 * k + 1) = h 1 + (k : ZMod 2) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : 2 * k + 1 ≤ n := by omega
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        halt (2 * k + 1) (by omega), ih hk']
      push_cast
      ring

/-- The two-step alternation relation determines every value up to `n` from its parity and the
integer half of its input. -/
lemma value_formula {n : ℕ} {h : ℕ → ZMod 2}
    (halt : ∀ d, d + 2 ≤ n → h (d + 2) = h d + 1) :
    ∀ d, d ≤ n → h d = h (d % 2) + ((d / 2 : ℕ) : ZMod 2) := by
  intro d hd
  rcases Nat.mod_two_eq_zero_or_one d with hpar | hpar
  · have hd2 : d = 2 * (d / 2) := by omega
    have he := even_values_of_alternation halt (d / 2) (by omega)
    rw [← hd2] at he
    rw [he, hpar]
  · have hd2 : d = 2 * (d / 2) + 1 := by omega
    have ho := odd_values_of_alternation halt (d / 2) (by omega)
    rw [← hd2] at ho
    rw [ho, hpar]

/-- For odd `n`, a function satisfying the two-step alternation relation has constant sum `h d +
h (n - d)` for all `d ≤ n`, with the stated parity correction. -/
lemma compl_value_sum {n : ℕ} (hodd : n % 2 = 1) {h : ℕ → ZMod 2}
    (halt : ∀ d, d + 2 ≤ n → h (d + 2) = h d + 1) :
    ∀ d, d ≤ n →
      h d + h (n - d) = h 0 + h 1 + (((n - 1) / 2 : ℕ) : ZMod 2) := by
  intro d hd
  have hv1 := value_formula halt d hd
  have hv2 := value_formula halt (n - d) (by omega)
  have hdiv : d / 2 + (n - d) / 2 = (n - 1) / 2 := by omega
  have hcast : ((d / 2 : ℕ) : ZMod 2) + (((n - d) / 2 : ℕ) : ZMod 2)
      = (((n - 1) / 2 : ℕ) : ZMod 2) := by
    rw [← Nat.cast_add, hdiv]
  rw [hv1, hv2]
  rcases Nat.mod_two_eq_zero_or_one d with hpar | hpar
  · have hpar2 : (n - d) % 2 = 1 := by omega
    rw [hpar, hpar2, ← hcast]
    ring
  · have hpar2 : (n - d) % 2 = 0 := by omega
    rw [hpar, hpar2, ← hcast]
    ring

/-- For odd word length greater than one, no Boolean function of Hamming distance yields a
learning matrix with Hadamard columns. [MeyerPommersheim2009]. -/
theorem theorem_4_2 {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (h : ℕ → ZMod 2) :
    ¬ IsHadamardColumns (learningMatrix (fun a x : Word n => h (dist a x))) := by
  intro hHad
  classical
  have hn2 : 2 ≤ n := by omega
  have halt := alternation_of_hadamard hn2 h hHad
  let x : Word n := 0
  let y : Word n := oneWord
  have hxy : x ≠ y := by
    intro hc
    have h1 := congrFun hc ⟨0, by omega⟩
    simp [x, y, oneWord] at h1
  have hzero : (∑ a : Word n,
      learningMatrix (fun a x : Word n => h (dist a x)) x a *
        learningMatrix (fun a x : Word n => h (dist a x)) y a) = 0 :=
    hadamard_row_dot hHad hxy
  rw [learningMatrix_row_inner] at hzero
  have hzero' : (∑ a : Word n,
      (-1 : ℤ) ^ ((h (dist a 0) + h (dist a oneWord)).val)) = 0 := by
    simpa [x, y] using hzero
  have hterm : ∀ a : Word n,
      (-1 : ℤ) ^ ((h (dist a 0) + h (dist a oneWord)).val)
        = (-1 : ℤ) ^ ((h 0 + h 1 + (((n - 1) / 2 : ℕ) : ZMod 2)).val) := by
    intro a
    have hd0 : dist a 0 = wt a := by
      rw [dist_eq_wt_add, add_zero]
    have hdy : dist a oneWord = n - wt a := by
      rw [dist_eq_wt_add, ← compl_eq_add_one, wt_compl]
    have hcs := compl_value_sum hodd halt
    rw [hd0, hdy, hcs (wt a) (wt_le a)]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)] at hzero'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hzero'
  have hcard : (Fintype.card (Word n) : ℤ) = (2 : ℤ) ^ n := by
    change (Fintype.card (Fin n → ZMod 2) : ℤ) = (2 : ℤ) ^ n
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    push_cast
    ring
  rw [hcard] at hzero'
  have h2n : (2 : ℤ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hsign : (-1 : ℤ) ^ ((h 0 + h 1 + (((n - 1) / 2 : ℕ) : ZMod 2)).val) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  exact (mul_ne_zero h2n hsign) hzero'

/-- Every distance-dependent learning matrix satisfying the Hadamard column condition is
represented by the second binary digit of distance plus some shift less than four.
[MeyerPommersheim2009]. -/
theorem corollary_4_3 {n : ℕ} (h : ℕ → ZMod 2)
    (hHad : IsHadamardColumns (learningMatrix (fun a x : Word n => h (dist a x)))) :
    ∃ s : ℕ, s < 4 ∧ ∀ a x : Word n, h (dist a x) = (b1 (dist a x + s) : ZMod 2) := by
  classical
  obtain ⟨s, hs4, hs0, hs1⟩ : ∃ s : ℕ, s < 4 ∧ (b1 s : ZMod 2) = h 0 ∧
      (b1 (s + 1) : ZMod 2) = h 1 := by
    rcases zmod2_eq_zero_or_one (h 0) with h0 | h0 <;>
      rcases zmod2_eq_zero_or_one (h 1) with h1 | h1
    · exact ⟨0, by norm_num, by rw [h0]; norm_num [b1], by rw [h1]; norm_num [b1]⟩
    · exact ⟨1, by norm_num, by rw [h0]; norm_num [b1], by rw [h1]; norm_num [b1]⟩
    · exact ⟨3, by norm_num, by rw [h0]; norm_num [b1], by rw [h1]; norm_num [b1]⟩
    · exact ⟨2, by norm_num, by rw [h0]; norm_num [b1], by rw [h1]; norm_num [b1]⟩
  refine ⟨s, hs4, ?_⟩
  intro a x
  by_cases hsmall : dist a x ≤ 1
  · interval_cases hdx : dist a x
    · simpa using hs0.symm
    · simpa [Nat.add_comm] using hs1.symm
  · have hd2 : 2 ≤ n := by
      have := dist_le a x
      omega
    have halt := alternation_of_hadamard hd2 h hHad
    have hv := value_formula halt
    have hfv := value_formula (n := n) (h := fun d : ℕ => (b1 (d + s) : ZMod 2))
      (fun d _ => b1_add_two_add s d)
    have hdxn : dist a x ≤ n := dist_le a x
    have hfv' : (b1 (dist a x + s) : ZMod 2) =
        (b1 (dist a x % 2 + s) : ZMod 2) + ((dist a x / 2 : ℕ) : ZMod 2) := by
      simpa using hfv (dist a x) hdxn
    rw [hv (dist a x) hdxn, hfv']
    rcases Nat.mod_two_eq_zero_or_one (dist a x) with hpar | hpar
    · rw [hpar]
      simp only [Nat.zero_add]
      rw [← hs0]
    · rw [hpar]
      rw [Nat.add_comm 1 s]
      rw [← hs1]

/-- The average real quadratic-form success value of the effects `X i` on the columns of `B`,
with equal prior weight `1 / M`. -/
def measurementSuccess {N M : ℕ} (B : Matrix (Fin N) (Fin M) ℂ)
    (X : Fin M → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / (M : ℝ)) * ∑ i : Fin M,
    (∑ p : Fin N, ∑ q : Fin N,
      (star (B p i)) * X i p q * B q i).re

/-- The condition that a complex matrix is Hermitian and every vector has a nonnegative real
quadratic form. -/
def IsPSD {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  M.conjTranspose = M ∧
    ∀ v : Fin N → ℂ,
      0 ≤ (∑ p : Fin N, ∑ q : Fin N, (star (v p)) * M p q * v q).re

/-- The condition that all effects satisfy `IsPSD` and their sum is the identity matrix. -/
def IsMeasurement {N M : ℕ} (X : Fin M → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ i, IsPSD (X i)) ∧ (∑ i, X i) = 1

end Qatlib.Papers.HammingDist09.MainResults
