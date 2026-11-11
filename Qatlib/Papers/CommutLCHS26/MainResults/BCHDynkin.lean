/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Dynkin maps and primitive word elements

This module constructs the rational word algebra `WordAlg`, its coproduct, and the Dynkin map
`dynkin` sending words to right nested commutators. The split convolutions and `contract`
identify the Dynkin map with the grading map on primitive elements.

A primitive homogeneous element of positive degree is therefore a coefficient weighted sum of
right nested brackets divided by its degree. The evaluation map `evaluateWords` transports this
identity to rational algebras for the BCH analysis of [AftabAnTrivisa2026].

## Main statements

* `contract_coproduct`: identifies coproduct contraction with the Dynkin map.
* `primitive_eq_bracket_sum`: expands positive degree primitive homogeneous elements into
  brackets.
* `grading_mul`: proves the grading product rule.
* `evaluateWords_rightBracket`: transports nested brackets under word evaluation.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace MonoidAlgebra
variable {k G : Type*} [Semiring k]
/-- The finite support of the coefficient function of a monoid algebra element. -/
abbrev support (p : MonoidAlgebra k G) : Finset G := p.coeff.support
/-- The finite sum of a function of the indices and coefficients of a monoid algebra element. -/
abbrev sum {N : Type*} [AddCommMonoid N] (p : MonoidAlgebra k G) (g : G → k → N) : N :=
  p.coeff.sum g
instance : CoeFun (MonoidAlgebra k G) (fun _ => G → k) := ⟨fun p => p.coeff⟩
end MonoidAlgebra

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHDynkin

open scoped BigOperators MonoidAlgebra

variable {A : Type} [Ring A]

/-- All assignments of a word's positions to two order preserving subwords, retaining
multiplicities. -/
def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: w => (splits w).flatMap fun p => [(a :: p.1, p.2), (p.1, a :: p.2)]

/-- The sum of `F` over all ordered subword splits of a word. -/
def splitSum {α : Type} (w : List α) (F : List α → List α → A) : A :=
  ((splits w).map fun p => F p.1 p.2).sum

/-- The split sum of the empty word is `F [] []`. -/
theorem splitSum_nil {α : Type} (F : List α → List α → A) : splitSum [] F = F [] [] := by
  simp [splitSum, splits]

/-- Splitting a word with a leading letter assigns that letter to either the left or the right
subword. -/
theorem splitSum_cons {α : Type} (a : α) (w : List α) (F : List α → List α → A) :
    splitSum (a :: w) F = splitSum w (fun l r => F (a :: l) r + F l (a :: r)) := by
  simp only [splitSum, splits, List.map_flatMap]
  induction splits w with
  | nil => simp
  | cons p ps ih => simp_all; abel

/-- Split sums preserve pointwise addition. -/
theorem splitSum_add {α : Type} (w : List α) (F G : List α → List α → A) :
    splitSum w (fun l r => F l r + G l r) = splitSum w F + splitSum w G := by
  simp only [splitSum, List.sum_map_add]

/-- Split sums preserve pointwise negation. -/
theorem splitSum_neg {α : Type} (w : List α) (F : List α → List α → A) :
    splitSum w (fun l r => -F l r) = -splitSum w F := by
  unfold splitSum
  induction splits w with
  | nil => simp
  | cons p ps ih => simp [ih]; abel

/-- A common left multiplication factor can be taken outside a split sum. -/
theorem splitSum_mul_left {α : Type} (w : List α) (a : A) (F : List α → List α → A) :
    splitSum w (fun l r => a * F l r) = a * splitSum w F := by
  exact List.sum_map_mul_left (splits w) (fun p => F p.1 p.2) a

/-- A common right multiplication factor can be taken outside a split sum. -/
theorem splitSum_mul_right {α : Type} (w : List α) (a : A) (F : List α → List α → A) :
    splitSum w (fun l r => F l r * a) = splitSum w F * a := by
  exact List.sum_map_mul_right (splits w) (fun p => F p.1 p.2) a

/-- The signed reversed product of a word, with value one on the empty word. -/
def antipodeWord : List A → A
  | [] => 1
  | a :: w => -antipodeWord w * a

/-- The split sum of the left subword product times the antipode of the right subword. -/
def antipodeConvolution (w : List A) : A :=
  splitSum w fun l r => l.prod * antipodeWord r

/-- The antipode split convolution weighted by the length of the left subword. -/
def dynkinConvolution (w : List A) : A :=
  splitSum w fun l r => l.length • (l.prod * antipodeWord r)

/-- The antipode convolution of a word with a leading letter is the commutator of that letter
with the convolution of the remaining word. -/
theorem antipodeConvolution_cons (a : A) (w : List A) :
    antipodeConvolution (a :: w) =
      a * antipodeConvolution w - antipodeConvolution w * a := by
  simp only [antipodeConvolution, splitSum_cons, List.prod_cons, antipodeWord]
  have he (l r : List A) : (a * l.prod) * antipodeWord r + l.prod * (-antipodeWord r * a) =
      a * (l.prod * antipodeWord r) + -(l.prod * antipodeWord r * a) := by noncomm_ring
  simp_rw [he]
  rw [splitSum_add, splitSum_neg, splitSum_mul_left, splitSum_mul_right]
  exact (sub_eq_add_neg _ _).symm

/-- The antipode convolution vanishes on every nonempty word. -/
theorem antipodeConvolution_cons_zero (a : A) (w : List A) :
    antipodeConvolution (a :: w) = 0 := by
  induction w generalizing a with
  | nil =>
    rw [antipodeConvolution_cons]
    simp [antipodeConvolution, splitSum_nil, antipodeWord]
  | cons b w ih => rw [antipodeConvolution_cons, ih b]; simp

/-- The Dynkin convolution of a word with a leading letter satisfies a commutator recurrence
with an antipode convolution correction. -/
theorem dynkinConvolution_cons (a : A) (w : List A) :
    dynkinConvolution (a :: w) = a * dynkinConvolution w - dynkinConvolution w * a +
      a * antipodeConvolution w := by
  simp only [dynkinConvolution, splitSum_cons, List.length_cons, List.prod_cons, antipodeWord]
  have he (l r : List A) :
      (l.length + 1) • ((a * l.prod) * antipodeWord r) +
          l.length • (l.prod * (-antipodeWord r * a)) =
        (a * (l.length • (l.prod * antipodeWord r)) +
          -((l.length • (l.prod * antipodeWord r)) * a)) + a * (l.prod * antipodeWord r) := by
    simp only [add_nsmul, one_nsmul, mul_smul_comm, smul_mul_assoc, mul_assoc, mul_neg,
      neg_mul, smul_neg]
    abel
  simp_rw [he]
  rw [splitSum_add, splitSum_add, splitSum_neg, splitSum_mul_left, splitSum_mul_right,
    splitSum_mul_left]
  simp only [antipodeConvolution, sub_eq_add_neg]

/-- The right nested commutator of a word, taking a singleton to its entry and the empty word to
zero. -/
def rightBracket : List A → A
  | [] => 0
  | [a] => a
  | a :: b :: w => a * rightBracket (b :: w) - rightBracket (b :: w) * a

/-- The Dynkin split convolution equals the right nested commutator. -/
theorem dynkinConvolution_eq_rightBracket (w : List A) : dynkinConvolution w = rightBracket w := by
  induction w with
  | nil => simp [dynkinConvolution, splitSum_nil, rightBracket]
  | cons a w ih =>
    cases w with
    | nil =>
      rw [dynkinConvolution_cons]
      simp [dynkinConvolution, antipodeConvolution, splitSum_nil, antipodeWord, rightBracket]
    | cons b w => rw [dynkinConvolution_cons, antipodeConvolution_cons_zero, mul_zero,
        add_zero, ih, rightBracket]

/-- Mapping a word before a split sum is equivalent to mapping both subwords in the summand. -/
theorem splitSum_map {α β : Type} (w : List α) (f : α → β)
    (F : List β → List β → A) :
    splitSum (w.map f) F = splitSum w (fun l r => F (l.map f) (r.map f)) := by
  induction w generalizing F with
  | nil => simp [splitSum_nil]
  | cons a w ih =>
    rw [List.map_cons, splitSum_cons, ih, splitSum_cons]
    rfl

/-- The rational monoid algebra of words in the alphabet `α`. -/
abbrev WordAlg (α : Type) := MonoidAlgebra ℚ (FreeMonoid α)

/-- The rational monoid algebra of pairs of words in the alphabet `α`. -/
abbrev PairAlg (α : Type) := MonoidAlgebra ℚ (FreeMonoid α × FreeMonoid α)

variable {α : Type}

/-- The basis element corresponding to a single letter. -/
def letter (a : α) : WordAlg α := MonoidAlgebra.single (FreeMonoid.of a) 1

/-- The basis element corresponding to a list of letters. -/
def word (w : List α) : WordAlg α := MonoidAlgebra.single (FreeMonoid.ofList w) 1

/-- The basis element of a word with a leading letter factors as that letter times the remaining
word. -/
theorem word_cons (a : α) (w : List α) : word (a :: w) = letter a * word w := by
  simp [word, letter, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_cons]

/-- A word basis element is the ordered product of its letter basis elements. -/
theorem word_eq_prod (w : List α) : word w = (w.map letter).prod := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [word_cons, List.map_cons, List.prod_cons, ih]

/-- The basis element corresponding to a pair of lists of letters. -/
def pairWord (l r : List α) : PairAlg α :=
  MonoidAlgebra.single (FreeMonoid.ofList l, FreeMonoid.ofList r) 1

/-- Multiplying on the left by a letter in the first component prepends that letter to the left
word. -/
theorem pairWord_left (a : α) (l r : List α) :
    pairWord [a] [] * pairWord l r = pairWord (a :: l) r := by
  simp [pairWord, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_cons]

/-- Multiplying on the left by a letter in the second component prepends that letter to the
right word. -/
theorem pairWord_right (a : α) (l r : List α) :
    pairWord [] [a] * pairWord l r = pairWord l (a :: r) := by
  simp [pairWord, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_cons]

/-- The algebra homomorphism sending each letter to its sum in the two word components. -/
def coproduct : WordAlg α →ₐ[ℚ] PairAlg α :=
  MonoidAlgebra.lift ℚ (PairAlg α) (FreeMonoid α)
    (FreeMonoid.lift fun a => pairWord [a] [] + pairWord [] [a])

/-- The coproduct of a letter is the sum of its left and right embeddings. -/
theorem coproduct_letter (a : α) :
    coproduct (letter a) = pairWord [a] [] + pairWord [] [a] := by
  simp [coproduct, letter]

/-- The coproduct of a word is the sum over all ordered subword splits. -/
theorem coproduct_word (w : List α) : coproduct (word w) = splitSum w pairWord := by
  induction w with
  | nil =>
    rw [splitSum_nil]
    change coproduct (1 : WordAlg α) = 1
    exact map_one _
  | cons a w ih =>
    rw [word_cons, map_mul, coproduct_letter, ih, splitSum_cons, add_mul]
    rw [← splitSum_mul_left, ← splitSum_mul_left, ← splitSum_add]
    simp only [pairWord_left, pairWord_right]

/-- The rational linear map sending each word to its right nested commutator. -/
def dynkin : WordAlg α →ₗ[ℚ] WordAlg α :=
  (Finsupp.linearCombination ℚ fun w : FreeMonoid α => rightBracket (w.toList.map letter)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- The rational linear map multiplying each word by its length. -/
def grading : WordAlg α →ₗ[ℚ] WordAlg α :=
  (Finsupp.linearCombination ℚ fun w : FreeMonoid α => w.toList.length • word w.toList) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- The linear contraction of a word pair to the left word times the antipode of the right word,
weighted by the left word length. -/
def contract : PairAlg α →ₗ[ℚ] WordAlg α :=
  (Finsupp.linearCombination ℚ fun p : FreeMonoid α × FreeMonoid α => p.1.toList.length •
    (word p.1.toList * antipodeWord (p.2.toList.map letter))) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

/-- Contracting a word pair gives the left word length times the left word multiplied by the
antipode of the right word. -/
theorem contract_pairWord (l r : List α) :
    contract (pairWord l r) = l.length • (word l * antipodeWord (r.map letter)) := by
  change (Finsupp.linearCombination ℚ (fun p : FreeMonoid α × FreeMonoid α =>
    p.1.toList.length • (word p.1.toList * antipodeWord (p.2.toList.map letter))))
      (Finsupp.single (FreeMonoid.ofList l, FreeMonoid.ofList r) 1) = _
  rw [Finsupp.linearCombination_single]
  simp only [FreeMonoid.toList_ofList, one_smul]

/-- Contraction carries the coproduct split sum to the corresponding length weighted antipode
split sum. -/
theorem contract_splitSum (w : List α) :
    contract (splitSum w pairWord) =
      splitSum w (fun l r => l.length • (word l * antipodeWord (r.map letter))) := by
  simp only [splitSum, map_list_sum, List.map_map, Function.comp_def, contract_pairWord]

/-- Contracting the coproduct of a word yields its right nested commutator. -/
theorem contract_coproduct_word (w : List α) :
    contract (coproduct (word w)) = rightBracket (w.map letter) := by
  rw [coproduct_word, contract_splitSum]
  have hd := dynkinConvolution_eq_rightBracket (w.map letter)
  simpa only [dynkinConvolution, splitSum_map, List.length_map, ← word_eq_prod] using hd

/-- The Dynkin map sends a scaled word basis element to the equally scaled right nested
commutator. -/
theorem dynkin_single (w : FreeMonoid α) (c : ℚ) :
    dynkin (MonoidAlgebra.single w c) = c • rightBracket (w.toList.map letter) := by
  exact Finsupp.linearCombination_single ℚ
      (v := fun w : FreeMonoid α => rightBracket (w.toList.map letter)) c w

/-- The Dynkin map is the coefficient weighted sum of right nested commutators over the word
support. -/
theorem dynkin_apply (p : WordAlg α) :
    dynkin p = p.sum (fun w c => c • rightBracket (w.toList.map letter)) := rfl

/-- The coproduct of a scaled word basis element is the same scalar times the coproduct of that
word. -/
theorem coproduct_single (w : FreeMonoid α) (c : ℚ) :
    coproduct (MonoidAlgebra.single w c) = c • coproduct (word w.toList) := by
  have hw : MonoidAlgebra.single w c = c • word w.toList := by simp [word]
  rw [hw, map_smul]

/-- Contraction composed with the coproduct is the Dynkin linear map. -/
theorem contract_coproduct : contract.comp coproduct.toLinearMap = (dynkin : WordAlg α →ₗ[ℚ] WordAlg α) := by
  apply MonoidAlgebra.lhom_ext'
  intro w
  apply LinearMap.ext
  intro c
  change contract (coproduct (MonoidAlgebra.single w c)) = dynkin (MonoidAlgebra.single w c)
  rw [coproduct_single, map_smul, contract_coproduct_word, dynkin_single]

/-- The algebra embedding placing a word in the left component and the empty word in the right
component. -/
def leftEmbedding : WordAlg α →ₐ[ℚ] PairAlg α :=
  MonoidAlgebra.lift ℚ (PairAlg α) (FreeMonoid α)
    { toFun := fun w => MonoidAlgebra.single (w, 1) 1
      map_one' := rfl
      map_mul' := by intros; simp [MonoidAlgebra.single_mul_single] }

/-- The algebra embedding placing a word in the right component and the empty word in the left
component. -/
def rightEmbedding : WordAlg α →ₐ[ℚ] PairAlg α :=
  MonoidAlgebra.lift ℚ (PairAlg α) (FreeMonoid α)
    { toFun := fun w => MonoidAlgebra.single (1, w) 1
      map_one' := rfl
      map_mul' := by intros; simp [MonoidAlgebra.single_mul_single] }

/-- The left embedding of a scaled word basis element is the corresponding scaled left word
pair. -/
theorem leftEmbedding_single (w : FreeMonoid α) (c : ℚ) :
    leftEmbedding (MonoidAlgebra.single w c) = c • pairWord w.toList [] := by
  rw [leftEmbedding, MonoidAlgebra.lift_single]
  rfl

/-- The right embedding of a scaled word basis element is the corresponding scaled right word
pair. -/
theorem rightEmbedding_single (w : FreeMonoid α) (c : ℚ) :
    rightEmbedding (MonoidAlgebra.single w c) = c • pairWord [] w.toList := by
  rw [rightEmbedding, MonoidAlgebra.lift_single]
  rfl

/-- Grading a scaled word basis element multiplies it by its word length. -/
theorem grading_single (w : FreeMonoid α) (c : ℚ) :
    grading (MonoidAlgebra.single w c) = c • (w.toList.length • word w.toList) := by
  exact Finsupp.linearCombination_single ℚ
      (v := fun w : FreeMonoid α => w.toList.length • word w.toList) c w

/-- Contraction composed with the left embedding is the grading map. -/
theorem contract_leftEmbedding :
    contract.comp leftEmbedding.toLinearMap = (grading : WordAlg α →ₗ[ℚ] WordAlg α) := by
  apply MonoidAlgebra.lhom_ext'
  intro w
  apply LinearMap.ext
  intro c
  change contract (leftEmbedding (MonoidAlgebra.single w c)) = grading (MonoidAlgebra.single w c)
  rw [leftEmbedding_single, map_smul, contract_pairWord, grading_single]
  simp only [List.map_nil, antipodeWord, mul_one]

/-- Contraction composed with the right embedding is zero. -/
theorem contract_rightEmbedding :
    contract.comp rightEmbedding.toLinearMap = (0 : WordAlg α →ₗ[ℚ] WordAlg α) := by
  apply MonoidAlgebra.lhom_ext'
  intro w
  apply LinearMap.ext
  intro c
  change contract (rightEmbedding (MonoidAlgebra.single w c)) = 0
  rw [rightEmbedding_single, map_smul, contract_pairWord]
  simp only [List.length_nil, zero_nsmul, smul_zero]

/-- A word algebra element is primitive when its coproduct is the sum of its left and right
embeddings. -/
def IsPrimitive (p : WordAlg α) : Prop := coproduct p = leftEmbedding p + rightEmbedding p

/-- The Dynkin map agrees with the grading map on primitive elements. -/
theorem dynkin_eq_grading {p : WordAlg α} (hp : IsPrimitive p) : dynkin p = grading p := by
  calc
    _ = contract (coproduct p) := (LinearMap.congr_fun contract_coproduct p).symm
    _ = contract (leftEmbedding p) + contract (rightEmbedding p) := by rw [hp, map_add]
    _ = _ := by
      have hl : contract (leftEmbedding p) = grading p :=
          LinearMap.congr_fun contract_leftEmbedding p
      have hr : contract (rightEmbedding p) = 0 := LinearMap.congr_fun contract_rightEmbedding p
      rw [hl, hr]
      simp only [add_zero]

/-- The coefficient weighted sum of the word basis elements reconstructs a word algebra element. -/
theorem sum_words (p : WordAlg α) : p.sum (fun w c => c • word w.toList) = p := by
  simp only [word, FreeMonoid.ofList_toList, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  exact p.sum_coeff_single

/-- The grading map multiplies an element supported on words of length `n` by `n`. -/
theorem grading_homogeneous (p : WordAlg α) (n : ℕ)
    (hdegree : ∀ w ∈ p.support, w.toList.length = n) : grading p = n • p := by
  have hs : (∑ w ∈ p.support, p w • word w.toList) = p := sum_words p
  change (∑ w ∈ p.support, p w • (w.toList.length • word w.toList)) = n • p
  conv_rhs => rw [← hs]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hdegree w hw]
  exact smul_comm _ _ _

/-- The Dynkin map multiplies a primitive element supported in degree `n` by `n`. -/
theorem dynkin_primitive_homogeneous (p : WordAlg α) (n : ℕ) (hp : IsPrimitive p)
    (hdegree : ∀ w ∈ p.support, w.toList.length = n) : dynkin p = n • p := by
  rw [dynkin_eq_grading hp, grading_homogeneous p n hdegree]

/-- A primitive homogeneous element of positive degree equals its Dynkin image divided by that
degree. -/
theorem primitive_eq_dynkin (p : WordAlg α) (n : ℕ) (hn : 0 < n) (hp : IsPrimitive p)
    (hdegree : ∀ w ∈ p.support, w.toList.length = n) : p = (n : ℚ)⁻¹ • dynkin p := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [dynkin_primitive_homogeneous p n hp hdegree, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, inv_mul_cancel₀ hn0, one_smul]

/-- A primitive homogeneous element of positive degree is the sum of its word coefficients
divided by the degree times the corresponding right nested commutators. -/
theorem primitive_eq_bracket_sum (p : WordAlg α) (n : ℕ) (hn : 0 < n) (hp : IsPrimitive p)
    (hdegree : ∀ w ∈ p.support, w.toList.length = n) :
    p = ∑ w ∈ p.support, (p w / (n : ℚ)) • rightBracket (w.toList.map letter) := by
  have h := primitive_eq_dynkin p n hn hp hdegree
  rw [dynkin_apply] at h
  change p = (n : ℚ)⁻¹ • (∑ w ∈ p.support, p w • rightBracket (w.toList.map letter)) at h
  rw [Finset.smul_sum] at h
  simpa only [smul_smul, div_eq_mul_inv, mul_comm] using h

/-- Every left embedded element commutes with every right embedded element. -/
theorem commute_embeddings (p q : WordAlg α) : Commute (leftEmbedding p) (rightEmbedding q) := by
  have hsingle (w v : FreeMonoid α) :
      Commute (leftEmbedding (MonoidAlgebra.single w 1)) (rightEmbedding (MonoidAlgebra.single v 1)) := by
    rw [leftEmbedding_single, rightEmbedding_single]
    simp only [one_smul, Commute, SemiconjBy]
    simp [pairWord, MonoidAlgebra.single_mul_single]
  have hword (w : FreeMonoid α) (q : WordAlg α) :
      Commute (leftEmbedding (MonoidAlgebra.single w 1)) (rightEmbedding q) := by
    induction q using MonoidAlgebra.induction_on with
    | of v => exact hsingle w v
    | add q r hq hr => rw [map_add]; exact hq.add_right hr
    | smul c q hq => rw [map_smul]; exact hq.smul_right c
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hword w q
  | add p r hp hr => rw [map_add]; exact hp.add_left hr
  | smul c p hp => rw [map_smul]; exact hp.smul_left c

/-- Each letter basis element is primitive. -/
theorem primitive_letter (a : α) : IsPrimitive (letter a) := by
  rw [IsPrimitive, coproduct_letter]
  simp only [letter, leftEmbedding_single, rightEmbedding_single, FreeMonoid.toList_of, one_smul]

/-- The zero word algebra element is primitive. -/
theorem primitive_zero : IsPrimitive (0 : WordAlg α) := by simp [IsPrimitive]

/-- The sum of two primitive elements is primitive. -/
theorem IsPrimitive.add {p q : WordAlg α} (hp : IsPrimitive p) (hq : IsPrimitive q) :
    IsPrimitive (p + q) := by
  dsimp only [IsPrimitive] at *
  rw [map_add, hp, hq, map_add, map_add]
  abel

/-- A rational scalar multiple of a primitive element is primitive. -/
theorem IsPrimitive.smul {p : WordAlg α} (hp : IsPrimitive p) (c : ℚ) : IsPrimitive (c • p) := by
  dsimp only [IsPrimitive] at *
  rw [map_smul, hp, smul_add, map_smul, map_smul]

/-- The commutator of two primitive elements is primitive. -/
theorem IsPrimitive.bracket {p q : WordAlg α} (hp : IsPrimitive p) (hq : IsPrimitive q) :
    IsPrimitive (p * q - q * p) := by
  dsimp only [IsPrimitive] at *
  simp only [map_sub, map_mul, hp, hq, add_mul, mul_add]
  rw [(commute_embeddings p q).eq, (commute_embeddings q p).eq]
  abel

/-- Multiplication of word basis elements corresponds to concatenation. -/
theorem word_mul (u v : List α) : word u * word v = word (u ++ v) := by
  simp [word, MonoidAlgebra.single_mul_single, FreeMonoid.ofList_append]

/-- The grading of a word is its length times that word. -/
theorem grading_word (w : List α) : grading (word w) = w.length • word w := by
  rw [word, grading_single]
  simp only [FreeMonoid.toList_ofList, one_smul]
  rfl

/-- The grading map vanishes on the multiplicative identity. -/
theorem grading_one : grading (1 : WordAlg α) = 0 := by
  have h := grading_word ([] : List α)
  simpa only [word, FreeMonoid.ofList_nil, List.length_nil, zero_nsmul] using! h

/-- The grading map fixes each letter. -/
theorem grading_letter (a : α) : grading (letter a) = letter a := by
  simpa only [word, letter, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil, mul_one,
    List.length_cons, List.length_nil, Nat.zero_add, one_nsmul] using grading_word [a]

/-- Grading satisfies the product rule on word basis elements. -/
theorem grading_word_mul (u v : List α) :
    grading (word u * word v) = grading (word u) * word v + word u * grading (word v) := by
  rw [word_mul, grading_word, List.length_append, add_nsmul, grading_word, grading_word,
    smul_mul_assoc, mul_smul_comm, word_mul]

/-- The grading map is a derivation of the word algebra. -/
theorem grading_mul (p q : WordAlg α) : grading (p * q) = grading p * q + p * grading q := by
  have hw (w : FreeMonoid α) (q : WordAlg α) :
      grading (word w.toList * q) = grading (word w.toList) * q + word w.toList * grading q := by
    induction q using MonoidAlgebra.induction_on with
    | of v => exact grading_word_mul w.toList v.toList
    | add q r hq hr =>
      simp only [mul_add, map_add, hq, hr]
      abel
    | smul c q hq =>
      simp only [mul_smul_comm, map_smul, hq, smul_add]
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w q
  | add p r hp hr =>
    simp only [add_mul, map_add, hp, hr]
    abel
  | smul c p hp =>
    simp only [smul_mul_assoc, map_smul, hp, smul_add]

/-- If grading fixes an element, it multiplies its nth power by `n`. -/
theorem grading_pow_of_degree_one (p : WordAlg α) (hp : grading p = p) (n : ℕ) :
    grading (p ^ n) = n • p ^ n := by
  induction n with
  | zero => simp only [pow_zero, grading_one, zero_nsmul]
  | succ n ih =>
    rw [pow_succ, grading_mul, ih, hp, smul_mul_assoc, ← pow_succ, succ_nsmul]

section Evaluation
variable {B : Type} [Ring B] [Algebra ℚ B]

/-- The rational algebra homomorphism evaluating each letter at its assigned algebra element. -/
def evaluateWords (X : α → B) : WordAlg α →ₐ[ℚ] B :=
  MonoidAlgebra.lift ℚ B (FreeMonoid α) (FreeMonoid.lift X)

/-- Word evaluation sends a letter to its assigned value. -/
theorem evaluateWords_letter (X : α → B) (a : α) : evaluateWords X (letter a) = X a := by
  simp [evaluateWords, letter]

/-- Word evaluation sends a word to the ordered product of its assigned letter values. -/
theorem evaluateWords_word (X : α → B) (w : List α) : evaluateWords X (word w) = (w.map X).prod := by
  simp [evaluateWords, word, FreeMonoid.lift_ofList]

omit [Algebra ℚ B] in

/-- Ring homomorphisms preserve right nested commutators. -/
theorem rightBracket_map {C : Type} [Ring C] (f : B →+* C) (w : List B) :
    rightBracket (w.map f) = f (rightBracket w) := by
  induction w with
  | nil => simp only [List.map_nil, rightBracket, map_zero]
  | cons a w ih =>
    cases w with
    | nil => simp only [List.map_cons, List.map_nil, rightBracket]
    | cons b w =>
      simpa only [List.map_cons, rightBracket, map_sub, map_mul] using
        congrArg (fun r => f a * r - r * f a) ih

/-- Evaluating a right nested commutator of letters gives the right nested commutator of their
assigned values. -/
theorem evaluateWords_rightBracket (X : α → B) (w : List α) :
    evaluateWords X (rightBracket (w.map letter)) = rightBracket (w.map X) := by
  have h := rightBracket_map (evaluateWords X).toRingHom (w.map letter)
  simpa only [List.map_map, Function.comp_def, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, evaluateWords_letter] using h.symm

end Evaluation

/-- Grading multiplies each word coefficient by the word length. -/
theorem grading_coeff (p : WordAlg α) (w : FreeMonoid α) :
    (grading p).coeff w = w.toList.length • p.coeff w := by
  classical
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (grading (MonoidAlgebra.single v 1)).coeff w =
      w.toList.length • (MonoidAlgebra.single v 1).coeff w
    rw [grading_single]
    by_cases h : v = w
    · subst v
      simp [word]
    · simp [word, h]
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, smul_add]
  | smul c p hp =>
    rw [map_smul]
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, hp, nsmul_eq_mul]
    ring

/-- If grading multiplies an element by `n`, every word in its support has length `n`. -/
theorem support_length_of_grading (p : WordAlg α) (n : ℕ) (hp : grading p = n • p)
    (w : FreeMonoid α) (hw : w ∈ p.support) : w.toList.length = n := by
  have he := congrArg (fun q : WordAlg α => q.coeff w) hp
  change (grading p).coeff w = (n • p).coeff w at he
  rw [grading_coeff] at he
  change w.toList.length • p.coeff w = n • p.coeff w at he
  have hc : p.coeff w ≠ 0 := by simpa using! hw
  have hn : (w.toList.length : ℚ) = n := by
    apply mul_right_cancel₀ hc
    simpa only [nsmul_eq_mul] using he
  exact_mod_cast hn

end Qatlib.Papers.CommutLCHS26.MainResults.BCHDynkin
