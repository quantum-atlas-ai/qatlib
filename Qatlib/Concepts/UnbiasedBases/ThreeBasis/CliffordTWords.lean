/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore, Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CliffordTNet

/-!
# Clifford-T Words and Recursive Length Bounds

Words over `Fin 3` represent the gates H, T, and T to the seventh power through `ctGen`, and
`ctEval` multiplies these matrices in list order. The equivalence
`mem_cliffordT_iff_exists_word` identifies their values with the Clifford-T submonoid. Reversing
a word and replacing each letter with `ctInvLetter` produces `ctInvWord`, which has the same
length and evaluates to a left inverse.

The theorem `exists_word_net` lifts a finite matrix net to a finite family of words with a
common length bound. The recursive sets `skWords` use a commutator word followed by a third
word, matching the word construction in Solovay-Kitaev recursion [DawsonNielsen2006]. The bound
`length_le_of_mem_skWords` controls length by `5 ^ n * ℓ₀`; this module establishes the word
algebra and length estimate without an approximation-error recurrence.

## Main statements

- `mem_cliffordT_iff_exists_word` characterizes Clifford-T matrices by finite words.
- `ctEval_ctInvWord` and `length_ctInvWord` give inverse evaluation and preservation of length.
- `exists_word_net` supplies finite nets represented by words of uniformly bounded length.
- `length_le_of_mem_skWords` bounds lengths in each recursive level by `5 ^ n * ℓ₀`.

## References

- [Dawson and Nielsen, 2006][DawsonNielsen2006], *The Solovay-Kitaev algorithm*.
-/

open Qatlib.Concepts.UnbiasedBases.ThreeBasis

section

open Matrix

open scoped Matrix.Norms.L2Operator

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

open CliffordT

/-- This three-letter gate alphabet has values `hGateM`, `tGateM`, and `tGateM ^ 7`, indexed by
zero, one, and two respectively. -/
noncomputable def ctGen : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![hGateM, tGateM, tGateM ^ 7]

/-- This letter map fixes zero and interchanges one and two, so that each letter is replaced by
the letter for its inverse gate. -/
def ctInvLetter : Fin 3 → Fin 3 := ![0, 2, 1]

/-- Evaluates a finite gate word by mapping its letters through `ctGen` and multiplying the
resulting matrices in list order. -/
noncomputable def ctEval (w : List (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ := (w.map ctGen).prod

/-- The empty gate word evaluates to the identity matrix. -/
@[simp] theorem ctEval_nil : ctEval [] = 1 := rfl

/-- Evaluating a word with first letter `x` gives `ctGen x` multiplied on the left of the
evaluation of the remaining word. -/
theorem ctEval_cons (x : Fin 3) (w : List (Fin 3)) :
    ctEval (x :: w) = ctGen x * ctEval w := by
  simp [ctEval]

/-- The evaluation of two concatenated words is the product of their evaluations in the same
order. -/
theorem ctEval_append (v w : List (Fin 3)) : ctEval (v ++ w) = ctEval v * ctEval w := by
  simp [ctEval, List.prod_append]

/-- Each of the three matrices in the gate alphabet belongs to the Clifford-T submonoid. -/
theorem ctGen_mem_cliffordT (i : Fin 3) : ctGen i ∈ cliffordT := by
  fin_cases i
  · simpa [ctGen] using hGateM_mem
  · simpa [ctGen] using tGateM_mem
  · simpa [ctGen] using pow_mem tGateM_mem 7

/-- Every finite gate word evaluates to an element of the Clifford-T submonoid. -/
theorem ctEval_mem_cliffordT (w : List (Fin 3)) : ctEval w ∈ cliffordT := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      rw [ctEval_cons]
      exact mul_mem (ctGen_mem_cliffordT x) ih

/-- This submonoid consists of the matrices represented as `ctEval w` for some finite word `w`,
with multiplication represented by word concatenation. -/
noncomputable def ctValues : Submonoid (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {A | ∃ w, ctEval w = A}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro A B ⟨v, hv⟩ ⟨w, hw⟩
    exact ⟨v ++ w, by rw [ctEval_append, hv, hw]⟩

/-- A matrix belongs to the Clifford-T submonoid exactly when it is the evaluation of a finite
word over the three-letter alphabet. -/
theorem mem_cliffordT_iff_exists_word {A : Matrix (Fin 2) (Fin 2) ℂ} :
    A ∈ cliffordT ↔ ∃ w, ctEval w = A := by
  constructor
  · intro hA
    have hle : cliffordT ≤ ctValues := by
      rw [cliffordT, Submonoid.closure_le]
      intro B hB
      rcases hB with h | h
      · exact ⟨[0], by rw [ctEval_cons, ctEval_nil, mul_one]; simpa [ctGen] using h.symm⟩
      · refine ⟨[1], ?_⟩
        simp only [Set.mem_singleton_iff] at h
        rw [ctEval_cons, ctEval_nil, mul_one, h]
        simp [ctGen]
    exact hle hA
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact ctEval_mem_cliffordT w

/-- Forms the inverse word by replacing each letter with `ctInvLetter` and reversing the
resulting list. -/
def ctInvWord (w : List (Fin 3)) : List (Fin 3) := (w.map ctInvLetter).reverse

/-- The inverse word `ctInvWord w` has the same length as `w`. -/
@[simp] theorem length_ctInvWord (w : List (Fin 3)) : (ctInvWord w).length = w.length := by
  simp [ctInvWord]

/-- The gate for `ctInvLetter i` multiplied by the gate for `i` is the identity matrix. -/
theorem ctGen_invLetter_mul (i : Fin 3) : ctGen (ctInvLetter i) * ctGen i = 1 := by
  fin_cases i
  · simpa [ctGen, ctInvLetter] using hGateM_mul_self
  · have h : tGateM ^ 7 * tGateM = tGateM ^ 8 := by rw [← pow_succ]
    simpa [ctGen, ctInvLetter] using h.trans tGateM_pow_eight
  · have h : tGateM * tGateM ^ 7 = tGateM ^ 8 := by rw [← pow_succ']
    simpa [ctGen, ctInvLetter] using h.trans tGateM_pow_eight

/-- The inverse of a word beginning with `x` is the inverse of its remaining word followed by
the single inverse letter `ctInvLetter x`. -/
theorem ctInvWord_cons (x : Fin 3) (w : List (Fin 3)) :
    ctInvWord (x :: w) = ctInvWord w ++ [ctInvLetter x] := by
  simp [ctInvWord]

/-- The evaluation of `ctInvWord w` is a left inverse of the evaluation of `w`. -/
theorem ctEval_ctInvWord (w : List (Fin 3)) : ctEval (ctInvWord w) * ctEval w = 1 := by
  induction w with
  | nil => simp [ctInvWord]
  | cons x xs ih =>
      rw [ctInvWord_cons, ctEval_append, ctEval_cons, ctEval_cons, ctEval_nil, mul_one]
      calc ctEval (ctInvWord xs) * ctGen (ctInvLetter x) * (ctGen x * ctEval xs)
          = ctEval (ctInvWord xs) * (ctGen (ctInvLetter x) * ctGen x) * ctEval xs := by
            noncomm_ring
        _ = 1 := by rw [ctGen_invLetter_mul, mul_one, ih]

open Classical in

/-- Chooses a word evaluating to `A` when such a word exists, and returns the empty word
otherwise. The choice is noncomputable and supplies no minimal-length guarantee. -/
noncomputable def wordOf (A : Matrix (Fin 2) (Fin 2) ℂ) : List (Fin 3) :=
  if h : ∃ w, ctEval w = A then h.choose else []

/-- For a matrix `A` in the Clifford-T submonoid, the chosen word `wordOf A` evaluates to `A`. -/
theorem ctEval_wordOf {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ cliffordT) :
    ctEval (wordOf A) = A := by
  have hex : ∃ w, ctEval w = A := mem_cliffordT_iff_exists_word.1 hA
  rw [wordOf, dif_pos hex]
  exact hex.choose_spec

/-- For every positive `ε`, there are a finite family of words and a common length bound such
that all words satisfy the bound and their evaluations approximate every element of `su2Set`
within `ε`. This supplies the finite initial word net used in Solovay-Kitaev recursion
[DawsonNielsen2006]. -/
theorem exists_word_net {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset (List (Fin 3))) (ℓ₀ : ℕ),
      (∀ w ∈ F, w.length ≤ ℓ₀) ∧
      ∀ U ∈ su2Set, ∃ w ∈ F, dist U (ctEval w) < ε := by
  classical
  obtain ⟨F₀, hF₀mem, hF₀net⟩ := exists_finite_cliffordT_net hε
  refine ⟨F₀.image wordOf, (F₀.image wordOf).sup List.length, ?_, ?_⟩
  · intro w hw
    exact Finset.le_sup hw
  · intro U hU
    obtain ⟨A, hA, hdist⟩ := hF₀net U hU
    refine ⟨wordOf A, Finset.mem_image_of_mem _ hA, ?_⟩
    rwa [ctEval_wordOf (hF₀mem A hA)]

/-- Defines recursive word sets starting from `F`, where each next-level word is `v ++ w ++
ctInvWord v ++ ctInvWord w ++ a` for three words from the preceding level. This is the
commutator-and-correction word pattern of [DawsonNielsen2006]. -/
def skWords (F : Finset (List (Fin 3))) : ℕ → Set (List (Fin 3))
  | 0 => ↑F
  | n + 1 => {u | ∃ v ∈ skWords F n, ∃ w ∈ skWords F n, ∃ a ∈ skWords F n,
      u = v ++ w ++ ctInvWord v ++ ctInvWord w ++ a}

/-- If every word in `F` has length at most `ℓ₀`, then every word in `skWords F n` has length at
most `5 ^ n * ℓ₀`. The factor of five records the five word blocks in each recursive step
[DawsonNielsen2006]. -/
theorem length_le_of_mem_skWords {F : Finset (List (Fin 3))} {ℓ₀ : ℕ}
    (hF : ∀ w ∈ F, w.length ≤ ℓ₀) (n : ℕ) :
    ∀ u ∈ skWords F n, u.length ≤ 5 ^ n * ℓ₀ := by
  induction n with
  | zero =>
      intro u hu
      simpa using hF u hu
  | succ n ih =>
      rintro u ⟨v, hv, w, hw, a, ha, rfl⟩
      have hv' := ih v hv
      have hw' := ih w hw
      have ha' := ih a ha
      have hlen : (v ++ w ++ ctInvWord v ++ ctInvWord w ++ a).length
          = v.length + w.length + v.length + w.length + a.length := by
        simp [length_ctInvWord]
        ring
      rw [hlen]
      calc v.length + w.length + v.length + w.length + a.length
          ≤ 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ + 5 ^ n * ℓ₀ :=
            Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hv' hw') hv') hw') ha'
        _ = 5 ^ (n + 1) * ℓ₀ := by ring

/-- Every word belonging to any level `skWords F n` evaluates to an element of the Clifford-T
submonoid. -/
theorem ctEval_mem_cliffordT_of_mem_skWords {F : Finset (List (Fin 3))} (n : ℕ) :
    ∀ u ∈ skWords F n, ctEval u ∈ cliffordT := fun u _ => ctEval_mem_cliffordT u

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.QuantumInfo.SU2

end
