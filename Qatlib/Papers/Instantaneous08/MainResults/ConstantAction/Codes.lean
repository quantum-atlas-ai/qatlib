/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.RankBias
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Binary code identities for constant-action programs

This module defines binary Hamming weight `hw`, parity `parity`, and the weight `extWt` after
appending a parity bit. It proves the two code averages used in Lemma 3 of [ShepherdBremner2009]
under explicit divisibility, closure, and dot-product hypotheses.

## Main statements

* `eq10_of_doublyEven`: evaluates the cosine-squared average for codes with doubly even
  extensions.
* `half_odd_of_odd_codeword`: counts odd codewords using translation by an odd codeword.
* `eq11_of_selfDual`: evaluates the pairwise orthogonality probability as `3 / 4` under the
  stated code hypotheses.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.ConstantAction

open Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox

attribute [local instance] Classical.propDecidable

/-- The squared cosine at `(8 * k + 1) * π / 8` equals the squared cosine at `π / 8`. -/
theorem cos_sq_pi_div_eight_one (k : ℤ) :
    Real.cos (Real.pi / 8 * ((8 * k + 1 : ℤ) : ℝ)) ^ 2 = Real.cos (Real.pi / 8) ^ 2 := by
  rw [Real.cos_sq, Real.cos_sq (Real.pi / 8)]
  have harg : 2 * (Real.pi / 8 * ((8 * k + 1 : ℤ) : ℝ)) =
      Real.pi / 4 + (k : ℝ) * (2 * Real.pi) := by push_cast; ring
  have harg2 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [harg, harg2, Real.cos_add_int_mul_two_pi]

/-- The squared cosine at `(8 * k + 7) * π / 8` equals the squared cosine at `π / 8`. -/
theorem cos_sq_pi_div_eight_seven (k : ℤ) :
    Real.cos (Real.pi / 8 * ((8 * k + 7 : ℤ) : ℝ)) ^ 2 = Real.cos (Real.pi / 8) ^ 2 := by
  rw [Real.cos_sq, Real.cos_sq (Real.pi / 8)]
  have harg : 2 * (Real.pi / 8 * ((8 * k + 7 : ℤ) : ℝ)) =
      -(Real.pi / 4) + ((k + 1 : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; ring
  have harg2 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring
  rw [harg, harg2, Real.cos_add_int_mul_two_pi, Real.cos_neg]

/-- The Hamming weight of a binary word, counted as the number of coordinates equal to `1`. -/
def hw {q : ℕ} (c : Fin q → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => c i = 1)).card

/-- The parity of a binary word, defined as the sum of its coordinates in `ZMod 2`. -/
def parity {q : ℕ} (c : Fin q → ZMod 2) : ZMod 2 := ∑ i, c i

/-- The Hamming weight after extending a binary word by its parity bit. -/
def extWt {q : ℕ} (c : Fin q → ZMod 2) : ℕ :=
  hw c + (if parity c = 1 then 1 else 0)

/-- The parity of a binary word is its Hamming weight reduced modulo two. -/
theorem parity_eq_hw_cast {q : ℕ} (c : Fin q → ZMod 2) :
    parity c = (hw c : ZMod 2) := by
  unfold parity hw
  have h : (∑ i : Fin q, c i) =
      ∑ i : Fin q, (if c i = 1 then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rcases ClassicalApprox.zmod2_eq_zero_or_one (c i) with h | h <;> simp [h]
  rw [h]
  exact Finset.sum_boole (fun i => c i = 1) Finset.univ

/-- If the parity-extended weight is divisible by four, the original weight is congruent to zero
or three modulo four. -/
theorem hw_cases_of_extWt {q : ℕ} (c : Fin q → ZMod 2)
    (h : (4 : ℤ) ∣ (extWt c : ℤ)) :
    (∃ a : ℤ, (hw c : ℤ) = 4 * a) ∨ (∃ a : ℤ, (hw c : ℤ) = 4 * a + 3) := by
  rcases ClassicalApprox.zmod2_eq_zero_or_one (parity c) with h0 | h1
  · left
    have hext : extWt c = hw c := by unfold extWt; rw [h0]; simp
    rw [hext] at h
    exact h
  · right
    have hext : extWt c = hw c + 1 := by unfold extWt; rw [h1]; simp
    rw [hext] at h
    have h' : (4 : ℤ) ∣ (hw c : ℤ) + 1 := by
      have := h
      push_cast at this
      exact this
    obtain ⟨a, ha⟩ := h'
    refine ⟨a - 1, ?_⟩
    have : (hw c : ℤ) = 4 * a - 1 := by linarith
    rw [this]; ring

/-- For length congruent to seven modulo eight and parity-extended weight divisible by four, the
codeword cosine square equals `cos (π / 8) ^ 2`. See [ShepherdBremner2009]. -/
theorem cos_sq_eq_of_doublyEven {q : ℕ} (hq : ∃ k : ℕ, q = 8 * k + 7)
    (c : Fin q → ZMod 2) (h : (4 : ℤ) ∣ (extWt c : ℤ)) :
    Real.cos (Real.pi / 8 * ((q : ℝ) - 2 * (hw c : ℝ))) ^ 2 =
      Real.cos (Real.pi / 8) ^ 2 := by
  obtain ⟨k, hk⟩ := hq
  have hqR : (q : ℝ) = 8 * (k : ℝ) + 7 := by rw [hk]; push_cast; ring
  rcases hw_cases_of_extWt c h with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hwR : (hw c : ℝ) = 4 * (a : ℝ) := by exact_mod_cast ha
    have hM : (q : ℝ) - 2 * (hw c : ℝ) = ((8 * ((k : ℤ) - a) + 7 : ℤ) : ℝ) := by
      rw [hqR, hwR]; push_cast; ring
    rw [hM]; exact cos_sq_pi_div_eight_seven _
  · have hwR : (hw c : ℝ) = 4 * (a : ℝ) + 3 := by exact_mod_cast ha
    have hM : (q : ℝ) - 2 * (hw c : ℝ) = ((8 * ((k : ℤ) - a) + 1 : ℤ) : ℝ) := by
      rw [hqR, hwR]; push_cast; ring
    rw [hM]; exact cos_sq_pi_div_eight_one _

/-- For a nonempty finite code of length congruent to seven modulo eight whose parity extensions
have weight divisible by four, the average cosine square equals `cos (π / 8) ^ 2`. See
[ShepherdBremner2009]. -/
theorem eq10_of_doublyEven {q : ℕ} (hq : ∃ k : ℕ, q = 8 * k + 7)
    (C : Finset (Fin q → ZMod 2)) (hne : C.Nonempty)
    (hde : ∀ c ∈ C, (4 : ℤ) ∣ (extWt c : ℤ)) :
    ((C.card : ℝ))⁻¹ *
        ∑ c ∈ C, Real.cos (Real.pi / 8 * ((q : ℝ) - 2 * (hw c : ℝ))) ^ 2 =
      Real.cos (Real.pi / 8) ^ 2 := by
  have hterm : ∀ c ∈ C,
      Real.cos (Real.pi / 8 * ((q : ℝ) - 2 * (hw c : ℝ))) ^ 2 =
        Real.cos (Real.pi / 8) ^ 2 := fun c hc =>
    cos_sq_eq_of_doublyEven hq c (hde c hc)
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((C.card : ℝ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Every binary word added to itself is zero. -/
theorem vec_add_self {q : ℕ} (z : Fin q → ZMod 2) : z + z = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (z i)

/-- Parity is additive under addition of binary words. -/
theorem parity_add {q : ℕ} (c1 c2 : Fin q → ZMod 2) :
    parity (c1 + c2) = parity c1 + parity c2 := by
  unfold parity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.add_apply]

/-- A product in `ZMod 2` vanishes if and only if at least one factor vanishes. -/
theorem zmod2_mul_eq_zero {a b : ZMod 2} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  rcases ClassicalApprox.zmod2_eq_zero_or_one a with ha | ha <;>
    rcases ClassicalApprox.zmod2_eq_zero_or_one b with hb | hb <;>
    rw [ha, hb] <;> decide

/-- The real indicator of a conjunction is the product of the real indicators. -/
theorem ind_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℝ) else 0) =
      (if p then 1 else 0) * (if q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The real indicator of a negation is one minus the real indicator of the original
proposition. -/
theorem ind_not (p : Prop) [Decidable p] :
    (if ¬ p then (1 : ℝ) else 0) = 1 - (if p then 1 else 0) := by
  by_cases hp : p <;> simp [hp]

/-- The real indicator that a binary word has odd parity. -/
def oddInd {q : ℕ} (c : Fin q → ZMod 2) : ℝ := if parity c = 1 then 1 else 0

/-- The sum of `oddInd` over a finite code is the number of its odd-parity words, viewed as a
real number. -/
theorem oddInd_sum_eq_card {q : ℕ} (C : Finset (Fin q → ZMod 2)) :
    (∑ c ∈ C, oddInd c) = ((C.filter (fun c => parity c = 1)).card : ℝ) := by
  unfold oddInd
  exact Finset.sum_boole (fun c => parity c = 1) C

/-- In a finite binary code containing zero and closed under addition, the existence of an odd
codeword implies that exactly half the codewords are odd. -/
theorem half_odd_of_odd_codeword {q : ℕ} (C : Finset (Fin q → ZMod 2))
    (_hc0 : (0 : Fin q → ZMod 2) ∈ C)
    (hadd : ∀ c1 ∈ C, ∀ c2 ∈ C, c1 + c2 ∈ C)
    (hodd : ∃ c0 ∈ C, parity c0 = 1) :
    2 * (C.filter (fun c => parity c = 1)).card = C.card := by
  obtain ⟨c0, hc0C, hpar⟩ := hodd
  classical
  set odd := C.filter (fun c => parity c = 1) with hodd_def
  set even := C.filter (fun c => parity c = 0) with heven_def
  have hpart : odd.card + even.card = C.card := by
    have h := Finset.card_filter_add_card_filter_not (s := C) (p := fun c => parity c = 1)
    have hfilter : C.filter (fun c => ¬ parity c = 1) =
        C.filter (fun c => parity c = 0) := by
      apply Finset.filter_congr
      intro c _
      constructor
      · intro hnc
        rcases ClassicalApprox.zmod2_eq_zero_or_one (parity c) with h0 | h1
        · exact h0
        · exact absurd h1 hnc
      · intro h0 h1; rw [h1] at h0; exact absurd h0 (by norm_num)
    rw [hfilter] at h
    simpa [odd, even] using h
  have hbij : odd.card = even.card := by
    apply Finset.card_bij (fun c _ => c + c0)
    · intro c hc
      simp only [odd, Finset.mem_filter] at hc
      obtain ⟨hcC, hpc⟩ := hc
      simp only [even, Finset.mem_filter]
      refine ⟨hadd c hcC c0 hc0C, ?_⟩
      rw [parity_add, hpc, hpar]
      decide
    · intro c1 _ c2 _ heq
      have h := congrArg (fun z => z + c0) heq
      simpa only [add_assoc, vec_add_self, add_zero] using h
    · intro b hb
      simp only [even, Finset.mem_filter] at hb
      obtain ⟨hbC, hpb⟩ := hb
      refine ⟨b + c0, ?_, ?_⟩
      · simp only [odd, Finset.mem_filter]
        refine ⟨hadd b hbC c0 hc0C, ?_⟩
        rw [parity_add, hpb, hpar]
        decide
      · rw [add_assoc, vec_add_self, add_zero]
  omega

/-- If dot products equal products of parities and the stated closure and odd-codeword
hypotheses hold, the probability that two uniform codewords are orthogonal is `3 / 4`, as in
[Shepherd and Bremner, Lemma 3][ShepherdBremner2009]. -/
theorem eq11_of_selfDual {q : ℕ} (C : Finset (Fin q → ZMod 2))
    (hne : C.Nonempty)
    (hc0 : (0 : Fin q → ZMod 2) ∈ C)
    (hadd : ∀ c1 ∈ C, ∀ c2 ∈ C, c1 + c2 ∈ C)
    (hself : ∀ c1 ∈ C, ∀ c2 ∈ C, dot c1 c2 = parity c1 * parity c2)
    (hodd : ∃ c0 ∈ C, parity c0 = 1) :
    ((C.card : ℝ))⁻¹ * ((C.card : ℝ))⁻¹ *
        ∑ c1 ∈ C, ∑ c2 ∈ C, (if dot c1 c2 = 0 then (1 : ℝ) else 0) = 3 / 4 := by
  classical
  have hcard : ((C.card : ℝ)) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  have hhalf : 2 * ((C.filter (fun c => parity c = 1)).card : ℝ) = (C.card : ℝ) := by
    have := half_odd_of_odd_codeword C hc0 hadd hodd
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this

  have hterm : ∀ c1 ∈ C, ∀ c2 ∈ C,
      (if dot c1 c2 = 0 then (1 : ℝ) else 0) = 1 - oddInd c1 * oddInd c2 := by
    intro c1 h1 c2 h2
    have hiff : dot c1 c2 = 0 ↔ ¬ (parity c1 = 1 ∧ parity c2 = 1) := by
      rw [hself c1 h1 c2 h2, zmod2_mul_eq_zero]
      constructor
      · rintro (h | h) ⟨hp1, hp2⟩
        · rw [h] at hp1; exact absurd hp1 (by norm_num)
        · rw [h] at hp2; exact absurd hp2 (by norm_num)
      · intro h
        by_contra hcon
        rw [not_or] at hcon
        obtain ⟨ha0, hb0⟩ := hcon
        have hp1 : parity c1 = 1 := by
          rcases ClassicalApprox.zmod2_eq_zero_or_one (parity c1) with hh | hh
          · exact absurd hh ha0
          · exact hh
        have hp2 : parity c2 = 1 := by
          rcases ClassicalApprox.zmod2_eq_zero_or_one (parity c2) with hh | hh
          · exact absurd hh hb0
          · exact hh
        exact h ⟨hp1, hp2⟩
    have hconv : (if dot c1 c2 = 0 then (1 : ℝ) else 0) =
        (if ¬ (parity c1 = 1 ∧ parity c2 = 1) then (1 : ℝ) else 0) := by
      by_cases h : dot c1 c2 = 0
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]
    rw [hconv]
    unfold oddInd
    rw [ind_not, ind_and]
  rw [Finset.sum_congr rfl (fun c1 h1 => Finset.sum_congr rfl (fun c2 h2 => hterm c1 h1 c2 h2))]

  have h_inner : ∀ c1 : Fin q → ZMod 2, (∑ c2 ∈ C, (1 - oddInd c1 * oddInd c2)) =
      (∑ c2 ∈ C, (1 : ℝ)) - ∑ c2 ∈ C, oddInd c1 * oddInd c2 := by
    intro c1
    exact Finset.sum_sub_distrib (f := fun _ => (1 : ℝ))
      (g := fun c2 => oddInd c1 * oddInd c2)
  rw [Finset.sum_congr rfl (fun c1 _ => h_inner c1)]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ c1 ∈ C, ∑ c2 ∈ C, (1 : ℝ)) = (C.card : ℝ) * (C.card : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ c1 ∈ C, ∑ c2 ∈ C, oddInd c1 * oddInd c2) =
      (∑ c1 ∈ C, oddInd c1) * (∑ c2 ∈ C, oddInd c2) := by
    rw [Finset.sum_mul_sum]
  rw [h1, h2, oddInd_sum_eq_card C]
  have hoddc : ((C.filter (fun c => parity c = 1)).card : ℝ) = (C.card : ℝ) / 2 := by
    linarith
  rw [hoddc]
  field_simp
  ring

end Qatlib.Papers.Instantaneous08.MainResults.ConstantAction
