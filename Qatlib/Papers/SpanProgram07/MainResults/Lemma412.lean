/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.WitnessSize
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Parity and OR span-program witnesses

This module constructs the two-input parity and weighted OR span programs used in Lemma 4.12 of
[ReichardtSpalek2008]. It characterizes their available column groups and proves exact
witness-size formulas, with a positive-witness upper bound for the all-true OR input.

## Main statements

* `parity_witness_size`: Collect the exact positive and negative parity witness sizes `B + B'`
  for the four specified weight and availability patterns.
* `or_witness_size`: Collect the exact OR witness sizes on the empty and singleton available
  sets and a positive-witness upper bound of `sqrt (B² + B'²)` when both columns are available.

## References

* [Reichardt and Spalek, 2008][ReichardtSpalek2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset
open SpanProgram
open scoped BigOperators

/-- When the auxiliary coordinate type is empty, a column pairing is the conjugate target
coordinate times `b none`. -/
theorem pair_empty_eq {n : ℕ} {J I : Type} (P : SpanProgram n J Empty I)
    (b : Option Empty → ℂ) (j : J) :
    P.pair b j = (starRingEnd ℂ) (P.v j none) * b none := by
  change (∑ k : Option Empty, (starRingEnd ℂ) (P.v j k) * b k) = _
  rw [Finset.sum_eq_single none]
  · intro k _ hk
    cases k with
    | none => exact absurd rfl hk
    | some e => exact e.elim
  · intro h
    exact absurd (Finset.mem_univ none) h

/-- The squared complex norm of a real number equals its real square. -/
theorem norm_real_sq (x : ℝ) : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The squared norm of the conjugate of a real complex number equals its real square. -/
theorem norm_conj_real_sq (x : ℝ) : ‖(starRingEnd ℂ) ((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
  have h : (starRingEnd ℂ) ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by simp
  rw [h, norm_real_sq]

/-- For columns identically one and no auxiliary coordinates, a finite linear combination equals
the target exactly when its coefficients sum to one. -/
theorem sum_smul_eq_target_empty {ι : Type} (S : Finset ι) (w : ι → ℂ)
    (v : ι → Option Empty → ℂ) (hv : ∀ j k, v j k = 1) :
    (∑ j ∈ S, w j • v j = target Empty) ↔ (∑ j ∈ S, w j) = 1 := by
  constructor
  · intro h
    have hn := congr_fun h none
    simpa [target, hv, Finset.sum_apply, Pi.smul_apply] using hn
  · intro h
    funext k
    cases k with
    | none => simpa [target, hv, Finset.sum_apply, Pi.smul_apply] using h
    | some e => exact e.elim

/-- With target coordinates one and normalized `b none`, the weighted sum of squared pairings
equals the sum of the weights. -/
theorem false_value_empty_const {n : ℕ} {J I : Type} [Fintype J] (z : J → ℝ)
    (P : SpanProgram n J Empty I) (hv : ∀ j, P.v j none = 1) (b : Option Empty → ℂ)
    (hb : b none = 1) :
    (∑ j, z j * ‖P.pair b j‖ ^ 2) = ∑ j, z j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_empty_eq P b j, hv j, map_one]
  simp [hb]

/-- Assign the first two parity literals to group zero and the last two to group one. -/
def parityGrp : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The parity literal list consisting of positive input zero, negative input one, negative
input zero, and positive input one. -/
def parityLit : Fin 4 → Lit 2 := ![Lit.pos 0, Lit.neg 1, Lit.neg 0, Lit.pos 1]

/-- The two-input parity span program with two constant columns and conjunctive literal groups
for the two unequal inputs. -/
def parityProgram : SpanProgram 2 (Fin 2) Empty (Fin 4) where
  grp := parityGrp
  lit := parityLit
  v _ _ := 1

/-- Parity group zero is available exactly when input zero is true and input one is false. -/
theorem parityGroupTrue_zero (x : Fin 2 → Bool) :
    parityProgram.groupTrue x 0 ↔ (x 0 = true ∧ x 1 = false) := by
  constructor
  · intro h
    have h0 : (parityLit 0).eval x = true := h 0 (by simp [parityProgram, parityGrp])
    have h1 : (parityLit 1).eval x = true := h 1 (by simp [parityProgram, parityGrp])
    have hx0 : x 0 = true := by simpa [parityLit, Lit.eval] using h0
    have hx1 : x 1 = false := by simpa [parityLit, Lit.eval] using h1
    exact ⟨hx0, hx1⟩
  · rintro ⟨h0, h1⟩ i hi
    fin_cases i <;> simp_all [parityProgram, parityGrp, parityLit, Lit.eval]

/-- Parity group one is available exactly when input zero is false and input one is true. -/
theorem parityGroupTrue_one (x : Fin 2 → Bool) :
    parityProgram.groupTrue x 1 ↔ (x 0 = false ∧ x 1 = true) := by
  constructor
  · intro h
    have h2 : (parityLit 2).eval x = true := h 2 (by simp [parityProgram, parityGrp])
    have h3 : (parityLit 3).eval x = true := h 3 (by simp [parityProgram, parityGrp])
    have hx0 : x 0 = false := by simpa [parityLit, Lit.eval] using h2
    have hx1 : x 1 = true := by simpa [parityLit, Lit.eval] using h3
    exact ⟨hx0, hx1⟩
  · rintro ⟨h0, h1⟩ i hi
    fin_cases i <;> simp_all [parityProgram, parityGrp, parityLit, Lit.eval]

/-- Neither parity group is available on the all-false input. -/
theorem parityTrue_false_false :
    ∀ j : Fin 2, ¬ parityProgram.groupTrue ![false, false] j := by
  intro j
  fin_cases j <;> simp [parityGroupTrue_zero, parityGroupTrue_one]

/-- On input `[true, false]`, exactly parity group zero is available. -/
theorem parityTrue_true_false :
    ∀ j : Fin 2, parityProgram.groupTrue ![true, false] j ↔ j = 0 := by
  intro j
  fin_cases j <;> simp [parityGroupTrue_zero, parityGroupTrue_one]

/-- On input `[false, true]`, exactly parity group one is available. -/
theorem parityTrue_false_true :
    ∀ j : Fin 2, parityProgram.groupTrue ![false, true] j ↔ j = 1 := by
  intro j
  fin_cases j <;> simp [parityGroupTrue_zero, parityGroupTrue_one]

/-- Neither parity group is available on the all-true input. -/
theorem parityTrue_true_true :
    ∀ j : Fin 2, ¬ parityProgram.groupTrue ![true, true] j := by
  intro j
  fin_cases j <;> simp [parityGroupTrue_zero, parityGroupTrue_one]

/-- For nonnegative `B` and `B'`, the negative witness size on the empty available set with
weights `[B, B']` is `B + B'`. -/
theorem parity_wsize_00 (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    parityProgram.WsizeFalseAt ![B, B'] (∅ : Finset (Fin 2)) (B + B') := by
  constructor
  · intro b hb _
    rw [false_value_empty_const ![B, B'] parityProgram (fun _ => rfl) b hb]
    rw [Fin.sum_univ_two]
    simp
  · refine ⟨fun _ => 1, rfl, ?_, ?_⟩
    · intro j hj
      exact absurd hj (by simp)
    · rw [false_value_empty_const ![B, B'] parityProgram (fun _ => rfl) (fun _ => 1) rfl]
      rw [Fin.sum_univ_two]
      simp

/-- With only group zero available and weights `[B + B', B]`, the positive witness size is
exactly `B + B'`. -/
theorem parity_wsize_10 (B B' : ℝ) :
    parityProgram.WsizeTrueAt ![B + B', B] ({0} : Finset (Fin 2)) (B + B') := by
  constructor
  · intro w hsupp hsum
    have h1 : (∑ j ∈ ({0} : Finset (Fin 2)), w j) = 1 :=
      (sum_smul_eq_target_empty ({0} : Finset (Fin 2)) w parityProgram.v (fun _ _ => rfl)).1 hsum
    have hw1 : w 1 = 0 := hsupp 1 (by simp)
    have hw0 : w 0 = 1 := by simpa using h1
    have hval : wt ![B + B', B] w = B + B' := by
      rw [wt, Fin.sum_univ_two]
      simp [hw0, hw1]
    rw [hval]
  · refine ⟨![1, 0], ?_, ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all
    · apply (sum_smul_eq_target_empty ({0} : Finset (Fin 2)) _ parityProgram.v (fun _ _ => rfl)).2
      simp
    · rw [wt, Fin.sum_univ_two]
      simp

/-- With only group one available and weights `[B, B + B']`, the positive witness size is
exactly `B + B'`. -/
theorem parity_wsize_01 (B B' : ℝ) :
    parityProgram.WsizeTrueAt ![B, B + B'] ({1} : Finset (Fin 2)) (B + B') := by
  constructor
  · intro w hsupp hsum
    have h1 : (∑ j ∈ ({1} : Finset (Fin 2)), w j) = 1 :=
      (sum_smul_eq_target_empty ({1} : Finset (Fin 2)) w parityProgram.v (fun _ _ => rfl)).1 hsum
    have hw0 : w 0 = 0 := hsupp 0 (by simp)
    have hw1 : w 1 = 1 := by simpa using h1
    have hval : wt ![B, B + B'] w = B + B' := by
      rw [wt, Fin.sum_univ_two]
      simp [hw0, hw1]
    rw [hval]
  · refine ⟨![0, 1], ?_, ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all
    · apply (sum_smul_eq_target_empty ({1} : Finset (Fin 2)) _ parityProgram.v (fun _ _ => rfl)).2
      simp
    · rw [wt, Fin.sum_univ_two]
      simp

/-- For nonnegative `B` and `B'`, the negative witness size on the empty available set with
weights `[B', B]` is `B + B'`. -/
theorem parity_wsize_11 (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    parityProgram.WsizeFalseAt ![B', B] (∅ : Finset (Fin 2)) (B + B') := by
  constructor
  · intro b hb _
    rw [false_value_empty_const ![B', B] parityProgram (fun _ => rfl) b hb]
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    linarith
  · refine ⟨fun _ => 1, rfl, ?_, ?_⟩
    · intro j hj
      exact absurd hj (by simp)
    · rw [false_value_empty_const ![B', B] parityProgram (fun _ => rfl) (fun _ => 1) rfl]
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      linarith

/-- Collect the exact positive and negative parity witness sizes `B + B'` for the four specified
weight and availability patterns. See [ReichardtSpalek2008]. -/
theorem parity_witness_size (B B' : ℝ) (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    parityProgram.WsizeTrueAt ![B + B', B] ({0} : Finset (Fin 2)) (B + B') ∧
    parityProgram.WsizeTrueAt ![B, B + B'] ({1} : Finset (Fin 2)) (B + B') ∧
    parityProgram.WsizeFalseAt ![B, B'] (∅ : Finset (Fin 2)) (B + B') ∧
    parityProgram.WsizeFalseAt ![B', B] (∅ : Finset (Fin 2)) (B + B') :=
  ⟨parity_wsize_10 B B', parity_wsize_01 B B', parity_wsize_00 B B' hB hB',
    parity_wsize_11 B B' hB hB'⟩

/-- The fourth root of `B² + B'²`, expressed as two successive square roots. -/
def orNorm (B B' : ℝ) : ℝ := Real.sqrt (Real.sqrt (B ^ 2 + B' ^ 2))

/-- The two scalar OR columns, with values `sqrt B / orNorm B B'` and `sqrt B' / orNorm B B'`. -/
def orCol (B B' : ℝ) : Fin 2 → Option Empty → ℂ :=
  fun j _ => if j = 0 then ((Real.sqrt B / orNorm B B' : ℝ) : ℂ)
    else ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ)

/-- The two-input OR span program with positive literals and scalar columns `orCol B B'`. -/
def orProgram (B B' : ℝ) : SpanProgram 2 (Fin 2) Empty (Fin 2) where
  grp := ![0, 1]
  lit := ![Lit.pos 0, Lit.pos 1]
  v := orCol B B'

/-- The target coordinate of OR column zero is `sqrt B / orNorm B B'`. -/
theorem orProgram_v_zero (B B' : ℝ) :
    (orProgram B B').v 0 none = ((Real.sqrt B / orNorm B B' : ℝ) : ℂ) := by
  simp [orProgram, orCol]

/-- The target coordinate of OR column one is `sqrt B' / orNorm B B'`. -/
theorem orProgram_v_one (B B' : ℝ) :
    (orProgram B B').v 1 none = ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ) := by
  simp [orProgram, orCol]

/-- Pairing with OR column zero multiplies `b none` by the conjugate of `sqrt B / orNorm B B'`. -/
theorem orProgram_pair_zero (B B' : ℝ) (b : Option Empty → ℂ) :
    (orProgram B B').pair b 0
      = (starRingEnd ℂ) ((Real.sqrt B / orNorm B B' : ℝ) : ℂ) * b none := by
  change (∑ k : Option Empty, (starRingEnd ℂ) ((orProgram B B').v 0 k) * b k) = _
  rw [Finset.sum_eq_single none]
  · rw [orProgram_v_zero]
  · intro k _ hk
    cases k with
    | none => exact absurd rfl hk
    | some e => exact e.elim
  · intro h
    exact absurd (Finset.mem_univ none) h

/-- Pairing with OR column one multiplies `b none` by the conjugate of `sqrt B' / orNorm B B'`. -/
theorem orProgram_pair_one (B B' : ℝ) (b : Option Empty → ℂ) :
    (orProgram B B').pair b 1
      = (starRingEnd ℂ) ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ) * b none := by
  change (∑ k : Option Empty, (starRingEnd ℂ) ((orProgram B B').v 1 k) * b k) = _
  rw [Finset.sum_eq_single none]
  · rw [orProgram_v_one]
  · intro k _ hk
    cases k with
    | none => exact absurd rfl hk
    | some e => exact e.elim
  · intro h
    exact absurd (Finset.mem_univ none) h

/-- OR group zero is available exactly when input zero is true. -/
theorem orGroupTrue_zero (B B' : ℝ) (x : Fin 2 → Bool) :
    (orProgram B B').groupTrue x 0 ↔ x 0 = true := by
  constructor
  · intro h
    have := h 0 (by simp [orProgram])
    simpa [orProgram, Lit.eval] using this
  · intro h i hi
    fin_cases i <;> simp_all [orProgram, Lit.eval]

/-- OR group one is available exactly when input one is true. -/
theorem orGroupTrue_one (B B' : ℝ) (x : Fin 2 → Bool) :
    (orProgram B B').groupTrue x 1 ↔ x 1 = true := by
  constructor
  · intro h
    have := h 1 (by simp [orProgram])
    simpa [orProgram, Lit.eval] using this
  · intro h i hi
    fin_cases i <;> simp_all [orProgram, Lit.eval]

/-- For positive weights, the weighted sum of the squared normalized OR columns is `sqrt (B² +
B'²)`. -/
theorem orCol_weighted (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    B * (Real.sqrt B / orNorm B B') ^ 2 + B' * (Real.sqrt B' / orNorm B B') ^ 2
      = Real.sqrt (B ^ 2 + B' ^ 2) := by
  have hn : orNorm B B' ^ 2 = Real.sqrt (B ^ 2 + B' ^ 2) := by
    rw [orNorm, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hnpos : orNorm B B' ≠ 0 := by
    rw [orNorm]
    exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have hsB' : Real.sqrt B' ^ 2 = B' := Real.sq_sqrt hB'.le
  have hDpos : 0 < Real.sqrt (B ^ 2 + B' ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [div_pow, div_pow, hsB, hsB', hn]
  field_simp [hDpos.ne']
  rw [Real.sq_sqrt (by positivity)]

/-- For positive weights, `B * (orNorm B B' / sqrt B)²` equals `sqrt (B² + B'²)`. -/
theorem mul_orNorm_div_sq (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    B * (orNorm B B' / Real.sqrt B) ^ 2 = Real.sqrt (B ^ 2 + B' ^ 2) := by
  have hn : orNorm B B' ^ 2 = Real.sqrt (B ^ 2 + B' ^ 2) := by
    rw [orNorm, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  rw [div_pow, hn, hsB]
  field_simp

/-- For positive weights, `B' * (orNorm B B' / sqrt B')²` equals `sqrt (B² + B'²)`. -/
theorem mul_orNorm_div_sq' (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    B' * (orNorm B B' / Real.sqrt B') ^ 2 = Real.sqrt (B ^ 2 + B' ^ 2) := by
  have h := mul_orNorm_div_sq B' B hB' hB
  have hnorm : orNorm B' B = orNorm B B' := by
    unfold orNorm
    rw [show B' ^ 2 + B ^ 2 = B ^ 2 + B' ^ 2 by ring]
  rw [show B' ^ 2 + B ^ 2 = B ^ 2 + B' ^ 2 by ring] at h
  rwa [hnorm] at h

/-- For positive weights, the exact negative OR witness size on the empty available set is `sqrt
(B² + B'²)`. -/
theorem or_wsize_00 (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    (orProgram B B').WsizeFalseAt ![B, B'] (∅ : Finset (Fin 2))
      (Real.sqrt (B ^ 2 + B' ^ 2)) := by
  have hvalue : ∀ b : Option Empty → ℂ, b none = 1 →
      (∑ j, ![B, B'] j * ‖(orProgram B B').pair b j‖ ^ 2)
        = Real.sqrt (B ^ 2 + B' ^ 2) := by
    intro b hb
    rw [Fin.sum_univ_two, orProgram_pair_zero, orProgram_pair_one, hb]
    simp only [mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      norm_conj_real_sq]
    exact orCol_weighted B B' hB hB'
  constructor
  · intro b hb _
    rw [hvalue b hb]
  · exact ⟨fun _ => 1, rfl, (by intro j hj; exact absurd hj (by simp)), hvalue _ rfl⟩

/-- For positive weights, the exact positive OR witness size with only column zero available is
`sqrt (B² + B'²)`. -/
theorem or_wsize_10 (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    (orProgram B B').WsizeTrueAt ![B, B'] ({0} : Finset (Fin 2))
      (Real.sqrt (B ^ 2 + B' ^ 2)) := by
  have hBne : Real.sqrt B ≠ 0 := (Real.sqrt_pos.2 hB).ne'
  have hnne : orNorm B B' ≠ 0 := by
    rw [orNorm]
    exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  constructor
  · intro w hsupp hsum
    have hw1 : w 1 = 0 := hsupp 1 (by simp)
    have hc : w 0 * ((Real.sqrt B / orNorm B B' : ℝ) : ℂ) = 1 := by
      have hn := congr_fun hsum none
      simp only [target_none, Finset.sum_apply, Finset.sum_singleton, Pi.smul_apply,
        smul_eq_mul] at hn
      rw [orProgram_v_zero] at hn
      exact hn
    have hcne : ((Real.sqrt B / orNorm B B' : ℝ) : ℂ) ≠ 0 := by
      have : (Real.sqrt B / orNorm B B' : ℝ) ≠ 0 := div_ne_zero hBne hnne
      exact_mod_cast this
    have hw0 : w 0 = ((orNorm B B' / Real.sqrt B : ℝ) : ℂ) := by
      have h1 : w 0 = (((Real.sqrt B / orNorm B B' : ℝ) : ℂ))⁻¹ := by
        have h2 : w 0 * ((Real.sqrt B / orNorm B B' : ℝ) : ℂ)
            = (((Real.sqrt B / orNorm B B' : ℝ) : ℂ))⁻¹
              * ((Real.sqrt B / orNorm B B' : ℝ) : ℂ) := by
          rw [hc, inv_mul_cancel₀ hcne]
        exact mul_right_cancel₀ hcne h2
      rw [h1, ← Complex.ofReal_inv]
      congr 1
      field_simp [hBne, hnne]
    have hval : wt ![B, B'] w = Real.sqrt (B ^ 2 + B' ^ 2) := by
      rw [wt, Fin.sum_univ_two, hw0, hw1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [norm_real_sq, mul_orNorm_div_sq B B' hB hB']
      simp
    rw [hval]
  · refine ⟨![((orNorm B B' / Real.sqrt B : ℝ) : ℂ), 0], ?_, ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all
    · funext k
      cases k with
      | none =>
          simp only [target_none, Finset.sum_apply, Finset.sum_singleton, Pi.smul_apply,
            smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [orProgram_v_zero]
          rw [← Complex.ofReal_mul]
          congr 1
          field_simp [hBne, hnne]
      | some e => exact e.elim
    · rw [wt, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [norm_real_sq, mul_orNorm_div_sq B B' hB hB']
      simp

/-- For positive weights, the exact positive OR witness size with only column one available is
`sqrt (B² + B'²)`. -/
theorem or_wsize_01 (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    (orProgram B B').WsizeTrueAt ![B, B'] ({1} : Finset (Fin 2))
      (Real.sqrt (B ^ 2 + B' ^ 2)) := by
  have hB'ne : Real.sqrt B' ≠ 0 := (Real.sqrt_pos.2 hB').ne'
  have hnne : orNorm B B' ≠ 0 := by
    rw [orNorm]
    exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  constructor
  · intro w hsupp hsum
    have hw0 : w 0 = 0 := hsupp 0 (by simp)
    have hc : w 1 * ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ) = 1 := by
      have hn := congr_fun hsum none
      simp only [target_none, Finset.sum_apply, Finset.sum_singleton, Pi.smul_apply,
        smul_eq_mul] at hn
      rw [orProgram_v_one] at hn
      exact hn
    have hcne : ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ) ≠ 0 := by
      have : (Real.sqrt B' / orNorm B B' : ℝ) ≠ 0 := div_ne_zero hB'ne hnne
      exact_mod_cast this
    have hw1 : w 1 = ((orNorm B B' / Real.sqrt B' : ℝ) : ℂ) := by
      have h1 : w 1 = (((Real.sqrt B' / orNorm B B' : ℝ) : ℂ))⁻¹ := by
        have h2 : w 1 * ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ)
            = (((Real.sqrt B' / orNorm B B' : ℝ) : ℂ))⁻¹
              * ((Real.sqrt B' / orNorm B B' : ℝ) : ℂ) := by
          rw [hc, inv_mul_cancel₀ hcne]
        exact mul_right_cancel₀ hcne h2
      rw [h1, ← Complex.ofReal_inv]
      congr 1
      field_simp [hB'ne, hnne]
    have hval : wt ![B, B'] w = Real.sqrt (B ^ 2 + B' ^ 2) := by
      rw [wt, Fin.sum_univ_two, hw0, hw1]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [norm_real_sq, mul_orNorm_div_sq' B B' hB hB']
      simp
    rw [hval]
  · refine ⟨![0, ((orNorm B B' / Real.sqrt B' : ℝ) : ℂ)], ?_, ?_, ?_⟩
    · intro j hj
      fin_cases j <;> simp_all
    · funext k
      cases k with
      | none =>
          simp only [target_none, Finset.sum_apply, Finset.sum_singleton, Pi.smul_apply,
            smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
          rw [orProgram_v_one]
          rw [← Complex.ofReal_mul]
          congr 1
          field_simp [hB'ne, hnne]
      | some e => exact e.elim
    · rw [wt, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [norm_real_sq, mul_orNorm_div_sq' B B' hB hB']
      simp

/-- For positive weights, there is a linear combination of both OR columns equal to the target
with weighted cost at most `sqrt (B² + B'²)`. -/
theorem or_wsize_11_le (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    ∃ w : Fin 2 → ℂ, (∑ j, w j • (orProgram B B').v j = target Empty) ∧
      wt ![B, B'] w ≤ Real.sqrt (B ^ 2 + B' ^ 2) := by
  have hBne : Real.sqrt B ≠ 0 := (Real.sqrt_pos.2 hB).ne'
  have hnne : orNorm B B' ≠ 0 := by
    rw [orNorm]
    exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 (by positivity))).ne'
  refine ⟨![((orNorm B B' / Real.sqrt B : ℝ) : ℂ), 0], ?_, ?_⟩
  · funext k
    cases k with
    | none =>
        simp only [target_none, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [orProgram_v_zero, orProgram_v_one]
        rw [zero_mul, add_zero, ← Complex.ofReal_mul]
        congr 1
        field_simp [hBne, hnne]
    | some e => exact e.elim
  · rw [wt, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [norm_real_sq, mul_orNorm_div_sq B B' hB hB']
    simp

/-- Collect the exact OR witness sizes on the empty and singleton available sets and a
positive-witness upper bound of `sqrt (B² + B'²)` when both columns are available. See
[ReichardtSpalek2008]. -/
theorem or_witness_size (B B' : ℝ) (hB : 0 < B) (hB' : 0 < B') :
    (orProgram B B').WsizeFalseAt ![B, B'] (∅ : Finset (Fin 2)) (Real.sqrt (B ^ 2 + B' ^ 2)) ∧
    (orProgram B B').WsizeTrueAt ![B, B'] ({0} : Finset (Fin 2))
      (Real.sqrt (B ^ 2 + B' ^ 2)) ∧
    (orProgram B B').WsizeTrueAt ![B, B'] ({1} : Finset (Fin 2))
      (Real.sqrt (B ^ 2 + B' ^ 2)) ∧
    (∃ w : Fin 2 → ℂ, (∑ j, w j • (orProgram B B').v j = target Empty) ∧
      wt ![B, B'] w ≤ Real.sqrt (B ^ 2 + B' ^ 2)) :=
  ⟨or_wsize_00 B B' hB hB', or_wsize_10 B B' hB hB', or_wsize_01 B B' hB hB',
    or_wsize_11_le B B' hB hB'⟩

end Qatlib.Papers.SpanProgram07.MainResults
