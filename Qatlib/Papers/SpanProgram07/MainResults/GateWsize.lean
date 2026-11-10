/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.Maj3
import Qatlib.Papers.SpanProgram07.MainResults.WitnessSize
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset
open SpanProgram
open scoped BigOperators

namespace maj3Program

variable {w : ℂ} {α : Fin 3 → ℂ}

@[simp] theorem v_none (j : Fin 3) : (maj3Program w α).v j none = w := rfl

@[simp] theorem v_some (j : Fin 3) : (maj3Program w α).v j (some ()) = α j := rfl

theorem pair_eq (b : Option Unit → ℂ) (j : Fin 3) :
    (maj3Program w α).pair b j
      = (starRingEnd ℂ) w * b none + (starRingEnd ℂ) (α j) * b (some ()) := by
  unfold SpanProgram.pair
  rw [Fintype.sum_option]
  simp [maj3Program, mul_comm]

theorem normSq_sub_eq_three (hα1 : ∀ j, Complex.normSq (α j) = 1)
    (hsum : ∑ j, α j = 0) {j k : Fin 3} (hjk : j ≠ k) :
    Complex.normSq (α k - α j) = 3 := by
  classical
  have hcard : ({j, k} : Finset (Fin 3)).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]; exact hjk
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ∉ ({j, k} : Finset (Fin 3)) := by
    by_contra h
    push Not at h
    have hsub : (univ : Finset (Fin 3)) ⊆ ({j, k} : Finset (Fin 3)) := fun x _ => h x
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, hcard] at hc
    omega
  have hins_card : (insert l ({j, k} : Finset (Fin 3))).card = 3 := by
    rw [Finset.card_insert_of_notMem hl, hcard]
  have huniv : insert l ({j, k} : Finset (Fin 3)) = univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [hins_card, Finset.card_univ, Fintype.card_fin])
  have hsum3 : α j + α k + α l = 0 := by
    have h := hsum
    rw [← huniv, Finset.sum_insert hl, Finset.sum_pair hjk] at h
    linear_combination h
  have hneg : α j + α k = -α l := by linear_combination hsum3
  have hu : Complex.normSq (α j + α k) = 1 := by
    rw [hneg, Complex.normSq_neg, hα1 l]
  have hinner : Complex.normSq (α j + α k)
      = 2 + 2 * (α j * (starRingEnd ℂ) (α k)).re := by
    rw [Complex.normSq_add, hα1 j, hα1 k]
    ring
  have hre : (α j * (starRingEnd ℂ) (α k)).re = -(1 / 2) := by
    rw [hinner] at hu
    linarith
  have hconj : (α k * (starRingEnd ℂ) (α j)).re = (α j * (starRingEnd ℂ) (α k)).re := by
    have h := Complex.conj_re (α j * (starRingEnd ℂ) (α k))
    simp only [map_mul, Complex.conj_conj] at h
    rw [← h]
    exact congrArg Complex.re (by ring)
  have hsub : Complex.normSq (α k - α j)
      = 2 - 2 * (α k * (starRingEnd ℂ) (α j)).re := by
    have hsplit : α k - α j = α k + -α j := by ring
    rw [hsplit, Complex.normSq_add, hα1 k, Complex.normSq_neg, hα1 j, map_neg, mul_neg,
      Complex.neg_re]
    ring
  rw [hsub, hconj, hre]
  ring

theorem false_value (hα1 : ∀ j, Complex.normSq (α j) = 1) (hsum : ∑ j, α j = 0)
    (b : Option Unit → ℂ) (hb : b none = 1) :
    ∑ j, ‖(maj3Program w α).pair b j‖ ^ 2
      = 3 * ‖w‖ ^ 2 + 3 * ‖b (some ())‖ ^ 2 := by
  have hterm : ∀ j : Fin 3, ‖(maj3Program w α).pair b j‖ ^ 2
      = ‖w‖ ^ 2 + ‖b (some ())‖ ^ 2
        + 2 * (((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j)).re) := by
    intro j
    rw [pair_eq, hb, ← Complex.normSq_eq_norm_sq]
    rw [show (starRingEnd ℂ) w * 1 + (starRingEnd ℂ) (α j) * b (some ())
        = (starRingEnd ℂ) w + (starRingEnd ℂ) (α j) * b (some ()) by ring]
    simp only [Complex.normSq_add, Complex.normSq_conj, Complex.normSq_mul, hα1 j, one_mul]
    have hre : ((starRingEnd ℂ) w
          * (starRingEnd ℂ) ((starRingEnd ℂ) (α j) * b (some ()))).re
        = ((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j)).re := by
      simp only [map_mul, Complex.conj_conj]
      exact congrArg Complex.re (by ring)
    rw [hre]
    simp only [Complex.normSq_eq_norm_sq]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_add_distrib]
  have hcross : (∑ j : Fin 3,
      2 * (((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j)).re)) = 0 := by
    have h1 : ∑ j : Fin 3, ((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j)) = 0 := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_zero, mul_zero]
    have h2 : (∑ j : Fin 3,
        ((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j))).re
        = ∑ j : Fin 3,
          (((starRingEnd ℂ) w * ((starRingEnd ℂ) (b (some ())) * α j)).re) := by
      rw [← Complex.re_sum]
    rw [← Finset.mul_sum, ← h2, h1, Complex.zero_re, mul_zero]
  rw [hcross, add_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem wsize_true_two (hw : Complex.normSq w = 1 / 3)
    (hα1 : ∀ j, Complex.normSq (α j) = 1) (hsum : ∑ j, α j = 0)
    (hinj : Function.Injective α) {j k : Fin 3} (hjk : j ≠ k) :
    (maj3Program w α).WsizeTrueAt (fun _ => 1) ({j, k} : Finset (Fin 3)) 2 := by
  classical
  have hD : α k - α j ≠ 0 := by
    intro h
    have h' : α k = α j := sub_eq_zero.mp h
    exact hjk (hinj h').symm
  have hαj : α j ≠ 0 := by
    intro h
    have h1 := hα1 j
    rw [h, Complex.normSq_zero] at h1
    norm_num at h1
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hw
    norm_num at hw
  have hDns : Complex.normSq (α k - α j) = 3 := normSq_sub_eq_three hα1 hsum hjk
  have hnormdiv : ∀ z : ℂ, Complex.normSq (z / (w * (α k - α j))) = Complex.normSq z := by
    intro z
    rw [map_div₀, Complex.normSq_mul, hw, hDns]
    norm_num
  have hnormneg : ∀ z : ℂ, Complex.normSq (-(z / (w * (α k - α j))))
      = Complex.normSq z := by
    intro z
    rw [Complex.normSq_neg, hnormdiv z]
  constructor
  · intro a ha hsuma
    have h1 : w * (a j + a k) = 1 := by
      have h := congr_fun hsuma none
      simp only [Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        maj3Program, target] at h
      linear_combination h
    have h2 : a j * α j + a k * α k = 0 := by
      have h := congr_fun hsuma (some ())
      simp only [Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        maj3Program, target] at h
      simpa using h
    have hkeyj : w * a j * (α k - α j) = α k := by
      linear_combination (α k) * h1 - w * h2
    have hkeyk : w * a k * (α j - α k) = α j := by
      linear_combination (α j) * h1 - w * h2
    have haj : a j = α k / (w * (α k - α j)) := by
      rw [eq_div_iff (mul_ne_zero hwne hD)]
      linear_combination hkeyj
    have hak : a k = -(α j / (w * (α k - α j))) := by
      rw [← neg_div, eq_div_iff (mul_ne_zero hwne hD)]
      linear_combination -hkeyk
    have hzero : ∀ t ∈ (univ : Finset (Fin 3)), t ∉ ({j, k} : Finset (Fin 3)) →
        (1 : ℝ) * ‖a t‖ ^ 2 = 0 := by
      intro t _ ht
      rw [ha t ht]
      simp
    have hwt : SpanProgram.wt (fun _ => (1 : ℝ)) a = ‖a j‖ ^ 2 + ‖a k‖ ^ 2 := by
      rw [SpanProgram.wt]
      rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_pair hjk]
      simp
    have hval : ‖a j‖ ^ 2 + ‖a k‖ ^ 2 = 2 := by
      rw [haj, hak, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [hnormdiv, hnormneg, hα1 k, hα1 j]
      norm_num
    rw [hwt, hval]
  · refine ⟨Pi.single j (α k / (w * (α k - α j)))
        + Pi.single k (-(α j / (w * (α k - α j)))), ?_, ?_, ?_⟩
    · intro t ht
      have htj : t ≠ j := fun h => ht (by simp [h])
      have htk : t ≠ k := fun h => ht (by simp [h])
      simp [Pi.single_eq_of_ne htj, Pi.single_eq_of_ne htk]
    · funext c
      cases c with
      | none =>
          simp only [target_none, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, maj3Program, Pi.add_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne (Ne.symm hjk), add_zero, zero_add]
          field_simp
          ring
      | some u =>
          have hu : u = () := Subsingleton.elim u ()
          subst hu
          simp only [target_some, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, maj3Program, Pi.add_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne (Ne.symm hjk), add_zero, zero_add]
          field_simp
          ring
    · have hzero : ∀ t ∈ (univ : Finset (Fin 3)), t ∉ ({j, k} : Finset (Fin 3)) →
          (1 : ℝ) * ‖(Pi.single j (α k / (w * (α k - α j)))
            + Pi.single k (-(α j / (w * (α k - α j)))) : Fin 3 → ℂ) t‖ ^ 2 = 0 := by
        intro t _ ht
        have htj : t ≠ j := fun h => ht (by simp [h])
        have htk : t ≠ k := fun h => ht (by simp [h])
        simp [Pi.single_eq_of_ne htj, Pi.single_eq_of_ne htk]
      rw [SpanProgram.wt]
      rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_pair hjk]
      simp only [one_mul, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk,
        Pi.single_eq_of_ne (Ne.symm hjk), add_zero, zero_add]
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      rw [hnormdiv, hnormneg, hα1 k, hα1 j]
      norm_num

theorem wsize_true_three (hw : Complex.normSq w = 1 / 3) (hsum : ∑ j, α j = 0)
    {S : Finset (Fin 3)} (hS : S.card = 3) :
    (maj3Program w α).WsizeTrueAt (fun _ => 1) S 1 := by
  classical
  have hSuni : S = univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
      rw [hS, Finset.card_univ, Fintype.card_fin])
  subst hSuni
  have hw2 : ‖w‖ ^ 2 = (1 / 3 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]; exact hw
  have hwne : w ≠ 0 := by
    intro h
    rw [h, Complex.normSq_zero] at hw
    norm_num at hw
  constructor
  · intro a _ hsuma
    have h1 : w * ∑ j, a j = 1 := by
      have h := congr_fun hsuma none
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, maj3Program, target] at h
      rw [← Finset.sum_mul] at h
      linear_combination h
    have hns : Complex.normSq (∑ j, a j) = 3 := by
      have := congrArg Complex.normSq h1
      simp only [Complex.normSq_mul, Complex.normSq_one] at this
      rw [hw] at this
      nlinarith
    have hstep : ‖∑ j, a j‖ ^ 2 ≤ (∑ j, ‖a j‖) ^ 2 := by
      have hle := norm_sum_le (univ : Finset (Fin 3)) a
      have h1 : (0 : ℝ) ≤ ‖∑ j, a j‖ := norm_nonneg _
      have h := mul_self_le_mul_self h1 hle
      simpa [pow_two] using h
    have hcs : (∑ j, ‖a j‖) ^ 2 ≤ 3 * ∑ j, ‖a j‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 3))) (f := fun j => ‖a j‖)
      simpa using this
    have hnorm : ‖∑ j, a j‖ ^ 2 = 3 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hns
    have hkey : 3 ≤ 3 * ∑ j, ‖a j‖ ^ 2 := by
      calc 3 = ‖∑ j, a j‖ ^ 2 := hnorm.symm
        _ ≤ (∑ j, ‖a j‖) ^ 2 := hstep
        _ ≤ 3 * ∑ j, ‖a j‖ ^ 2 := hcs
    rw [SpanProgram.wt]
    simp only [one_mul]
    nlinarith
  · refine ⟨fun _ => ((3 : ℂ) * w)⁻¹, ?_, ?_, ?_⟩
    · intro t ht
      exact absurd (Finset.mem_univ t) ht
    · funext c
      cases c with
      | none =>
          simp only [target_none, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, maj3Program]
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring
      | some u =>
          have hu : u = () := Subsingleton.elim u ()
          subst hu
          simp only [target_some, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, maj3Program]
          rw [← Finset.mul_sum, hsum, mul_zero]
    · have hconst : ∀ j : Fin 3, ‖(((3 : ℂ) * w)⁻¹)‖ ^ 2 = (1 / 3 : ℝ) := by
        intro j
        rw [← Complex.normSq_eq_norm_sq, map_inv₀, Complex.normSq_mul, hw]
        norm_num
      rw [SpanProgram.wt]
      simp only [one_mul]
      rw [Finset.sum_congr rfl (fun j _ => hconst j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      norm_num

theorem wsize_false_none (hw : Complex.normSq w = 1 / 3)
    (hα1 : ∀ j, Complex.normSq (α j) = 1) (hsum : ∑ j, α j = 0) :
    (maj3Program w α).WsizeFalseAt (fun _ => 1) (∅ : Finset (Fin 3)) 1 := by
  have hw2 : ‖w‖ ^ 2 = (1 / 3 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]; exact hw
  constructor
  · intro b hb _
    simp only [one_mul]
    rw [false_value hα1 hsum b hb]
    nlinarith [sq_nonneg ‖b (some ())‖]
  · refine ⟨fun k => k.rec 1 (fun _ => 0), rfl, ?_, ?_⟩
    · intro j hj
      exact absurd hj (by simp)
    · simp only [one_mul]
      rw [false_value hα1 hsum (fun k => Option.rec 1 (fun _ => 0) k) rfl]
      simp [hw2]

theorem wsize_false_one (hw : Complex.normSq w = 1 / 3)
    (hα1 : ∀ j, Complex.normSq (α j) = 1) (hsum : ∑ j, α j = 0) (j : Fin 3) :
    (maj3Program w α).WsizeFalseAt (fun _ => 1) ({j} : Finset (Fin 3)) 2 := by
  have hw2 : ‖w‖ ^ 2 = (1 / 3 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq]; exact hw
  have hαjne : α j ≠ 0 := by
    intro h
    have h1 := hα1 j
    rw [h, Complex.normSq_zero] at h1
    norm_num at h1
  have hconjne : (starRingEnd ℂ) (α j) ≠ 0 := by
    intro h
    apply hαjne
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  constructor
  · intro b hb horth
    have hp : (starRingEnd ℂ) w + (starRingEnd ℂ) (α j) * b (some ()) = 0 := by
      have h := horth j (by simp)
      rw [pair_eq, hb] at h
      simpa using h
    have hc : Complex.normSq (b (some ())) = Complex.normSq w := by
      have h1 : (starRingEnd ℂ) w = -((starRingEnd ℂ) (α j) * b (some ())) := by
        linear_combination hp
      have := congrArg Complex.normSq h1
      simp only [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_conj, hα1 j,
        one_mul] at this
      linarith
    simp only [one_mul]
    rw [false_value hα1 hsum b hb, ← Complex.normSq_eq_norm_sq,
      ← Complex.normSq_eq_norm_sq, hc, hw]
    norm_num
  · let b : Option Unit → ℂ := fun k => k.rec 1 fun _ => -((starRingEnd ℂ) w / (starRingEnd ℂ) (α j))
    have hb : b none = 1 := rfl
    have hbc : b (some ()) = -((starRingEnd ℂ) w / (starRingEnd ℂ) (α j)) := rfl
    refine ⟨b, hb, ?_, ?_⟩
    · intro j' hj'
      have hjj : j' = j := by simpa using hj'
      subst hjj
      rw [pair_eq, hb, hbc]
      field_simp
      ring
    · have hc2 : Complex.normSq (b (some ())) = Complex.normSq w := by
        rw [hbc, Complex.normSq_neg, map_div₀, Complex.normSq_conj, Complex.normSq_conj,
          hα1 j]
        field_simp
      simp only [one_mul]
      rw [false_value hα1 hsum b hb, ← Complex.normSq_eq_norm_sq,
        ← Complex.normSq_eq_norm_sq, hc2, hw]
      norm_num

theorem maj3_witness_size (hw : Complex.normSq w = 1 / 3)
    (hα1 : ∀ j, Complex.normSq (α j) = 1) (hsum : ∑ j, α j = 0)
    (hinj : Function.Injective α) :
    (maj3Program w α).WsizeTrueAt (fun _ => 1) ({0, 1} : Finset (Fin 3)) 2 ∧
    (maj3Program w α).WsizeTrueAt (fun _ => 1) (univ : Finset (Fin 3)) 1 ∧
    (maj3Program w α).WsizeFalseAt (fun _ => 1) (∅ : Finset (Fin 3)) 1 ∧
    (maj3Program w α).WsizeFalseAt (fun _ => 1) ({0} : Finset (Fin 3)) 2 :=
  ⟨wsize_true_two hw hα1 hsum hinj (by decide), wsize_true_three hw hsum (by simp),
    wsize_false_none hw hα1 hsum, wsize_false_one hw hα1 hsum 0⟩

end maj3Program

end Qatlib.Papers.SpanProgram07.MainResults
