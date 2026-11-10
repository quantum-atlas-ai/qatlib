/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelianState
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Normed.Ring.Finite

open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalshMoment.Forrelation
open scoped ComplexConjugate BigOperators Classical

namespace Qatlib.Papers.HiddenTransl02.MainResults.FourierSamplingPair

set_option autoImplicit false

variable {G : Type*} [AddCommGroup G] [Fintype G]

def signOfBit (c : Bool) : ℂ := if c then -1 else 1

noncomputable def pairAmplitude (e : G ≃ AddChar G ℂ) (u : G) (y : G) (c : Bool)
    (x : G) : ℂ :=
  (2 * (Fintype.card G : ℂ))⁻¹ *
    ((e y) x * (1 + signOfBit c * (e y) u))

noncomputable def pairProb (e : G ≃ AddChar G ℂ) (u : G) (y : G) (c : Bool) : ℝ :=
  ∑ x : G, ‖pairAmplitude e u y c x‖ ^ 2

def memOrthogonal (e : G ≃ AddChar G ℂ) (u y : G) : Prop := (e y) u = 1

lemma norm_pairAmplitude (e : G ≃ AddChar G ℂ) (u y : G) (c : Bool) (x : G) :
    ‖pairAmplitude e u y c x‖ =
      ‖(2 * (Fintype.card G : ℂ))⁻¹‖ * ‖1 + signOfBit c * (e y) u‖ := by
  rw [pairAmplitude, norm_mul, norm_mul, AddChar.norm_apply, one_mul]

lemma norm_inv_two_card :
    ‖(2 * (Fintype.card G : ℂ))⁻¹‖ = (2 * (Fintype.card G : ℝ))⁻¹ := by
  rw [norm_inv, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hc : ‖(Fintype.card G : ℂ)‖ = (Fintype.card G : ℝ) := by
    rw [norm_natCast]
  rw [h2, hc]

theorem pairProb_eq (e : G ≃ AddChar G ℂ) (u y : G) (c : Bool) :
    pairProb e u y c =
      (4 * (Fintype.card G : ℝ))⁻¹ * ‖1 + signOfBit c * (e y) u‖ ^ 2 := by
  have hC : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold pairProb
  rw [Finset.sum_congr rfl (fun x _ => by rw [norm_pairAmplitude e u y c x])]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, norm_inv_two_card]
  field_simp
  ring

theorem pairProb_one_depends_only_on_character (e : G ≃ AddChar G ℂ) (u y y' : G)
    (h : (e y) u = (e y') u) :
    pairProb e u y true = pairProb e u y' true := by
  simp only [pairProb_eq, signOfBit, if_true, h]

theorem pairProb_one_eq_zero_iff (e : G ≃ AddChar G ℂ) (u y : G) :
    pairProb e u y true = 0 ↔ memOrthogonal e u y := by
  rw [pairProb_eq]
  have hC : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hscalen : (4 * (Fintype.card G : ℝ))⁻¹ ≠ 0 := by
    have : (4 * (Fintype.card G : ℝ)) ≠ 0 := by positivity
    exact inv_ne_zero this
  constructor
  · intro h
    have hp : ‖1 + signOfBit true * (e y) u‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 hscalen
      · exact h2
    have hn : ‖1 + signOfBit true * (e y) u‖ = 0 := sq_eq_zero_iff.mp hp
    unfold memOrthogonal
    have h1 : 1 + signOfBit true * (e y) u = 0 := norm_eq_zero.mp hn
    have h1' : (1 : ℂ) - (e y) u = 0 := by
      have hh := h1
      simp only [signOfBit, if_true] at hh
      linear_combination hh
    exact (sub_eq_zero.mp h1').symm
  · intro h
    unfold memOrthogonal at h
    rw [h]
    simp [signOfBit]

theorem sum_character_eval (e : G ≃ AddChar G ℂ) (u : G) :
    (∑ y : G, (e y) u) = if u = 0 then (Fintype.card G : ℂ) else 0 := by
  have h1 : (∑ y : G, (e y) u) = ∑ y : G, ((e y) u * conj ((e y) 0)) := by
    refine Finset.sum_congr rfl ?_
    intro y _
    simp
  rw [h1, Equiv.sum_comp e (fun χ : AddChar G ℂ => χ u * conj (χ 0)),
    sum_dual_mul_conj u 0]

theorem fourierSampling_outputs_one_prob (e : G ≃ AddChar G ℂ) (u : G) (hu : u ≠ 0) :
    (∑ y : G, pairProb e u y true) = 1 / 2 := by
  have hC : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexpand : ∀ y : G, ‖1 + signOfBit true * (e y) u‖ ^ 2 =
      2 - 2 * ((e y) u).re := by
    intro y
    have hnorm : ‖(e y) u‖ = 1 := AddChar.norm_apply _ _
    have hsq : ‖1 + signOfBit true * (e y) u‖ ^ 2 =
        Complex.normSq (1 + signOfBit true * (e y) u) := Complex.sq_norm _
    rw [hsq, Complex.normSq_apply]
    have hchi : ((e y) u).re ^ 2 + ((e y) u).im ^ 2 = 1 := by
      have h := Complex.sq_norm ((e y) u)
      rw [Complex.normSq_apply, hnorm] at h
      norm_num at h
      nlinarith [h]
    simp only [signOfBit, if_true, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [hchi]
  have hsumre : (∑ y : G, ((e y) u).re) = 0 := by
    have hc0 : (∑ y : G, (e y) u) = 0 := by
      rw [sum_character_eval e u, if_neg hu]
    have := congrArg (fun z : ℂ => z.re) hc0
    simpa [Complex.re_sum] using this
  simp_rw [pairProb_eq, hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hsumre, mul_zero, sub_zero]
  field_simp
  ring

theorem lemma_3_1 (e : G ≃ AddChar G ℂ) (u : G) (hu : u ≠ 0) :
    (∑ y : G, pairProb e u y true) = 1 / 2 ∧
      (∀ y y', (e y) u = (e y') u → pairProb e u y true = pairProb e u y' true) ∧
      (∀ y, pairProb e u y true = 0 ↔ memOrthogonal e u y) :=
  ⟨fourierSampling_outputs_one_prob e u hu,
    fun y y' h => pairProb_one_depends_only_on_character e u y y' h,
    fun y => pairProb_one_eq_zero_iff e u y⟩

end Qatlib.Papers.HiddenTransl02.MainResults.FourierSamplingPair
