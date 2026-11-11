/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.QubitMeasure.Data.TrineCopies

/-!
# Collective Geometry

Collective Risk constructions for Copy Decision.
Defines `collectiveA`, `collectiveB`, `collectiveOrtho`.
Proves `collective_coefficients`, `equigram_inner_sum`, `equigram_sum_inner`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
open Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Definition of collective A in the Collective Risk construction. -/
def collectiveA (s : ℝ) : ℝ := (Real.sqrt (1-s))⁻¹
/-- Definition of collective B in the Collective Risk construction. -/
def collectiveB (s : ℝ) : ℝ := ((Real.sqrt (1+2*s))⁻¹-collectiveA s)/3

/-- The stated copy-decision construction satisfies `collective_coefficients` with the complete displayed premises. -/
lemma collective_coefficients (s : ℝ) (hm : 0 < 1-s) (hp : 0 < 1+2*s) :
    (collectiveA s)^2*(1-s)=1 ∧
    (collectiveA s)^2*s+(2*collectiveA s*collectiveB s+3*(collectiveB s)^2)*(1+2*s)=0 := by
  have hu := Real.sq_sqrt (le_of_lt hm)
  have hv := Real.sq_sqrt (le_of_lt hp)
  have hune : Real.sqrt (1-s) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hvne : Real.sqrt (1+2*s) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hA : (collectiveA s)^2*(1-s)=1 := by
    unfold collectiveA
    calc
      _ = ((Real.sqrt (1-s))⁻¹)^2*(Real.sqrt (1-s))^2 := by rw [hu]
      _ = 1 := by field_simp
  have hB : (collectiveA s+3*collectiveB s)^2*(1+2*s)=1 := by
    unfold collectiveB
    have he : collectiveA s+3*(((Real.sqrt (1+2*s))⁻¹-collectiveA s)/3)=
        (Real.sqrt (1+2*s))⁻¹ := by ring
    rw [he]
    calc
      _ = ((Real.sqrt (1+2*s))⁻¹)^2*(Real.sqrt (1+2*s))^2 := by rw [hv]
      _ = 1 := by field_simp
  exact ⟨hA, by nlinarith only [hA, hB]⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Definition of collective Ortho in the Collective Risk construction. -/
def collectiveOrtho (ψ : Fin 3 → H) (s : ℝ) (i : Fin 3) : H :=
  (collectiveA s:ℂ) • ψ i+(collectiveB s:ℂ) • ∑ k, ψ k

/-- The stated copy-decision construction satisfies `equigram_inner_sum` with the complete displayed premises. -/
lemma equigram_inner_sum (ψ : Fin 3 → H) (s : ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j)=((if i=j then 1 else s:ℝ):ℂ)) (i : Fin 3) :
    inner ℂ (ψ i) (∑ k, ψ k)=((1+2*s:ℝ):ℂ) := by
  rw [inner_sum]
  simp_rw [hG]
  fin_cases i <;> norm_num [Fin.sum_univ_three, Fin.ext_iff] <;> ring

/-- The stated copy-decision construction satisfies `equigram_sum_inner` with the complete displayed premises. -/
lemma equigram_sum_inner (ψ : Fin 3 → H) (s : ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j)=((if i=j then 1 else s:ℝ):ℂ)) (i : Fin 3) :
    inner ℂ (∑ k, ψ k) (ψ i)=((1+2*s:ℝ):ℂ) := by
  rw [← inner_conj_symm, equigram_inner_sum ψ s hG]
  exact Complex.conj_ofReal _

/-- The stated copy-decision construction satisfies `equigram_sum_sum` with the complete displayed premises. -/
lemma equigram_sum_sum (ψ : Fin 3 → H) (s : ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j)=((if i=j then 1 else s:ℝ):ℂ)) :
    inner ℂ (∑ k, ψ k) (∑ k, ψ k)=((3*(1+2*s):ℝ):ℂ) := by
  rw [inner_sum]
  simp_rw [equigram_sum_inner ψ s hG]
  simp
  ring

/-- Orthonormal vectors inside the SAME full source Hilbert space. -/
theorem collectiveOrtho_gram (ψ : Fin 3 → H) (s : ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j)=((if i=j then 1 else s:ℝ):ℂ))
    (hm : 0 < 1-s) (hp : 0 < 1+2*s) (i j : Fin 3) :
    inner ℂ (collectiveOrtho ψ s i) (collectiveOrtho ψ s j)=if i=j then 1 else 0 := by
  have hc := collective_coefficients s hm hp
  have he : inner ℂ (collectiveOrtho ψ s i) (collectiveOrtho ψ s j)=
      (((collectiveA s)^2*(if i=j then 1 else s)+
        (2*collectiveA s*collectiveB s+3*(collectiveB s)^2)*(1+2*s):ℝ):ℂ) := by
    simp only [collectiveOrtho, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      hG, equigram_inner_sum ψ s hG, equigram_sum_inner ψ s hG, equigram_sum_sum ψ s hG]
    push_cast
    ring
  rw [he]
  by_cases h : i=j
  · rw [if_pos h, if_pos h]
    have hr : (collectiveA s)^2*1+
        (2*collectiveA s*collectiveB s+3*(collectiveB s)^2)*(1+2*s)=1 := by
      nlinarith only [hc.1, hc.2]
    exact_mod_cast hr
  · rw [if_neg h, if_neg h]
    exact_mod_cast hc.2

/-- Definition of collective Alpha in the Collective Risk construction. -/
def collectiveAlpha (s : ℝ) : ℝ := (Real.sqrt (1+2*s)+2*Real.sqrt (1-s))/3
/-- Definition of collective Beta in the Collective Risk construction. -/
def collectiveBeta (s : ℝ) : ℝ := (Real.sqrt (1+2*s)-Real.sqrt (1-s))/3

/-- The stated copy-decision construction satisfies `collectiveOrtho_overlap` with the complete displayed premises. -/
lemma collectiveOrtho_overlap (ψ : Fin 3 → H) (s : ℝ)
    (hG : ∀ i j, inner ℂ (ψ i) (ψ j)=((if i=j then 1 else s:ℝ):ℂ))
    (hm : 0 < 1-s) (hp : 0 < 1+2*s) (i j : Fin 3) :
    inner ℂ (collectiveOrtho ψ s i) (ψ j)=
      ((if i=j then collectiveAlpha s else collectiveBeta s:ℝ):ℂ) := by
  simp only [collectiveOrtho, inner_add_left, inner_smul_left, Complex.conj_ofReal,
    hG, equigram_sum_inner ψ s hG]
  have hu := Real.sq_sqrt (le_of_lt hm)
  have hv := Real.sq_sqrt (le_of_lt hp)
  have hune : Real.sqrt (1-s) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
  have hvne : Real.sqrt (1+2*s) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hu' : collectiveA s*(1-s)=Real.sqrt (1-s) := by
    unfold collectiveA
    calc
      _ = (Real.sqrt (1-s))⁻¹*(Real.sqrt (1-s))^2 := by rw [hu]
      _ = _ := by field_simp
  have hv' : (Real.sqrt (1+2*s))⁻¹*(1+2*s)=Real.sqrt (1+2*s) := by
    calc
      _ = (Real.sqrt (1+2*s))⁻¹*(Real.sqrt (1+2*s))^2 := by rw [hv]
      _ = _ := by field_simp
  have hb : collectiveB s*(1+2*s)=
      (Real.sqrt (1+2*s)-collectiveA s*(1+2*s))/3 := by
    calc
      _ = ((Real.sqrt (1+2*s))⁻¹*(1+2*s)-collectiveA s*(1+2*s))/3 := by
        unfold collectiveB
        ring
      _ = _ := by rw [hv']
  have hreal : collectiveA s*(if i=j then 1 else s)+collectiveB s*(1+2*s)=
      if i=j then collectiveAlpha s else collectiveBeta s := by
    rw [hb]
    unfold collectiveAlpha collectiveBeta
    split_ifs <;> nlinarith only [hu']
  exact_mod_cast hreal

/-- The stated copy-decision construction satisfies `collectiveAlphaBeta` with the complete displayed premises. -/
lemma collectiveAlphaBeta (s : ℝ) (hm : 0 < 1-s) (hp : 0 < 1+2*s) :
    (collectiveAlpha s)^2+2*(collectiveBeta s)^2=1 := by
  have hu := Real.sq_sqrt (le_of_lt hm)
  have hv := Real.sq_sqrt (le_of_lt hp)
  unfold collectiveAlpha collectiveBeta
  nlinarith only [hu, hv]

end Qatlib.Concepts.CopyDecision.CollectiveRisk.Data
