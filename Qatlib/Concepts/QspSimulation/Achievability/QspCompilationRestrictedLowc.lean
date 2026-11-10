/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel

open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Polynomial

section Helpers

private theorem lcC_comp_real (s : ℝ) (p : Polynomial ℝ) :
    (Polynomial.C s).comp p = Polynomial.C s := by
  simp [Polynomial.comp]

private theorem norm_ofReal' (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  have h : Complex.normSq ((r : ℝ) : ℂ) = r * r := Complex.normSq_ofReal r
  rw [Complex.normSq_eq_norm_sq] at h
  have habs : |r| * |r| = r * r := abs_mul_abs_self r
  have hfac : (‖((r : ℝ) : ℂ)‖ - |r|) * (‖((r : ℝ) : ℂ)‖ + |r|) = 0 := by
    linear_combination h - habs
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · have hnn : 0 ≤ ‖((r : ℝ) : ℂ)‖ := norm_nonneg _
    have hna : 0 ≤ |r| := abs_nonneg r
    linarith

private theorem norm_exp_I (y : ℝ) : ‖Complex.exp (Complex.I * (y : ℂ))‖ = 1 := by
  have hre : (Complex.I * (y : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  have him : (Complex.I * (y : ℂ)).im = y := by
    simp [Complex.mul_im]
  have hsq : Complex.normSq (Complex.exp (Complex.I * (y : ℂ))) = 1 := by
    rw [Complex.normSq_apply, Complex.exp_re, Complex.exp_im, hre, him,
      Real.exp_zero, one_mul, one_mul]
    linear_combination Real.sin_sq_add_cos_sq y
  rw [Complex.normSq_eq_norm_sq] at hsq
  have hfac : (‖Complex.exp (Complex.I * (y : ℂ))‖ - 1)
      * (‖Complex.exp (Complex.I * (y : ℂ))‖ + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h' | h'
  · linarith
  · have hnn : 0 ≤ ‖Complex.exp (Complex.I * (y : ℂ))‖ := norm_nonneg _
    linarith

end Helpers

theorem qspCompilationRestricted : QspCompilationRestricted := by
  intro N h A Qt ε hN hp hodd hper hAeven hQtodd hAdeg hQtdeg hεpos hε16 happrox
  set s : ℝ := 1 / (1 + ε) with hsdef
  have h1pe : (0 : ℝ) < 1 + ε := by linarith
  have hspos : (0 : ℝ) < s := by
    rw [hsdef]; exact div_pos (by norm_num) h1pe
  have hsne : s ≠ 0 := by
    rw [hsdef]; exact div_ne_zero one_ne_zero (ne_of_gt h1pe)
  have hsle : s ≤ 1 := by
    rw [hsdef, div_le_iff₀ h1pe]
    linarith
  have hssub : s - 1 = -(ε / (1 + ε)) := by
    rw [hsdef]; field_simp; ring

  have hA₁even : (Polynomial.C s * A).comp (-X) = Polynomial.C s * A := by
    rw [mul_comp, lcC_comp_real, hAeven]
  have hQt₁odd : (Polynomial.C s * Qt).comp (-X) = -(Polynomial.C s * Qt) := by
    rw [mul_comp, lcC_comp_real, hQtodd, mul_neg]
  have hA₁deg : (Polynomial.C s * A).degree ≤ (N : WithBot ℕ) := by
    rw [Polynomial.degree_C_mul hsne]
    exact hAdeg
  have hQt₁deg : (Polynomial.C s * Qt).degree < (N : WithBot ℕ) := by
    rw [Polynomial.degree_C_mul hsne]
    exact hQtdeg

  have hcond₁ : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (Polynomial.C s * A).eval x * (Polynomial.C s * A).eval x
        + (1 - x * x) * ((Polynomial.C s * Qt).eval x * (Polynomial.C s * Qt).eval x)
        ≤ 1 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
    have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
    have hθmem : 2 * Real.arccos x ∈ Set.Icc 0 (2 * Real.pi) := by
      refine ⟨mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.arccos_nonneg x), ?_⟩
      nlinarith [Real.arccos_le_pi x]
    have hθh := happrox (2 * Real.arccos x) hθmem
    have hθhalf : 2 * Real.arccos x / 2 = Real.arccos x := by
      field_simp
    rw [hθhalf, hc, hsin, show (1 : ℝ) - x ^ 2 = 1 - x * x from by ring] at hθh
    have hAval : realEval A ((x : ℝ) : ℂ) = ((A.eval x : ℝ) : ℂ) := map_eval_ofReal A x
    have hQval : realEval Qt ((x : ℝ) : ℂ) = ((Qt.eval x : ℝ) : ℂ) := map_eval_ofReal Qt x
    have hzre : (realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)).re
        = A.eval x := by
      rw [hAval, hQval, mul_assoc, ← Complex.ofReal_mul, Complex.add_re,
        Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero]
    have hzim : (realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)).im
        = Real.sqrt (1 - x * x) * Qt.eval x := by
      rw [hAval, hQval, mul_assoc, ← Complex.ofReal_mul, Complex.add_im,
        Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add]
    have hne : ‖Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ = 1 := norm_exp_I _
    have hzle : ‖realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)‖
        ≤ 1 + ε := by
      have hsplit : realEval A ((x : ℝ) : ℂ)
          + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)
          = (realEval A ((x : ℝ) : ℂ)
              + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)
              - Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ)))
            + Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ)) := by ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [hne]
      linarith
    have htnn : (0 : ℝ) ≤ 1 - x * x := by nlinarith
    have ht2 : Real.sqrt (1 - x * x) * Real.sqrt (1 - x * x) = 1 - x * x :=
      Real.mul_self_sqrt htnn
    have hsq : (‖realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)‖)
        * ‖realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ)‖
        = A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) := by
      rw [← pow_two, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzre, hzim]
      linear_combination (Qt.eval x * Qt.eval x) * ht2
    have h2 : A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x)
        ≤ (1 + ε) * (1 + ε) := by
      have h3 := mul_self_le_mul_self (norm_nonneg (realEval A ((x : ℝ) : ℂ)
        + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ))) hzle
      rw [hsq] at h3
      exact h3
    have hsev : s * s * ((1 + ε) * (1 + ε)) = 1 := by
      rw [hsdef]; field_simp
    have hgoal : (Polynomial.C s * A).eval x * (Polynomial.C s * A).eval x
        + (1 - x * x) * ((Polynomial.C s * Qt).eval x * (Polynomial.C s * Qt).eval x)
        = s * s * (A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x)) := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    have hsnn : (0 : ℝ) ≤ s * s := by positivity
    have hstep : s * s * (A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x))
        ≤ s * s * ((1 + ε) * (1 + ε)) :=
      mul_le_mul_of_nonneg_left h2 hsnn
    rw [hgoal]
    linarith

  obtain ⟨γ₀, γ₁, psis, hlen, hamp⟩ := achievableSufficiencyCore N
    (Polynomial.C s * A) (Polynomial.C s * Qt) hN hp hA₁even hQt₁odd hA₁deg hQt₁deg hcond₁
  refine ⟨γ₀, γ₁, psis, hlen, ?_⟩
  intro x hx
  obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
  have hc : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
  have hsin : Real.sin (Real.arccos x) = Real.sqrt (1 - x ^ 2) := Real.sin_arccos x
  have hθmem : 2 * Real.arccos x ∈ Set.Icc 0 (2 * Real.pi) := by
    refine ⟨mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.arccos_nonneg x), ?_⟩
    nlinarith [Real.arccos_le_pi x]
  have hθh := happrox (2 * Real.arccos x) hθmem
  have hθhalf : 2 * Real.arccos x / 2 = Real.arccos x := by
    field_simp
  rw [hθhalf, hc, hsin, show (1 : ℝ) - x ^ 2 = 1 - x * x from by ring] at hθh
  set w₀ : ℂ := realEval A ((x : ℝ) : ℂ)
    + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ) with hw₀def
  set e : ℂ := Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ)) with hedef
  have hne : ‖e‖ = 1 := norm_exp_I _
  have hA₁val : realEval (Polynomial.C s * A) ((x : ℝ) : ℂ)
      = ((s : ℝ) : ℂ) * realEval A ((x : ℝ) : ℂ) := by
    simp only [realEval, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C, Complex.ofRealHom_eq_coe]
  have hQt₁val : realEval (Polynomial.C s * Qt) ((x : ℝ) : ℂ)
      = ((s : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ) := by
    simp only [realEval, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul,
      Polynomial.eval_C, Complex.ofRealHom_eq_coe]
  have hscale : ((s : ℝ) : ℂ) * realEval A ((x : ℝ) : ℂ)
      + Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ)
        * (((s : ℝ) : ℂ) * realEval Qt ((x : ℝ) : ℂ))
      = ((s : ℝ) : ℂ) * w₀ := by
    rw [hw₀def, mul_add]
    ring
  have hampeq : lcRepoAmp γ₀ γ₁ psis x = ((s : ℝ) : ℂ) * w₀ := by
    rw [hamp x hx, hA₁val, hQt₁val, hscale]
  have hsplit : ((s : ℝ) : ℂ) * w₀ - e
      = ((s : ℝ) : ℂ) * (w₀ - e) + (((s : ℝ) : ℂ) - 1) * e := by ring
  have hn1 : ‖((s : ℝ) : ℂ) * (w₀ - e)‖ ≤ ε := by
    rw [Complex.norm_mul, norm_ofReal', abs_of_pos hspos]
    refine le_trans (mul_le_mul_of_nonneg_left hθh (le_of_lt hspos)) ?_
    have hse := mul_le_mul_of_nonneg_right hsle (le_of_lt hεpos)
    linarith
  have hgnn : (0 : ℝ) ≤ ε / (1 + ε) := div_nonneg (le_of_lt hεpos) (le_of_lt h1pe)
  have hgg : (1 + ε) * (ε / (1 + ε)) = ε := by field_simp
  have habs1 : |s - 1| ≤ ε := by
    rw [hssub, abs_neg, abs_of_nonneg hgnn]
    nlinarith [hgg, h1pe]
  have hconv : ((s : ℝ) : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
  have hn2 : ‖(((s : ℝ) : ℂ) - 1) * e‖ ≤ ε := by
    rw [Complex.norm_mul, hne, mul_one, hconv, norm_ofReal']
    exact habs1
  have hb2 : ‖((s : ℝ) : ℂ) * w₀ - e‖ ≤ 2 * ε := by
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    linarith
  have hrev : 1 - 2 * ε ≤ ‖((s : ℝ) : ℂ) * w₀‖ := by
    have ht := norm_sub_norm_le e (((s : ℝ) : ℂ) * w₀)
    rw [hne, norm_sub_rev] at ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hampeq, hsplit]
    refine le_trans (norm_add_le _ _) ?_
    linarith
  · rw [hampeq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    have h0 : 0 ≤ 1 - 8 * ε := by linarith
    exact sq_le_sq' (le_trans (neg_nonpos.mpr (norm_nonneg _)) h0)
      (le_trans (by linarith) hrev)
  · rw [hampeq, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
    have hsq18 : (1 - 8 * ε) ^ 2 ≥ 1 - 16 * ε := by
      nlinarith [sq_nonneg (8 * ε)]
    have hnn : 1 - 8 * ε ≤ ‖((s : ℝ) : ℂ) * w₀‖ := by linarith
    have h0 : 0 ≤ 1 - 8 * ε := by linarith
    have hfin := sq_le_sq' (le_trans (neg_nonpos.mpr (norm_nonneg _)) h0) hnn
    linarith

end Qatlib.Concepts.QspSimulation.Achievability
