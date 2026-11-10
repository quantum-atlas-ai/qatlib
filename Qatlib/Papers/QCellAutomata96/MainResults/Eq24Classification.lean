/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCellAutomata96.MainResults.ParityReduction
import Qatlib.Papers.QCellAutomata96.MainResults.PairNormalForm
import Qatlib.Concepts.QcaDynamics.ParityWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
set_option warningAsError false

open Complex Matrix
open scoped Matrix
open Qatlib.Concepts.QcaDynamics.ParityWeights

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section

namespace Qatlib.Papers.QCellAutomata96.MainResults

def redM (A B : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, A; 0, B]

def redP (A B : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![B, 0; A, 0]

def red0 (C D : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![C, D; D, C]

lemma red19m (A B C D : ℂ) :
    redM A B * (redM A B)ᴴ + red0 C D * (red0 C D)ᴴ + redP A B * (redP A B)ᴴ
      = par2 (A * star A + B * star B + C * star C + D * star D)
             (A * star B + B * star A + C * star D + D * star C) := by
  simp only [redM, redP, red0, par2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      star_zero, mul_zero, add_zero, zero_add, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val', Matrix.tail_cons,
      Fin.cons_zero, Fin.cons_succ, Fin.reduceFinMk, Fin.isValue, Fin.succ_zero_eq_one] <;>
    ring_nf

lemma red19z (A B C D : ℂ) :
    red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ =
      !![D * star A + B * star C, D * star B + B * star D;
         C * star A + A * star C, C * star B + A * star D] := by
  simp only [redM, redP, red0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      star_zero, mul_zero, add_zero, zero_add, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val', Matrix.tail_cons,
      Fin.cons_zero, Fin.cons_succ, Fin.reduceFinMk, Fin.isValue, Fin.succ_zero_eq_one] <;>
    ring_nf

lemma red19z_00 (A B C D : ℂ) :
    (red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ) 0 0 = D * star A + B * star C := by
  rw [red19z]
  simp [Matrix.of_apply, Matrix.cons_val_zero]

lemma red19z_10 (A B C D : ℂ) :
    (red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ) 1 0 = C * star A + A * star C := by
  rw [red19z]
  simp [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val']

lemma mul_star_self_real (z : ℂ) : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
  simpa using Complex.mul_conj z

lemma re_mul_star_self (z : ℂ) : (z * star z).re = Complex.normSq z := by
  rw [mul_star_self_real]
  simp

lemma re_mul_star_eq_half (z w : ℂ) :
    (z * star w).re
      = (Complex.normSq (z + w) - Complex.normSq z - Complex.normSq w) / 2 := by
  have h := Complex.normSq_add z w
  have h' : (z * (starRingEnd ℂ) w).re = (z * star w).re := rfl
  rw [h'] at h
  linarith

lemma re_mul_star_comm (z w : ℂ) : (z * star w).re = (w * star z).re := by
  rw [re_mul_star_eq_half, re_mul_star_eq_half, add_comm z w]
  ring

lemma normSq_smul_I_mul (w : ℝ) (A : ℂ) :
    Complex.normSq (((w : ℝ) : ℂ) * Complex.I * A) = w * w * Complex.normSq A := by
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I]
  ring

lemma star_smul_I (w : ℝ) (A : ℂ) :
    star (((w : ℝ) : ℂ) * Complex.I * A) = -(((w : ℝ) : ℂ) * Complex.I * star A) := by
  rw [star_mul, star_mul]
  have hI : star Complex.I = -Complex.I := by simp
  have hw : star ((w : ℝ) : ℂ) = ((w : ℝ) : ℂ) := by simp
  rw [hI, hw]
  ring

lemma mul_star_smul_I (w : ℝ) (A B : ℂ) :
    (((w : ℝ) : ℂ) * Complex.I * A) * star (((w : ℝ) : ℂ) * Complex.I * B)
      = ((w : ℝ) : ℂ) ^ 2 * (A * star B) := by
  rw [star_smul_I]
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  calc (((w : ℝ) : ℂ) * Complex.I * A) * -(((w : ℝ) : ℂ) * Complex.I * star B)
      = -(((w : ℝ) : ℂ) * ((w : ℝ) : ℂ)) * (Complex.I * Complex.I) * (A * star B) := by ring
    _ = ((w : ℝ) : ℂ) ^ 2 * (A * star B) := by rw [hI]; ring

lemma re_mul_star_eq_zero {C A : ℂ} (h : C * star A + A * star C = 0) :
    (C * star A).re = 0 := by
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.zero_re] at hre
  have hsym : (A * star C).re = (C * star A).re := re_mul_star_comm A C
  rw [hsym] at hre
  linarith

lemma exists_smul_I {C A : ℂ} (hA : A ≠ 0) (h : (C * star A).re = 0) :
    ∃ w : ℝ, C = ((w : ℝ) : ℂ) * Complex.I * A := by
  have hns : Complex.normSq A ≠ 0 := by
    intro hz
    exact hA (Complex.normSq_eq_zero.mp hz)
  refine ⟨(C * star A).im / Complex.normSq A, ?_⟩
  have hzero : C * star A = (((C * star A).im : ℝ) : ℂ) * Complex.I := by
    have hz : C * star A
        = (((C * star A).re : ℝ) : ℂ) + (((C * star A).im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im (C * star A)).symm
    rw [hz, h]
    simp
  have hnorm : (star A) * A = ((Complex.normSq A : ℝ) : ℂ) := by
    simpa using (Complex.normSq_eq_conj_mul_self (z := A)).symm
  have key : C * ((Complex.normSq A : ℝ) : ℂ)
      = (((C * star A).im : ℝ) : ℂ) * Complex.I * A := by
    calc C * ((Complex.normSq A : ℝ) : ℂ)
        = C * ((star A) * A) := by rw [hnorm]
      _ = (C * star A) * A := by rw [mul_assoc]
      _ = (((C * star A).im : ℝ) : ℂ) * Complex.I * A := by
        conv_lhs => rw [hzero]
  have hden : ((Complex.normSq A : ℝ) : ℂ) ≠ 0 := by
    simpa using hns
  refine mul_right_cancel₀ hden ?_
  rw [key]
  push_cast
  field_simp

lemma eq_smul_I_of_add {C D B A : ℂ} (hA : A ≠ 0) {w : ℝ}
    (hC : C = ((w : ℝ) : ℂ) * Complex.I * A) (h : D * star A + B * star C = 0) :
    D = ((w : ℝ) : ℂ) * Complex.I * B := by
  have hstarC : star C = -(((w : ℝ) : ℂ) * Complex.I * star A) := by
    rw [hC]
    exact star_smul_I w A
  rw [hstarC] at h
  have hzero : (D - ((w : ℝ) : ℂ) * Complex.I * B) * star A = 0 := by
    linear_combination h
  have hstarA : star A ≠ 0 := by
    intro hz
    apply hA
    have := congrArg star hz
    simpa using this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hstarA)

lemma I_mul_mul_I (a x : ℂ) : Complex.I * (a * (Complex.I * x)) = -(a * x) := by
  calc Complex.I * (a * (Complex.I * x)) = (Complex.I * Complex.I) * (a * x) := by ring
    _ = -(a * x) := by rw [Complex.I_mul_I]; ring

lemma smul_I_mul_mul_I (c a x : ℂ) :
    c * Complex.I * (a * (Complex.I * x)) = -(c * (a * x)) := by
  calc c * Complex.I * (a * (Complex.I * x)) = (Complex.I * Complex.I) * (c * a * x) := by ring
    _ = -(c * (a * x)) := by rw [Complex.I_mul_I]; ring

theorem pair_normal_form {x y : ℂ}
    (h1 : x * star x + y * star y = 1) (h2 : x * star y + y * star x = 0) :
    ∃ ψ φ : ℝ, x = Complex.exp ((ψ : ℂ) * Complex.I) * (Complex.I * (Real.sin φ : ℂ)) ∧
      y = Complex.exp ((ψ : ℂ) * Complex.I) * (Real.cos φ : ℂ) := by
  have hlp : (x + y) * star (x + y) = 1 := by
    calc (x + y) * star (x + y) = (x * star x + y * star y) + (x * star y + y * star x) := by
          rw [star_add]; ring
      _ = 1 := by rw [h1, h2]; ring
  have hlm : (x - y) * star (x - y) = 1 := by
    calc (x - y) * star (x - y) = (x * star x + y * star y) - (x * star y + y * star x) := by
          rw [star_sub]; ring
      _ = 1 := by rw [h1, h2]; ring
  set A : ℝ := Complex.arg (x + y)
  set B : ℝ := Complex.arg (x - y)
  have hA : x + y = Complex.exp ((A : ℂ) * Complex.I) := eq_exp_arg_mul_I hlp
  have hB : x - y = Complex.exp ((B : ℂ) * Complex.I) := eq_exp_arg_mul_I hlm
  obtain ⟨ψ, φ, hψ, hφ⟩ : ∃ ψ φ : ℝ, ψ + φ = A ∧ ψ - φ = B - Real.pi :=
    ⟨(A + B) / 2 - Real.pi / 2, (A - B) / 2 + Real.pi / 2, by ring, by ring⟩
  refine ⟨ψ, φ, ?_, ?_⟩
  · have hA' : (A : ℂ) = ((ψ + φ : ℝ) : ℂ) := by rw [hψ]
    have hB2 : B = (ψ - φ) + Real.pi := by linarith [hφ]
    have hB' : (B : ℂ) = (((ψ - φ) + Real.pi : ℝ) : ℂ) := by rw [hB2]
    have hx : x = (Complex.exp ((A : ℂ) * Complex.I) + Complex.exp ((B : ℂ) * Complex.I)) / 2 := by
      rw [← hA, ← hB]; ring
    rw [hx, hA', hB', exp_add_pi]
    exact exp_sin_split ψ φ
  · have hA' : (A : ℂ) = ((ψ + φ : ℝ) : ℂ) := by rw [hψ]
    have hB2 : B = (ψ - φ) + Real.pi := by linarith [hφ]
    have hB' : (B : ℂ) = (((ψ - φ) + Real.pi : ℝ) : ℂ) := by rw [hB2]
    have hy : y = (Complex.exp ((A : ℂ) * Complex.I) - Complex.exp ((B : ℂ) * Complex.I)) / 2 := by
      rw [← hA, ← hB]; ring
    rw [hy, hA', hB', exp_add_pi, sub_neg_eq_add]
    exact exp_cos_split ψ φ

theorem eq24_classification {A B C D : ℂ} (hA : A ≠ 0)
    (h1 : redM A B * (redM A B)ᴴ + red0 C D * (red0 C D)ᴴ + redP A B * (redP A B)ᴴ = 1)
    (h2 : red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ = 0) :
    ∃ ψ ρ θ : ℝ,
      A = Complex.exp ((ψ : ℂ) * Complex.I) *
            (Complex.I * ((Real.cos ρ : ℂ) * (Real.sin θ : ℂ))) ∧
      B = Complex.exp ((ψ : ℂ) * Complex.I) * ((Real.cos ρ : ℂ) * (Real.cos θ : ℂ)) ∧
      C = Complex.exp ((ψ : ℂ) * Complex.I) * ((Real.sin ρ : ℂ) * (Real.sin θ : ℂ)) ∧
      D = Complex.exp ((ψ : ℂ) * Complex.I) *
            (-(Complex.I * ((Real.sin ρ : ℂ) * (Real.cos θ : ℂ)))) := by

  have hsum : par2 (A * star A + B * star B + C * star C + D * star D)
      (A * star B + B * star A + C * star D + D * star C) = 1 := by
    rw [← red19m A B C D]
    exact h1
  obtain ⟨hX, hY⟩ := (par2_eq_one_iff _ _).mp hsum

  have hmat : (red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ) = 0 := h2
  have h00 : D * star A + B * star C = 0 := by
    have h := congrFun (congrFun hmat 0) 0
    rw [red19z_00] at h
    simpa using h
  have h10 : C * star A + A * star C = 0 := by
    have h := congrFun (congrFun hmat 1) 0
    rw [red19z_10] at h
    simpa using h

  have hreCA : (C * star A).re = 0 := re_mul_star_eq_zero h10
  obtain ⟨w, hCw⟩ := exists_smul_I hA hreCA

  have hDw : D = ((w : ℝ) : ℂ) * Complex.I * B := eq_smul_I_of_add hA hCw h00

  have hXre : Complex.normSq A + Complex.normSq B + Complex.normSq C + Complex.normSq D = 1 := by
    have h := congrArg Complex.re hX
    simp only [Complex.add_re, Complex.one_re] at h
    rw [re_mul_star_self, re_mul_star_self, re_mul_star_self, re_mul_star_self] at h
    exact h
  have hnorm : (1 + w ^ 2) * (Complex.normSq A + Complex.normSq B) = 1 := by
    have hC' : Complex.normSq C = w * w * Complex.normSq A := by rw [hCw, normSq_smul_I_mul]
    have hD' : Complex.normSq D = w * w * Complex.normSq B := by rw [hDw, normSq_smul_I_mul]
    rw [hC', hD'] at hXre
    have e : Complex.normSq A + Complex.normSq B + w * w * Complex.normSq A
        + w * w * Complex.normSq B
        = (1 + w ^ 2) * (Complex.normSq A + Complex.normSq B) := by ring
    rw [e] at hXre
    exact hXre

  have hCsD : C * star D = ((w : ℝ) : ℂ) ^ 2 * (A * star B) := by
    rw [hCw, hDw, mul_star_smul_I]
  have hDsC : D * star C = ((w : ℝ) : ℂ) ^ 2 * (B * star A) := by
    rw [hDw, hCw, mul_star_smul_I]
  have horth : A * star B + B * star A = 0 := by
    rw [hCsD, hDsC] at hY
    have e : A * star B + B * star A + ((w : ℝ) : ℂ) ^ 2 * (A * star B)
        + ((w : ℝ) : ℂ) ^ 2 * (B * star A)
        = ((1 + w ^ 2 : ℝ) : ℂ) * (A * star B + B * star A) := by push_cast; ring
    rw [e] at hY
    have hc : ((1 + w ^ 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]
      nlinarith [sq_nonneg w]
    exact (mul_eq_zero.mp hY).resolve_left hc

  have hsumA : A * star A + B * star B = (((1 : ℝ) / (1 + w ^ 2)) : ℂ) := by
    have hne : (1 + w ^ 2 : ℝ) ≠ 0 := by nlinarith [sq_nonneg w]
    have hdiv : Complex.normSq A + Complex.normSq B = 1 / (1 + w ^ 2) := by
      rw [eq_div_iff hne]
      linarith [hnorm]
    rw [mul_star_self_real A, mul_star_self_real B, ← Complex.ofReal_add, hdiv]
    push_cast
    ring

  set s : ℝ := Real.sqrt (1 + w ^ 2) with hs
  have hspos : (0 : ℝ) < 1 + w ^ 2 := by nlinarith [sq_nonneg w]
  have hs2 : s * s = 1 + w ^ 2 := by
    rw [hs]
    exact Real.mul_self_sqrt (le_of_lt hspos)
  have hsne : s ≠ 0 := by
    rw [hs]
    exact Real.sqrt_ne_zero'.mpr hspos
  have hsne_c : ((s : ℝ) : ℂ) ≠ 0 := by simpa using hsne
  have hx1 : ((s : ℂ) * A) * star ((s : ℂ) * A) + ((s : ℂ) * B) * star ((s : ℂ) * B) = 1 := by
    have eA : ((s : ℂ) * A) * star ((s : ℂ) * A) = ((s * s : ℝ) : ℂ) * (A * star A) := by
      rw [star_mul]
      have hs' : star (s : ℂ) = (s : ℂ) := by simp
      rw [hs']
      push_cast
      ring
    have eB : ((s : ℂ) * B) * star ((s : ℂ) * B) = ((s * s : ℝ) : ℂ) * (B * star B) := by
      rw [star_mul]
      have hs' : star (s : ℂ) = (s : ℂ) := by simp
      rw [hs']
      push_cast
      ring
    rw [eA, eB, ← mul_add, mul_star_self_real A, mul_star_self_real B, ← Complex.ofReal_add,
        ← Complex.ofReal_mul, hs2, hnorm, Complex.ofReal_one]
  have hx2 : ((s : ℂ) * A) * star ((s : ℂ) * B) + ((s : ℂ) * B) * star ((s : ℂ) * A) = 0 := by
    have eA : ((s : ℂ) * A) * star ((s : ℂ) * B) = ((s * s : ℝ) : ℂ) * (A * star B) := by
      rw [star_mul]
      have hs' : star (s : ℂ) = (s : ℂ) := by simp
      rw [hs']
      push_cast
      ring
    have eB : ((s : ℂ) * B) * star ((s : ℂ) * A) = ((s * s : ℝ) : ℂ) * (B * star A) := by
      rw [star_mul]
      have hs' : star (s : ℂ) = (s : ℂ) := by simp
      rw [hs']
      push_cast
      ring
    rw [eA, eB, ← mul_add, horth, mul_zero]
  obtain ⟨ψ, θ, hAn, hBn⟩ := pair_normal_form hx1 hx2

  set ρ : ℝ := Real.arctan (-w) with hρ
  have hcosρ : Real.cos ρ = 1 / s := by
    rw [hρ, Real.cos_arctan]
    have h1w : (1 : ℝ) + (-w) ^ 2 = 1 + w ^ 2 := by ring
    rw [h1w, ← hs]
  have hsinρ : Real.sin ρ = -w / s := by
    rw [hρ, Real.sin_arctan]
    have h1w : (1 : ℝ) + (-w) ^ 2 = 1 + w ^ 2 := by ring
    rw [h1w, ← hs]
  have hcosρ' : ((Real.cos ρ : ℝ) : ℂ) = (s : ℂ)⁻¹ := by
    rw [hcosρ, ← Complex.ofReal_inv]
    norm_num
  have hsinρ' : ((Real.sin ρ : ℝ) : ℂ) = -(((w : ℝ) : ℂ) * (s : ℂ)⁻¹) := by
    rw [hsinρ]
    push_cast
    ring
  have hs_inv : A = (s : ℂ)⁻¹ * ((s : ℂ) * A) := by
    rw [← mul_assoc, inv_mul_cancel₀ hsne_c, one_mul]
  have hBs_inv : B = (s : ℂ)⁻¹ * ((s : ℂ) * B) := by
    rw [← mul_assoc, inv_mul_cancel₀ hsne_c, one_mul]
  refine ⟨ψ, ρ, θ, ?_, ?_, ?_, ?_⟩
  · rw [hs_inv, hAn, hcosρ']
    ring
  · rw [hBs_inv, hBn, hcosρ']
    ring
  · rw [hCw, hs_inv, hAn]
    have hassoc : (s : ℂ)⁻¹ * (Complex.exp ((ψ : ℂ) * Complex.I) *
          (Complex.I * (Real.sin θ : ℂ)))
        = ((s : ℂ)⁻¹ * Complex.exp ((ψ : ℂ) * Complex.I)) *
          (Complex.I * (Real.sin θ : ℂ)) := by ring
    rw [hassoc, smul_I_mul_mul_I, hsinρ']
    ring
  · rw [hDw, hBs_inv, hBn, hsinρ']
    ring

theorem eq24_classification_of_eq19 {A B C D : ℂ} (hA : A ≠ 0)
    (h19 : Eq19 (redM A B) (red0 C D) (redP A B)) :
    ∃ ψ ρ θ : ℝ,
      redM A B = Complex.exp ((ψ : ℂ) * Complex.I) • eq24wm θ ρ ∧
      red0 C D = Complex.exp ((ψ : ℂ) * Complex.I) • eq24w0 θ ρ ∧
      redP A B = Complex.exp ((ψ : ℂ) * Complex.I) • eq24wp θ ρ := by
  obtain ⟨h1, h2, -⟩ := h19
  have h1' : redM A B * (redM A B)ᴴ + red0 C D * (red0 C D)ᴴ
      + redP A B * (redP A B)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using h1
  have h2' : red0 C D * (redM A B)ᴴ + redP A B * (red0 C D)ᴴ = 0 := by
    simpa only [Matrix.star_eq_conjTranspose] using h2
  obtain ⟨ψ, ρ, θ, hAe, hBe, hCe, hDe⟩ := eq24_classification hA h1' h2'
  refine ⟨ψ, ρ, θ, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [redM, eq24wm, Matrix.smul_apply, hAe, hBe] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [red0, eq24w0, Matrix.smul_apply, hCe, hDe] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [redP, eq24wp, Matrix.smul_apply, hAe, hBe] <;> ring

end Qatlib.Papers.QCellAutomata96.MainResults
