/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxEndpointNormalization

/-!
# Compiling Fourier approximations into source phases

This module turns a polynomial Fourier approximation to `exp (Complex.I * h θ)` into a source
phase list in the quantum signal processing framework [LowChuang2017]. The input consists of an
even real polynomial `A`, an odd real polynomial `Qt`, and a uniform error bound on the angle
interval `[0, 2 * Real.pi]`.

The theorem `lcScaledFourierPair` rescales the pair by `1 / (1 + ε)` to obtain the weighted
square bound needed for completion, with approximation error at most `2 * ε`. Real completion
and endpoint normalization then yield `lcSourceCompilation`: for positive even `N`, odd `h`, and
`0 < ε ≤ 1 / 16`, a list of length `N` whose `lcPlusAmp` error is at most `8 * ε`.

## Main statements

* `lcScaledFourierPair` preserves parity and degree bounds while making the polynomial pair
  contractive.
* `lcFourierNormSq` identifies the squared amplitude norm with the weighted polynomial square
  sum.
* `lcSourceCompilation` produces source phases with the stated length and uniform approximation
  bound.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel

open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Concepts.QspSimulation.Achievability
open Polynomial
section Helpers

/-- Composing a constant real polynomial with any real polynomial leaves the constant polynomial
unchanged. -/
private theorem lcC_comp_real (s : ℝ) (p : Polynomial ℝ) :
    (Polynomial.C s).comp p = Polynomial.C s := by
  simp [Polynomial.comp]

/-- The complex norm of a real number embedded in the complex numbers is its real absolute
value. -/
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

/-- The complex exponential of `Complex.I` times a real number has norm one. -/
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

/-- Rescaling the input Fourier polynomial pair by `1 / (1 + ε)` preserves its parity and degree
bounds and makes its weighted square sum at most one on `[-1, 1]`. Its approximation to the
target exponential at angle `2 * Real.arccos x` has error at most `2 * ε`. -/
theorem lcScaledFourierPair (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (N : WithBot ℕ)) (hQtdeg : Qt.degree < (N : WithBot ℕ))
    (hεpos : 0 < ε)
    (happrox : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) *
        realEval Qt (Real.cos (θ / 2) : ℂ) - Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) :
    let s := 1 / (1 + ε)
    (C s * A).comp (-X) = C s * A ∧ (C s * Qt).comp (-X) = -(C s * Qt) ∧
    (C s * A).degree ≤ (N : WithBot ℕ) ∧ (C s * Qt).degree < (N : WithBot ℕ) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (C s * A).eval x * (C s * A).eval x +
        (1 - x * x) * ((C s * Qt).eval x * (C s * Qt).eval x) ≤ 1) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖realEval (C s * A) (x : ℂ) + Complex.I * (Real.sqrt (1 - x * x) : ℂ) *
        realEval (C s * Qt) (x : ℂ) -
        Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ≤ 2 * ε) := by
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
  refine ⟨hA₁even, hQt₁odd, hA₁deg, hQt₁deg, hcond₁, ?_⟩
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
  rw [hA₁val, hQt₁val, hscale]
  exact hb2

/-- On `[-1, 1]`, the squared norm of the Fourier amplitude of `A` and `Qt` equals `A.eval x ^ 2
+ (1 - x * x) * Qt.eval x ^ 2`. -/
theorem lcFourierNormSq (A Qt : Polynomial ℝ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖realEval A (x : ℂ) + Complex.I * (Real.sqrt (1 - x * x) : ℂ) * realEval Qt (x : ℂ)‖ ^ 2 =
      A.eval x ^ 2 + (1 - x * x) * Qt.eval x ^ 2 := by
  have ht : 0 ≤ 1 - x * x := by nlinarith [hx.1, hx.2]
  simp only [realEval, map_eval_ofReal]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith [Real.sq_sqrt ht]

/-- For positive even `N`, odd `h`, and `0 < ε ≤ 1 / 16`, the stated polynomial Fourier
approximation yields a source phase list of length `N`. Its `lcPlusAmp` approximates `exp
(Complex.I * h θ)` uniformly within `8 * ε` on `[0, 2 * Real.pi]`. -/
theorem lcSourceCompilation (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ)
    (hN : Even N) (hp : 0 < N) (hodd : ∀ θ, h (-θ) = -h θ)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (N : WithBot ℕ)) (hQtdeg : Qt.degree < (N : WithBot ℕ))
    (hεpos : 0 < ε) (hε16 : ε ≤ 1 / 16)
    (happrox : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (θ / 2) : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) *
        realEval Qt (Real.cos (θ / 2) : ℂ) - Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) :
    ∃ phis : List ℝ, phis.length = N ∧
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        ‖lcPlusAmp phis θ - Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ 8 * ε := by
  let A₁ := C (1 / (1 + ε)) * A
  let Q₁ := C (1 / (1 + ε)) * Qt
  obtain ⟨ha, hq, had, hqd, hcond, happ⟩ :=
    lcScaledFourierPair N h A Qt ε hAeven hQtodd hAdeg hQtdeg hεpos happrox
  obtain ⟨B, D, hsos, hbdeg, _, hbpar, _⟩ :=
    lcRealCompletion N A₁ Q₁ hN hp ha hq had hqd hcond
  have hcompletion : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      A₁.eval x ^ 2 + B.eval x ^ 2 + (1 - x * x) * Q₁.eval x ^ 2 ≤ 1 := by
    intro x hx
    have hh := congrArg (Polynomial.eval x) hsos
    simp only [eval_sub, eval_mul, eval_pow, eval_one, eval_X, eval_add] at hh
    have ht : 0 ≤ 1 - x * x := by nlinarith [hx.1, hx.2]
    have hn := mul_nonneg ht (sq_nonneg (D.eval x))
    nlinarith [hh]
  have hone : A₁.eval 1 ^ 2 + B.eval 1 ^ 2 = 1 := by
    have hh := congrArg (Polynomial.eval 1) hsos
    norm_num only [eval_sub, eval_mul, eval_pow, eval_one, eval_X, eval_add,
      one_pow, sub_self, zero_mul, sub_zero] at hh
    linarith
  have hAbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |A₁.eval x| ≤ 1 := by
    intro x hx
    have hh := hcompletion x hx
    have ht : 0 ≤ 1 - x * x := by nlinarith [hx.1, hx.2]
    have hn := mul_nonneg ht (sq_nonneg (Q₁.eval x))
    exact abs_le.mpr ⟨by nlinarith [sq_nonneg (B.eval x)], by nlinarith [sq_nonneg (B.eval x)]⟩
  have hBbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, B.eval x ^ 2 ≤ 4 * ε := by
    intro x hx
    let w := realEval A₁ (x : ℂ) + Complex.I * (Real.sqrt (1 - x * x) : ℂ) * realEval Q₁ (x : ℂ)
    let e := Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))
    have happx : ‖w - e‖ ≤ 2 * ε := happ x hx
    have hnorm : ‖e‖ = 1 := norm_exp_I _
    have hrev := norm_sub_norm_le e w
    rw [hnorm, norm_sub_rev] at hrev
    have hsq := lcFourierNormSq A₁ Q₁ x hx
    have hc := hcompletion x hx
    change ‖w‖ ^ 2 = _ at hsq
    have hnon : 0 ≤ 1 - 2 * ε := by linarith
    have hge : 1 - 2 * ε ≤ ‖w‖ := by linarith
    have hl : (1 - 2 * ε) ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    nlinarith [sq_nonneg ε]
  have hzero : h 0 = 0 := by have hh := hodd 0; simp only [neg_zero] at hh; linarith
  have haone : |A₁.eval 1 - 1| ≤ 2 * ε := by
    have hh := happ 1 (by norm_num)
    change ‖realEval A₁ (1 : ℂ) + Complex.I * (Real.sqrt (1 - 1 * 1) : ℂ) * realEval Q₁ (1 : ℂ)
      - Complex.exp (Complex.I * (h (2 * Real.arccos 1) : ℂ))‖ ≤ 2 * ε at hh
    have heval : realEval A₁ (1 : ℂ) = ((A₁.eval 1 : ℝ) : ℂ) := map_eval_ofReal A₁ 1
    rw [heval] at hh
    norm_num only [Real.arccos_one, mul_zero, hzero, Complex.ofReal_zero,
      sub_self, Real.sqrt_zero, zero_mul, add_zero, Complex.exp_zero,
      one_mul, sub_zero, Complex.ofReal_one] at hh
    rw [show ((A₁.eval 1 : ℝ) : ℂ) - 1 = ((A₁.eval 1 - 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_ofReal'] at hh
    exact hh
  obtain ⟨phis, hlen, hamp⟩ := lcEndpointNormalize_source N A₁ B Q₁ hN hp ha hbpar hq
    had hbdeg hqd hone hcompletion
  refine ⟨phis, hlen, ?_⟩
  intro θ hθ
  let x := Real.cos (θ / 2)
  have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have harc : 2 * Real.arccos x = θ := by
    rw [show x = Real.cos (θ / 2) from rfl,
      Real.arccos_cos (by linarith [hθ.1]) (by linarith [hθ.2])]
    ring
  have hsin : Real.sqrt (1 - x * x) = Real.sin (θ / 2) := by
    have ht := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1] : 0 ≤ θ / 2)
      (by linarith [hθ.2] : θ / 2 ≤ Real.pi)
    rw [show 1 - x * x = Real.sin (θ / 2) ^ 2 by
      dsimp [x]; nlinarith [Real.sin_sq_add_cos_sq (θ / 2)], Real.sqrt_sq ht]
  let w₁ := realEval A₁ (x : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) * realEval Q₁ (x : ℂ)
  have he : ‖w₁ - Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ 2 * ε := by
    have hh := happ x hx
    rw [harc, hsin] at hh
    exact hh
  have hdiff : ‖lcPlusAmp phis θ - w₁‖ ≤ 6 * ε := by
    rw [hamp θ hθ]
    change ‖(realEval (lcEndpointNormalize A₁ B) (x : ℂ) +
        Complex.I * (Real.sin (θ / 2) : ℂ) * realEval Q₁ (x : ℂ)) -
      (realEval A₁ (x : ℂ) + Complex.I * (Real.sin (θ / 2) : ℂ) * realEval Q₁ (x : ℂ))‖ ≤ 6 * ε
    rw [show ∀ a b c : ℂ, (a + c) - (b + c) = a - b by intros; ring]
    simp only [realEval, map_eval_ofReal]
    rw [← Complex.ofReal_sub, norm_ofReal']
    exact lcEndpointNormalize_error A₁ B x ε (le_of_lt hεpos) (hAbound x hx)
      haone (hBbound 1 (by norm_num)) (hBbound x hx)
  calc
    ‖lcPlusAmp phis θ - Complex.exp (Complex.I * (h θ : ℂ))‖ =
        ‖(lcPlusAmp phis θ - w₁) + (w₁ - Complex.exp (Complex.I * (h θ : ℂ)))‖ := by congr 1; ring
    _ ≤ ‖lcPlusAmp phis θ - w₁‖ + ‖w₁ - Complex.exp (Complex.I * (h θ : ℂ))‖ := norm_add_le _ _
    _ ≤ 8 * ε := by linarith

end Qatlib.Concepts.QspSimulation.Achievability
