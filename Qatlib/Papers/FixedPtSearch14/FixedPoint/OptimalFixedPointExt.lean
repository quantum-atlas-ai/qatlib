/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExtDefs
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Qatlib
open Matrix

theorem l3_unit_abs (delta : ℝ) : ‖l3Unit delta‖ = 1 := by
  have hre : (-(Complex.I * (l3Phase delta : ℝ))).re = 0 := by
    rw [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [l3Unit, l3PhaseUnit, Complex.norm_exp, hre, Real.exp_zero]

theorem l3_unit_conj (delta : ℝ) :
    starRingEnd ℂ (l3Unit delta) + l3Unit delta = 2 * (Real.cos (l3Phase delta) : ℂ) := by
  have hre : (l3Unit delta).re = Real.cos (l3Phase delta) := by
    rw [l3Unit, l3PhaseUnit, Complex.exp_re]
    have hz : (-(Complex.I * (l3Phase delta : ℝ))).re = 0 := by
      rw [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hzi : (-(Complex.I * (l3Phase delta : ℝ))).im = -(l3Phase delta) := by
      rw [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hz, hzi, Real.exp_zero, Real.cos_neg]
    ring
  calc starRingEnd ℂ (l3Unit delta) + l3Unit delta
      = l3Unit delta + starRingEnd ℂ (l3Unit delta) := by ring
    _ = ((2 * (l3Unit delta).re : ℝ) : ℂ) := Complex.add_conj _
    _ = 2 * (Real.cos (l3Phase delta) : ℂ) := by rw [hre]; push_cast; ring

theorem l3_failure_amplitude_factor (delta lam : ℝ) (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicFailureAmplitude 1 delta lam =
      -(((Real.sqrt (1 - lam) : ℝ) : ℂ) * l3Unit delta *
        ((l3FailureFactor delta lam : ℝ) : ℂ)) := by
  have htu : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hl]
  have hu : l3Unit delta * starRingEnd ℂ (l3Unit delta) = 1 := by
    have harg' : starRingEnd ℂ (-(Complex.I * (l3Phase delta : ℝ))) =
        Complex.I * (l3Phase delta : ℝ) := by
      rw [map_neg (starRingEnd ℂ), map_mul (starRingEnd ℂ), Complex.conj_ofReal,
        Complex.conj_I]
      ring
    have h2 : starRingEnd ℂ (l3Unit delta) =
        Complex.exp (Complex.I * (l3Phase delta : ℝ)) := by
      rw [l3Unit, l3PhaseUnit, Eq.symm (Complex.exp_conj _), harg']
    rw [h2]
    rw [l3Unit, l3PhaseUnit, ← Complex.exp_add]
    have hz : -(Complex.I * (l3Phase delta : ℝ)) + Complex.I * (l3Phase delta : ℝ) = 0 := by
      ring
    rw [hz, Complex.exp_zero]
  have hf := l3_failure_amplitude delta lam hl hl'
  rw [hf]
  rw [← l3Unit_eq]
  have hbracket :
      ((1 - (lam : ℂ)) * l3Unit delta + (lam : ℂ)) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) +
          ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) *
            (l3Unit delta - 1) * (l3Unit delta * ((Real.sqrt lam : ℝ) : ℂ))
        = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * l3Unit delta *
          ((lam : ℂ) * (starRingEnd ℂ (l3Unit delta) + l3Unit delta) +
            (1 - 2 * (lam : ℂ))) := by
    calc
      _ = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
            (((1 - (lam : ℂ)) * l3Unit delta + (lam : ℂ)) +
              ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) *
                (l3Unit delta - 1) * l3Unit delta) := by ring
      _ = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
            (((1 - (lam : ℂ)) * l3Unit delta + (lam : ℂ)) +
              (lam : ℂ) * (l3Unit delta - 1) * l3Unit delta) := by
            rw [show ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = (lam : ℂ)
              from htu]
      _ = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
            ((lam : ℂ) * l3Unit delta ^ 2 + (1 - 2 * (lam : ℂ)) * l3Unit delta +
              (lam : ℂ)) := by ring
      _ = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * l3Unit delta *
            ((lam : ℂ) * (starRingEnd ℂ (l3Unit delta) + l3Unit delta) +
              (1 - 2 * (lam : ℂ))) := by
            calc
              ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
                    ((lam : ℂ) * l3Unit delta ^ 2 + (1 - 2 * (lam : ℂ)) * l3Unit delta +
                      (lam : ℂ))
                = ((Real.sqrt (1 - lam) : ℝ) : ℂ) *
                    (l3Unit delta * ((lam : ℂ) * (starRingEnd ℂ (l3Unit delta) + l3Unit delta) +
                        (1 - 2 * (lam : ℂ))) +
                      (lam : ℂ) * (1 - l3Unit delta * starRingEnd ℂ (l3Unit delta))) := by ring
              _ = ((Real.sqrt (1 - lam) : ℝ) : ℂ) * l3Unit delta *
                    ((lam : ℂ) * (starRingEnd ℂ (l3Unit delta) + l3Unit delta) +
                      (1 - 2 * (lam : ℂ))) := by
                    have hz : (lam : ℂ) * (1 - l3Unit delta * starRingEnd ℂ (l3Unit delta)) = 0 := by
                      rw [hu]
                      ring
                    rw [hz]
                    ring
  rw [hbracket]
  rw [l3_unit_conj delta]
  simp only [l3FailureFactor]
  push_cast
  ring

theorem l3_width_identity (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    l3WidthValue delta = delta * (4 - 3 * (ylcGamma 3 delta) ^ 2) := by
  have hw := widthIdentity 3 delta (by omega) ⟨hd, hd'⟩
  have hγlt : ylcGamma 3 delta < 1 := hw.2.1
  have h1 : 1 ≤ 1 / delta := one_le_one_div_of_le hd (le_of_lt hd')
  have hmain : Real.cosh (Real.arcosh (1 / delta)) = 1 / delta := Real.cosh_arcosh h1
  have htriple : Real.cosh (Real.arcosh (1 / delta)) =
      Real.cosh (Real.arcosh (1 / delta) / 3) *
        (4 * Real.cosh (Real.arcosh (1 / delta) / 3) ^ 2 - 3) := by
    have h := Real.cosh_three_mul (Real.arcosh (1 / delta) / 3)
    rw [show (3 * (Real.arcosh (1 / delta) / 3)) = Real.arcosh (1 / delta) by ring] at h
    calc Real.cosh (Real.arcosh (1 / delta))
        = 4 * Real.cosh (Real.arcosh (1 / delta) / 3) ^ 3 -
            3 * Real.cosh (Real.arcosh (1 / delta) / 3) := h
      _ = Real.cosh (Real.arcosh (1 / delta) / 3) *
          (4 * Real.cosh (Real.arcosh (1 / delta) / 3) ^ 2 - 3) := by ring
  have hpos : 0 < Real.cosh (Real.arcosh (1 / delta) / 3) := Real.cosh_pos _
  have hB : 4 - 3 * (ylcGamma 3 delta) ^ 2 ≠ 0 := by
    have : 0 < 4 - 3 * (ylcGamma 3 delta) ^ 2 := by nlinarith [hγlt]
    exact ne_of_gt this
  have hkey : delta * (Real.cosh (Real.arcosh (1 / delta) / 3) *
      (4 * Real.cosh (Real.arcosh (1 / delta) / 3) ^ 2 - 3)) = 1 := by
    rw [← htriple, hmain]
    field_simp [ne_of_gt hd]
  have hγ : ylcGamma 3 delta = 1 / Real.cosh (Real.arcosh (1 / delta) / 3) := rfl
  rw [l3WidthValue, hγ]
  have hnonzero : Real.cosh (Real.arcosh (1 / delta) / 3) ≠ 0 := ne_of_gt hpos
  field_simp [hnonzero]
  nlinarith [hkey]

theorem l3_width_cubed (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    (ylcGamma 3 delta) ^ 3 = delta * (4 - 3 * (ylcGamma 3 delta) ^ 2) :=
  l3_width_identity delta hd hd'

theorem l3_failure_prob (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicFailureProb 1 delta lam =
      (delta * cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)) ^ 2 := by
  have hw := widthIdentity 3 delta (by omega) ⟨hd, hd'⟩
  have hγpos : 0 < ylcGamma 3 delta := hw.1
  have hγlt : ylcGamma 3 delta < 1 := hw.2.1
  have hB : 4 - 3 * (ylcGamma 3 delta) ^ 2 ≠ 0 := by
    have : 0 < 4 - 3 * (ylcGamma 3 delta) ^ 2 := by nlinarith [hγlt]
    exact ne_of_gt this
  have hwidth := l3_width_identity delta hd hd'
  have hnorm : ‖publicFailureAmplitude 1 delta lam‖ ^ 2 =
      (1 - lam) * (l3FailureFactor delta lam) ^ 2 := by
    have hfactor := l3_failure_amplitude_factor delta lam hl hl'
    rw [hfactor]
    have hs : ‖((Real.sqrt (1 - lam) : ℝ) : ℂ)‖ ^ 2 = 1 - lam := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by linarith)]
    have hu : ‖l3Unit delta‖ ^ 2 = 1 := by rw [l3_unit_abs]; norm_num
    have hr : ‖((l3FailureFactor delta lam : ℝ) : ℂ)‖ ^ 2 =
        (l3FailureFactor delta lam) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    have hsq' : ‖-(((Real.sqrt (1 - lam) : ℝ) : ℂ) * l3Unit delta *
          ((l3FailureFactor delta lam : ℝ) : ℂ))‖ ^ 2
        = (‖((Real.sqrt (1 - lam) : ℝ) : ℂ)‖ ^ 2) * (‖l3Unit delta‖ ^ 2) *
          (‖((l3FailureFactor delta lam : ℝ) : ℂ)‖ ^ 2) := by
      rw [norm_neg, norm_mul, norm_mul]
      ring
    rw [hsq', hs, hu, hr]
    ring
  have hR : l3FailureFactor delta lam =
      (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2) / (4 - 3 * (ylcGamma 3 delta) ^ 2) := by
    have hcos := l3_cos_identity delta
    have hmu : (l3HalfWidth delta) ^ 2 = 1 - (ylcGamma 3 delta) ^ 2 := by
      have hnonneg : 0 ≤ 1 - (ylcGamma 3 delta) ^ 2 := by nlinarith [hγpos, hγlt]
      rw [l3HalfWidth]
      exact Real.sq_sqrt hnonneg
    have hEq : 1 + 3 * (1 - (ylcGamma 3 delta) ^ 2) =
        4 - 3 * (ylcGamma 3 delta) ^ 2 := by ring
    rw [l3FailureFactor, hcos, hmu, hEq]
    field_simp [hB]
    ring
  have hcheb : cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta) =
      (Real.sqrt (1 - lam) / (ylcGamma 3 delta) ^ 3) *
        (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2) := by
    rw [cheb_three]
    have hsq : (Real.sqrt (1 - lam) : ℝ) ^ 2 = 1 - lam := Real.sq_sqrt (by linarith)
    calc
      4 * (Real.sqrt (1 - lam) / ylcGamma 3 delta) ^ 3
          - 3 * (Real.sqrt (1 - lam) / ylcGamma 3 delta)
        = (Real.sqrt (1 - lam) / (ylcGamma 3 delta) ^ 3) *
            (4 * (Real.sqrt (1 - lam) : ℝ) ^ 2 - 3 * (ylcGamma 3 delta) ^ 2) := by
          field_simp [hγpos.ne']
      _ = (Real.sqrt (1 - lam) / (ylcGamma 3 delta) ^ 3) *
            (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2) := by rw [hsq]
  have hratio : delta / (ylcGamma 3 delta) ^ 3 =
      1 / (4 - 3 * (ylcGamma 3 delta) ^ 2) := by
    have hγ3 : (ylcGamma 3 delta) ^ 3 ≠ 0 := by positivity
    rw [l3_width_cubed delta hd hd']
    field_simp [hB, hγ3, ne_of_gt hd]
  have hratio' : delta * (Real.sqrt (1 - lam) / (ylcGamma 3 delta) ^ 3 *
      (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2))
    = (Real.sqrt (1 - lam) * (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2)) /
        (4 - 3 * (ylcGamma 3 delta) ^ 2) := by
    have hγ3 : (ylcGamma 3 delta) ^ 3 ≠ 0 := by positivity
    rw [l3_width_cubed delta hd hd']
    field_simp [hB, hγ3, ne_of_gt hd]
  rw [publicFailureProb, hnorm, hR, hcheb]
  have hsq : Real.sqrt (1 - lam) ^ 2 = 1 - lam := Real.sq_sqrt (by linarith)
  calc
    (1 - lam) * ((4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2) /
        (4 - 3 * (ylcGamma 3 delta) ^ 2)) ^ 2
        = (Real.sqrt (1 - lam) * (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2) /
            (4 - 3 * (ylcGamma 3 delta) ^ 2)) ^ 2 := by
          nth_rewrite 1 [← hsq]
          ring
    _ = (delta * (Real.sqrt (1 - lam) / (ylcGamma 3 delta) ^ 3 *
            (4 * (1 - lam) - 3 * (ylcGamma 3 delta) ^ 2))) ^ 2 := by
        rw [hratio']

theorem l3_success_prob (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hl : 0 ≤ lam) (hl' : lam ≤ 1) :
    publicSuccessProb 1 delta lam = responseProb 3 delta lam := by
  have hnorm : ‖publicFailureAmplitude 1 delta lam‖ ^ 2
      + ‖publicSuccessAmplitude 1 delta lam‖ ^ 2 = 1 := by
    have htwo := two_component_normSq (publicWord 1 delta lam *ᵥ ampState lam)
    have hψ : Normalized (publicWord 1 delta lam *ᵥ ampState lam) := by
      have hU := publicWord_unitary 1 delta lam hl hl'
      have hs := ampState_normalized hl hl'
      simpa [ApplyGate] using normalized_applyGate hU hs
    have hsum : (∑ i, ‖(publicWord 1 delta lam *ᵥ ampState lam) i‖ ^ 2) = 1 := hψ
    have h1 := htwo
    rw [hsum] at h1
    simpa [publicFailureAmplitude, publicSuccessAmplitude, add_comm] using h1
  have hfail := l3_failure_prob delta lam hd hd' hl hl'
  have hresp : responseProb 3 delta lam =
      1 - (delta * cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)) ^ 2 :=
    responseProb_eq 3 delta lam
  have h1 : publicFailureProb 1 delta lam + publicSuccessProb 1 delta lam = 1 := by
    rw [publicFailureProb, publicSuccessProb]
    linarith [hnorm]
  have h2 : publicSuccessProb 1 delta lam = 1 - publicFailureProb 1 delta lam := by
    linarith [h1]
  rw [h2, hfail, hresp]

theorem l3_endpoints (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    publicSuccessProb 1 delta 0 = 0 ∧ publicSuccessProb 1 delta 1 = 1 := by
  have h0 := l3_success_prob delta 0 hd hd' (by norm_num) (by norm_num)
  have h1 := l3_success_prob delta 1 hd hd' (by norm_num) (by norm_num)
  have hw := widthIdentity 3 delta (by omega) ⟨hd, hd'⟩
  have hresp0 : responseProb 3 delta 0 = 0 := by
    rw [responseProb_eq]
    have hsqrt : Real.sqrt (1 - 0) = 1 := by simp
    rw [hsqrt, hw.2.2]
    field_simp [ne_of_gt hd]
    ring
  have hresp1 : responseProb 3 delta 1 = 1 := by
    rw [responseProb_eq]
    have hsqrt : Real.sqrt (1 - 1) = 0 := by simp
    rw [hsqrt, zero_div, cheb_zero_of_odd (⟨1, by omega⟩ : Odd 3), mul_zero]
    ring
  rw [h0, hresp0]
  rw [h1, hresp1]
  exact ⟨rfl, rfl⟩

theorem l3_guarantee (delta lam : ℝ) (hd : 0 < delta) (hd' : delta < 1)
    (hl : 1 - (ylcGamma 3 delta) ^ 2 ≤ lam) (hl' : lam ≤ 1) :
    1 - delta ^ 2 ≤ publicSuccessProb 1 delta lam := by
  have hw := widthIdentity 3 delta (by omega) ⟨hd, hd'⟩
  have hγpos : 0 < ylcGamma 3 delta := hw.1
  have hγlo : 0 < 1 - (ylcGamma 3 delta) ^ 2 := by nlinarith [hγpos, hw.2.1]
  have hsucc := l3_success_prob delta lam hd hd' (by linarith [hγlo]) hl'
  rw [hsucc, responseProb_eq]
  have hy0 : 0 ≤ Real.sqrt (1 - lam) / ylcGamma 3 delta := by
    apply div_nonneg
    · exact Real.sqrt_nonneg _
    · linarith [hl']
  have hy1 : Real.sqrt (1 - lam) / ylcGamma 3 delta ≤ 1 := by
    apply (div_le_one hγpos).2
    rw [Real.sqrt_le_iff]
    constructor
    · exact hγpos.le
    · nlinarith [hl]
  have hcheb : |cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)| ≤ 1 := by
    set y := Real.sqrt (1 - lam) / ylcGamma 3 delta with hydef
    rw [cheb_three, abs_le]
    constructor
    · have h1 : -1 ≤ 4 * y ^ 3 - 3 * y := by
        have hsq : 0 ≤ (2 * y - 1) ^ 2 := sq_nonneg _
        have hfac : 1 + (4 * y ^ 3 - 3 * y) = (y + 1) * (2 * y - 1) ^ 2 := by ring
        have hmul : 0 ≤ (y + 1) * (2 * y - 1) ^ 2 := by
          apply mul_nonneg
          · linarith [hy0]
          · exact hsq
        nlinarith [hmul, hfac]
      exact h1
    · have h1 : 4 * y ^ 3 - 3 * y ≤ 1 := by
        have hsq : 0 ≤ (2 * y + 1) ^ 2 := sq_nonneg _
        have hfac : 1 - (4 * y ^ 3 - 3 * y) = (1 - y) * (2 * y + 1) ^ 2 := by ring
        have hmul : 0 ≤ (1 - y) * (2 * y + 1) ^ 2 := by
          apply mul_nonneg
          · linarith [hy1]
          · exact hsq
        nlinarith [hmul, hfac]
      exact h1
  have hsq : (delta * cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)) ^ 2 ≤ delta ^ 2 := by
    have h1 : |delta * cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)| ≤ delta := by
      rw [abs_mul, abs_of_pos hd]
      simpa using mul_le_mul_of_nonneg_left hcheb (le_of_lt hd)
    have h2 : (delta * cheb 3 (Real.sqrt (1 - lam) / ylcGamma 3 delta)) ^ 2 ≤ delta ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (le_of_lt hd)).mpr h1
    nlinarith [h2]
  nlinarith [hsq]

private theorem prepAccessCount_append (x y : List FixedPointAccess) :
    prepAccessCount (x ++ y) = prepAccessCount x + prepAccessCount y := by
  induction x with
  | nil => simp [prepAccessCount]
  | cons a t ih => cases a <;> simp [prepAccessCount, ih] <;> ring

private theorem queryAccessCount_append (x y : List FixedPointAccess) :
    queryAccessCount (x ++ y) = queryAccessCount x + queryAccessCount y := by
  induction x with
  | nil => simp [queryAccessCount]
  | cons a t ih => cases a <;> simp [queryAccessCount, ih] <;> ring

private theorem phaseAccessCount_append (x y : List FixedPointAccess) :
    phaseAccessCount (x ++ y) = phaseAccessCount x + phaseAccessCount y := by
  induction x with
  | nil => simp [phaseAccessCount]
  | cons a t ih => cases a <;> simp [phaseAccessCount, ih] <;> ring

private theorem phaseBitCount_append (x y : List FixedPointAccess) :
    phaseBitCount (x ++ y) = phaseBitCount x + phaseBitCount y := by
  induction x with
  | nil => simp [phaseBitCount]
  | cons a t ih => cases a <;> simp [phaseBitCount, ih] <;> ring

private theorem count_range {α : Type} (count : List α → ℕ) (hc0 : count [] = 0)
    (hadd : ∀ x y, count (x ++ y) = count x + count y)
    (f : ℕ → List α) (l c : ℕ) (h : ∀ i, count (f i) = c) :
    count (List.flatMap f (List.range l)) = c * l := by
  induction l with
  | zero => simp [hc0]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, hadd, ih]
      simp [h]
      ring

theorem prepAccessCount_word (l : ℕ) (delta : ℝ) (bits : ℕ) :
    prepAccessCount (fixedPointAccessWord l delta bits) = 2 * l := by
  rw [fixedPointAccessWord]
  exact count_range prepAccessCount (by simp [prepAccessCount]) prepAccessCount_append
    (fun i => iterateAccesses l delta bits i) l (2) (by
      intro i
      simp [iterateAccesses, prepAccessCount])

theorem queryAccessCount_word (l : ℕ) (delta : ℝ) (bits : ℕ) :
    queryAccessCount (fixedPointAccessWord l delta bits) = 2 * l := by
  rw [fixedPointAccessWord]
  exact count_range queryAccessCount (by simp [queryAccessCount]) queryAccessCount_append
    (fun i => iterateAccesses l delta bits i) l (2) (by
      intro i
      simp [iterateAccesses, queryAccessCount])

theorem phaseAccessCount_word (l : ℕ) (delta : ℝ) (bits : ℕ) :
    phaseAccessCount (fixedPointAccessWord l delta bits) = 2 * l := by
  rw [fixedPointAccessWord]
  exact count_range phaseAccessCount (by simp [phaseAccessCount]) phaseAccessCount_append
    (fun i => iterateAccesses l delta bits i) l (2) (by
      intro i
      simp [iterateAccesses, phaseAccessCount])

theorem phaseBitCount_word (l : ℕ) (delta : ℝ) (bits : ℕ) :
    phaseBitCount (fixedPointAccessWord l delta bits) = 2 * l * bits := by
  rw [fixedPointAccessWord]
  have h := count_range phaseBitCount (by simp [phaseBitCount]) phaseBitCount_append
    (fun i => iterateAccesses l delta bits i) l (2 * bits) (by
      intro i
      have hb : phaseBitCount (iterateAccesses l delta bits i) = bits + bits := by
        simp [iterateAccesses, phaseBitCount]
      rw [hb]
      ring)
  rwa [show (2 * bits) * l = 2 * l * bits by ring] at h

private theorem accessWordMatrix_append (lam : ℝ) (x y : List FixedPointAccess) :
    accessWordMatrix lam (x ++ y) = accessWordMatrix lam y * accessWordMatrix lam x := by
  induction x with
  | nil => simp [accessWordMatrix]
  | cons a t ih =>
      rw [List.cons_append, accessWordMatrix, ih]
      ac_rfl

private theorem accessWordMatrix_flatMap (lam : ℝ) (f : ℕ → List FixedPointAccess) (l : ℕ) :
    accessWordMatrix lam (List.flatMap f (List.range l)) =
      ((List.range l).map (fun i => accessWordMatrix lam (f i))).reverse.prod := by
  induction l with
  | zero => simp [accessWordMatrix]
  | succ n ih =>
      simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      rw [accessWordMatrix_append, ih]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [List.reverse_append, List.prod_append]
      simp only [List.nil_append, List.reverse_cons, List.reverse_nil, List.prod_cons,
        List.prod_nil, mul_one]

theorem iterateAccessMatrix (lam : ℝ) (l : ℕ) (delta : ℝ) (bits : ℕ) (i : ℕ) :
    accessWordMatrix lam (iterateAccesses l delta bits i) = publicIterate l delta lam i := by
  simp only [iterateAccesses, accessWordMatrix, FixedPointAccess.matrix]
  rw [publicIterate, groverIterate]
  simp

theorem accessWord_realizes_publicWord (l : ℕ) (delta lam : ℝ) (bits : ℕ) :
    accessWordMatrix lam (fixedPointAccessWord l delta bits) = publicWord l delta lam := by
  rw [fixedPointAccessWord, accessWordMatrix_flatMap]
  have hmap : (List.range l).map (fun i => accessWordMatrix lam (iterateAccesses l delta bits i))
      = (List.range l).map (fun i => publicIterate l delta lam i) := by
    apply List.map_congr_left
    intro i hi
    exact iterateAccessMatrix lam l delta bits i
  rw [hmap]
  rfl

theorem dyadicAngle_error (bits : ℕ) (angle : ℝ) :
    |angle - dyadicAngle bits angle| ≤ Real.pi / (2:ℝ) ^ bits := by
  set c : ℝ := angle * (2:ℝ) ^ bits / (2 * Real.pi) + 1 / 2 with hc
  have h1 : (↑(Int.floor c) : ℝ) ≤ c := Int.floor_le c
  have h2 : c < (↑(Int.floor c) : ℝ) + 1 := Int.lt_floor_add_one c
  have hmid : -(1 / 2) ≤ angle * (2:ℝ) ^ bits / (2 * Real.pi) - (↑(Int.floor c) : ℝ) ∧
      angle * (2:ℝ) ^ bits / (2 * Real.pi) - (↑(Int.floor c) : ℝ) ≤ 1 / 2 := by
    constructor <;> linarith
  have hpow : 0 < (2:ℝ) ^ bits := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp : dyadicAngle bits angle =
      2 * Real.pi * (↑(Int.floor c) : ℝ) / (2:ℝ) ^ bits := by
    simp [dyadicAngle, hc]
  rw [hexp]
  have hmain : angle - 2 * Real.pi * (↑(Int.floor c) : ℝ) / (2:ℝ) ^ bits
      = 2 * Real.pi * (angle * (2:ℝ) ^ bits / (2 * Real.pi) - (↑(Int.floor c) : ℝ)) /
          (2:ℝ) ^ bits := by
    field_simp
  rw [hmain, abs_div, abs_mul, abs_of_pos hpow]
  have hA : |2 * Real.pi| = 2 * Real.pi := by simp [abs_mul, abs_of_pos hpi]
  rw [hA]
  rw [(div_le_iff₀ hpow)]
  have hkey : (Real.pi / (2:ℝ) ^ bits) * (2:ℝ) ^ bits = Real.pi := by
    field_simp
  rw [hkey]
  have habs : |angle * (2:ℝ) ^ bits / (2 * Real.pi) - (↑(Int.floor c) : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    exact ⟨hmid.1, hmid.2⟩
  have hmul : 2 * Real.pi *
      |angle * (2:ℝ) ^ bits / (2 * Real.pi) - (↑(Int.floor c) : ℝ)| ≤ 2 * Real.pi * (1 / 2) :=
    mul_le_mul_of_nonneg_left habs (by linarith [hpi])
  linarith

private theorem prod_offdiag_zero :
    ∀ (xs : List (Matrix (Fin 2) (Fin 2) ℂ)),
      (∀ X ∈ xs, X 1 0 = 0) → (xs.prod) 1 0 = 0 := by
  intro xs
  induction xs with
  | nil => intro h; simp
  | cons X t ih =>
      intro h
      rw [List.prod_cons, Matrix.mul_apply, Fin.sum_univ_two]
      have hX : X 1 0 = 0 := h X (by simp)
      have ht : (t.prod) 1 0 = 0 := ih (fun Y hY => h Y (by simp [hY]))
      rw [hX, ht]
      simp

theorem groverIterate_zero_offdiag (alpha beta : ℝ) :
    groverIterate 0 alpha beta 1 0 = 0 := by
  have hss := stateReflection_entry 0 alpha (by norm_num) (by norm_num)
  rw [groverIterate, hss, Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [targetReflection, Real.sqrt_zero, Real.sqrt_one]

theorem ylcWordMatrix_zero_offdiag (l : ℕ) (delta : ℝ) :
    (ylcWordMatrix l delta 0) 1 0 = 0 := by
  have hgrover : ∀ (alpha beta : ℝ), groverIterate 0 alpha beta 1 0 = 0 :=
    fun alpha beta => groverIterate_zero_offdiag alpha beta
  unfold ylcWordMatrix
  apply prod_offdiag_zero
  intro X hX
  rw [List.mem_reverse] at hX
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
  exact hgrover _ _

theorem lcu_success_prob_eq_word {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    lcuSuccessProb j₀ l delta lam = publicSuccessProb l delta lam := by
  unfold lcuSuccessProb lcuSelectOperator lcuPrepareState
  exact clause3_fiber_success_probability j₀ l delta lam

theorem lcu_conditional_output_on_target_ray {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta lam : ℝ) :
    ∃ c : ℂ, lcuConditionalOutput j₀ l delta lam = c • fiberTarget j₀ := by
  refine ⟨(Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
      (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam) /
        (‖Qatlib.Foundations.PureStateMath.Inner (fiberTarget j₀)
          (lcuSelectOperator j₀ l delta lam *ᵥ lcuPrepareState j₀ lam)‖ : ℂ)), ?_⟩
  rfl

theorem lcu_zero_good_mass_fails {J : Type} [Fintype J] [DecidableEq J]
    (j₀ : J) (l : ℕ) (delta : ℝ) :
    lcuSuccessProb j₀ l delta 0 = 0 := by
  rw [lcu_success_prob_eq_word]
  have hamp0 : publicSuccessAmplitude l delta 0 = 0 := by
    unfold publicSuccessAmplitude
    rw [inner_ylcTargetVec]
    have hamp : ampState 0 = fun i => if i = 0 then (1:ℂ) else 0 := by
      funext i
      by_cases hi : i = 0 <;> simp [ampState, hi]
    rw [hamp]
    have hprod : (publicWord l delta 0) 1 0 = 0 := by
      rw [publicWord_eq]
      exact ylcWordMatrix_zero_offdiag l delta
    have hzero : (publicWord l delta 0 *ᵥ (fun i => if i = 0 then (1:ℂ) else 0)) 1 = 0 := by
      simp [Matrix.mulVec, hprod]
    rw [hzero]
  rw [publicSuccessProb, hamp0]
  simp

end Qatlib.Papers.FixedPtSearch14.FixedPoint
