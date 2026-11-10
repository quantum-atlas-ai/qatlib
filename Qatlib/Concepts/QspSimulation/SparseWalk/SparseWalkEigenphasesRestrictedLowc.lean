/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.SparseWalk.SparseWalkEigenphasesRestrictedStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.QspSimulation.SparseWalk

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

section Aux

variable {W : Type} [Fintype W] [DecidableEq W]

private theorem lcStarDot_self_eq (u : W → ℂ) :
    star u ⬝ᵥ u = ((∑ j, ‖u j‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star u ⬝ᵥ u = Qatlib.Foundations.PureStateMath.Inner u u from rfl, Qatlib.Foundations.PureStateMath.inner_self,
    Complex.ofReal_sum]

private theorem lcStarDot_eq_zero (f : W → ℂ) (h : star f ⬝ᵥ f = 0) : f = 0 := by
  rw [lcStarDot_self_eq] at h
  have hsum : ∑ j, ‖f j‖ ^ 2 = 0 := by
    have h0 : ((∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := h
    exact Complex.ofReal_injective h0
  funext j
  have hj : ‖f j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2).mp hsum j
      (Finset.mem_univ j)
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hj)

end Aux

theorem sparseWalkEigenphasesRestricted : SparseWalkEigenphasesRestricted := by
  intro I W _ _ _ _ H c hc hnorm L R S hL hR hLR hSu hSd hS2 hSL ψ hψ ev hev
  have hLd : L.conjTranspose * L = 1 := hL
  have hRd : R.conjTranspose * R = 1 := hR
  set u : W → ℂ := L *ᵥ ψ with hu
  set v : W → ℂ := R *ᵥ ψ with hv
  set s : ℝ := c * ev with hsdef

  have hψdot : star ψ ⬝ᵥ ψ = 1 := by
    rw [lcStarDot_self_eq, show (∑ i, ‖ψ i‖ ^ 2 : ℝ) = 1 from hψ, Complex.ofReal_one]
  have hinner : star u ⬝ᵥ v = (s : ℂ) := by
    rw [hu, hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hLR, Matrix.smul_mulVec, hev, dotProduct_smul, dotProduct_smul,
      smul_smul, hψdot]
    rw [show ((c : ℂ) * (ev : ℂ)) = ((c * ev : ℝ) : ℂ) from by
      rw [← Complex.ofReal_mul]]
    simp only [smul_eq_mul, mul_one]
    rfl
  have hinner' : star v ⬝ᵥ u = (s : ℂ) := by
    rw [Matrix.star_dotProduct, hinner]
    exact Complex.conj_ofReal s
  have hu1 : star u ⬝ᵥ u = 1 := by
    rw [hu, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hLd, Matrix.one_mulVec, hψdot]
  have hv1 : star v ⬝ᵥ v = 1 := by
    rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hRd, Matrix.one_mulVec, hψdot]

  have hquad : star (u - (s : ℂ) • v) ⬝ᵥ (u - (s : ℂ) • v) = ((1 - s * s : ℝ) : ℂ) := by
    rw [show star (u - (s : ℂ) • v) = star u - (s : ℂ) • star v from by
        simp [star_sub, star_smul]]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      hu1, hv1, hinner, hinner']
    simp only [smul_eq_mul, mul_one]
    rw [show ((s : ℂ) * (s : ℂ)) = ((s * s : ℝ) : ℂ) from by
        rw [← Complex.ofReal_mul],
      show ((1 - s * s : ℝ) : ℂ) = ((1 : ℝ) : ℂ) - ((s * s : ℝ) : ℂ) from by
        rw [Complex.ofReal_sub, Complex.ofReal_one]]
    push_cast
    ring
  have hs2le : s * s ≤ 1 := by
    have hnn : (0 : ℝ) ≤ (star (u - (s : ℂ) • v) ⬝ᵥ (u - (s : ℂ) • v)).re := by
      rw [lcStarDot_self_eq]
      exact Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) 2
    rw [hquad, Complex.ofReal_re] at hnn
    linarith

  set M : Matrix W W ℂ := ((2 : ℂ) • (L * L.conjTranspose)) - 1 with hMdef
  set V : Matrix W W ℂ := Complex.I • S * M with hVdef
  have hP2 : (L * L.conjTranspose) * (L * L.conjTranspose) = L * L.conjTranspose := by
    rw [Matrix.mul_assoc L L.conjTranspose (L * L.conjTranspose),
      ← Matrix.mul_assoc L.conjTranspose L L.conjTranspose, hLd, Matrix.one_mul]
  have hMself : M.conjTranspose = M := by
    rw [hMdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one,
      show star (2 : ℂ) = (2 : ℂ) from by
        rw [show star (2 : ℂ) = (starRingEnd ℂ) (2 : ℂ) from rfl, Complex.conj_ofNat]]
  have hMM : M * M = 1 := by
    have e1 : ((2 : ℂ) • (L * L.conjTranspose)) * ((2 : ℂ) • (L * L.conjTranspose))
        = ((4 : ℂ)) • ((L * L.conjTranspose) * (L * L.conjTranspose)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        show ((2 : ℂ) * 2) = 4 from by norm_num]
    have h2 : ((4 : ℂ)) • (L * L.conjTranspose)
        = ((2 : ℂ)) • (L * L.conjTranspose) + ((2 : ℂ)) • (L * L.conjTranspose) := by
      rw [← add_smul]
      norm_num
    rw [hMdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, e1,
      hP2, h2]
    module
  have hVU : V ∈ Matrix.unitaryGroup W ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, hVdef, Matrix.smul_mul, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hMself, hSd, Complex.star_def,
      Complex.conj_I, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show Complex.I * -Complex.I = 1 from by rw [mul_neg, Complex.I_mul_I, neg_neg],
      one_smul, Matrix.mul_assoc S M (M * S), ← Matrix.mul_assoc M M S, hMM,
      Matrix.one_mul, hS2]
  have hML : M * L = L := by
    rw [hMdef, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_assoc L L.conjTranspose L, hLd, Matrix.mul_one]
    module
  have hVL : V *ᵥ u = Complex.I • v := by
    rw [hVdef, hu, Matrix.mulVec_mulVec,
      show (Complex.I • S * M) * L = Complex.I • R from by
        rw [Matrix.mul_assoc (Complex.I • S) M L, hML, Matrix.smul_mul, hSL],
      Matrix.smul_mulVec]
  have hMR : M * R = ((2 * c : ℝ) : ℂ) • (L * H) - R := by
    rw [hMdef, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_assoc L L.conjTranspose R, hLR, Matrix.mul_smul, smul_smul,
      show ((2 : ℂ) * (c : ℂ)) = ((2 * c : ℝ) : ℂ) from by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_mul]]
  have hSLR : S * R = L := by
    rw [← hSL, ← Matrix.mul_assoc, hS2, Matrix.one_mul]
  have hVR : V *ᵥ v = Complex.I • (((2 * s : ℝ) : ℂ) • v - u) := by
    rw [hVdef, hv, Matrix.mulVec_mulVec,
      show (Complex.I • S * M) * R
          = Complex.I • (((2 * c : ℝ) : ℂ) • (R * H) - L) from by
        rw [Matrix.mul_assoc (Complex.I • S) M R, hMR, Matrix.smul_mul, Matrix.mul_sub,
          Matrix.mul_smul, ← Matrix.mul_assoc, hSL, hSLR],
      Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, hev, Matrix.mulVec_smul, smul_smul,
      show ((2 * c : ℝ) : ℂ) * (ev : ℂ) = ((2 * s : ℝ) : ℂ) from by
        rw [hsdef]; push_cast; ring]
  by_cases hsq : s * s < 1
  · have h1s : 0 < 1 - s * s := by linarith
    set rw2 : ℝ := Real.sqrt (1 - s * s) with hrw2def
    have hrw2pos : 0 < rw2 := Real.sqrt_pos_of_pos h1s
    have hrw2sq : rw2 * rw2 = 1 - s * s := Real.mul_self_sqrt (le_of_lt h1s)
    set eP : ℂ := (rw2 : ℂ) - (s : ℂ) * Complex.I with hePdef
    set eM : ℂ := (rw2 : ℂ) + (s : ℂ) * Complex.I with heMdef
    set zP : ℂ := -Complex.I * eM with hzPdef
    set zM : ℂ := Complex.I * eP with hzMdef
    set N : ℝ := Real.sqrt 2 * rw2 with hNdef
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hrw2c2 : ((rw2 : ℂ)) * ((rw2 : ℂ)) = ((1 - s * s : ℝ) : ℂ) := by
      rw [show ((rw2 : ℂ)) * ((rw2 : ℂ)) = ((rw2 * rw2 : ℝ) : ℂ) from by
          rw [← Complex.ofReal_mul], hrw2sq]
    have hssc2 : ((s : ℂ)) * ((s : ℂ)) = ((s * s : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    have hdotsmul : ∀ (a b : ℂ) (x y : W → ℂ), (a • x) ⬝ᵥ (b • y) = (a * b) * (x ⬝ᵥ y) := by
      intro a b x y
      rw [dotProduct_smul, smul_dotProduct, smul_smul, smul_eq_mul]
      ring
    have hac : |s| ≤ 1 := by
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    have hzPeq : zP = (s : ℂ) - Complex.I * (rw2 : ℂ) := by
      rw [hzPdef, heMdef, neg_mul, mul_add,
        show Complex.I * ((s : ℂ) * Complex.I) = -((s : ℂ)) from by
          rw [← mul_assoc, mul_comm Complex.I (s : ℂ), mul_assoc, hII, mul_neg_one]]
      ring
    have hzMeq : zM = (s : ℂ) + Complex.I * (rw2 : ℂ) := by
      rw [hzMdef, hePdef, mul_sub,
        show Complex.I * ((s : ℂ) * Complex.I) = -((s : ℂ)) from by
          rw [← mul_assoc, mul_comm Complex.I (s : ℂ), mul_assoc, hII, mul_neg_one]]
      ring
    have hlzP : Complex.I * zP = eM := by
      rw [hzPeq, mul_sub, ← mul_assoc, hII]
      ring
    have hlzM : Complex.I * zM = -eP := by
      rw [hzMeq, mul_add, ← mul_assoc, hII]
      ring
    have hzsum : zP + zM = 2 * (s : ℂ) := by
      rw [hzPeq, hzMeq]
      ring
    have hstarzP : star zP = zM := by
      rw [hzPeq, hzMeq, show star ((s : ℂ) - Complex.I * (rw2 : ℂ))
            = (starRingEnd ℂ) ((s : ℂ) - Complex.I * (rw2 : ℂ)) from rfl,
        map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
        Complex.conj_ofReal]
      ring
    have hstarzM : star zM = zP := by
      rw [hzPeq, hzMeq, show star ((s : ℂ) + Complex.I * (rw2 : ℂ))
            = (starRingEnd ℂ) ((s : ℂ) + Complex.I * (rw2 : ℂ)) from rfl,
        map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
        Complex.conj_ofReal]
      ring
    have hzz : zP * zM = 1 := by
      rw [hzPeq, hzMeq]
      push_cast at hrw2c2 hssc2
      linear_combination hrw2c2 + hssc2 -
        ((rw2 : ℂ) * (rw2 : ℂ)) * hII
    have hzPchar : zP * zP = 2 * (s : ℂ) * zP - 1 := by
      linear_combination zP * hzsum - hzz
    have hzMchar : zM * zM = 2 * (s : ℂ) * zM - 1 := by
      linear_combination zM * hzsum - hzz
    have hexpM : Complex.exp (Complex.I * ((Real.arcsin s : ℝ) : ℂ)) = eM := by
      rw [show Complex.I * ((Real.arcsin s : ℝ) : ℂ)
          = ((Real.arcsin s : ℝ) : ℂ) * Complex.I from mul_comm _ _,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_arcsin, Real.sin_arcsin (abs_le.mp hac).1 (abs_le.mp hac).2, heMdef, hrw2def, pow_two]
    have hexpP : Complex.exp (Complex.I * ((-Real.arcsin s : ℝ) : ℂ)) = eP := by
      rw [show Complex.I * ((-Real.arcsin s : ℝ) : ℂ)
          = ((-Real.arcsin s : ℝ) : ℂ) * Complex.I from mul_comm _ _,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Real.cos_arcsin, Real.sin_arcsin (abs_le.mp hac).1 (abs_le.mp hac).2, hePdef, hrw2def, pow_two,
        Complex.ofReal_neg]
      ring

    have hkeyP : (Complex.I * zP) * zP = ((2 * s : ℝ) : ℂ) * (Complex.I * zP) - Complex.I := by
      push_cast
      linear_combination Complex.I * hzPchar
    have hkeyM : (Complex.I * zM) * zM = ((2 * s : ℝ) : ℂ) * (Complex.I * zM) - Complex.I := by
      push_cast
      linear_combination Complex.I * hzMchar
    have hVIexpand : Complex.I • (((2 * s : ℝ) : ℂ) • v - u)
        = (Complex.I * ((2 * s : ℝ) : ℂ)) • v - Complex.I • u := by
      rw [smul_sub, smul_smul]
    have hVfP : V *ᵥ (u - zP • v) = eM • (u - zP • v) := by
      have hL : V *ᵥ (u - zP • v)
          = (Complex.I * zP) • u + (Complex.I - ((2 * s : ℝ) : ℂ) * (Complex.I * zP)) • v := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hVL, hVR, hVIexpand]
        module
      have hR : eM • (u - zP • v)
          = (Complex.I * zP) • u - ((Complex.I * zP) * zP) • v := by
        rw [hlzP, smul_sub, smul_smul]
      rw [hL, hR, hkeyP]
      module
    have hVfM : V *ᵥ (u - zM • v) = -eP • (u - zM • v) := by
      have hL : V *ᵥ (u - zM • v)
          = (Complex.I * zM) • u + (Complex.I - ((2 * s : ℝ) : ℂ) * (Complex.I * zM)) • v := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hVL, hVR, hVIexpand]
        module
      have hR : -eP • (u - zM • v)
          = (Complex.I * zM) • u - ((Complex.I * zM) * zM) • v := by
        rw [show -eP = Complex.I * zM from hlzM.symm, smul_sub, smul_smul]
      rw [hL, hR, hkeyM]
      module

    have h2ss : ((2 - 2 * s * s : ℝ) : ℂ) = (1 : ℂ) - (s : ℂ) * (zP + zM) + 1 * 1 := by
      rw [hzsum]
      push_cast
      ring
    have hnormP : star (u - zP • v) ⬝ᵥ (u - zP • v) = ((2 - 2 * s * s : ℝ) : ℂ) := by
      simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, hstarzP, hu1, hv1, hinner, hinner', smul_eq_mul]
      linear_combination -h2ss + hzz
    have hnormM : star (u - zM • v) ⬝ᵥ (u - zM • v) = ((2 - 2 * s * s : ℝ) : ℂ) := by
      simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, hstarzM, hu1, hv1, hinner, hinner', smul_eq_mul]
      linear_combination -h2ss + hzz
    have horth : star (u - zP • v) ⬝ᵥ (u - zM • v) = 0 := by
      simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, hstarzP, hu1, hv1, hinner, hinner', smul_eq_mul]
      linear_combination hzMchar

    have hNpos : 0 < N := by
      rw [hNdef]
      positivity
    have hN2 : N * N = 2 * (1 - s * s) := by
      rw [hNdef, show (Real.sqrt 2 * rw2) * (Real.sqrt 2 * rw2)
          = (Real.sqrt 2 * Real.sqrt 2) * (rw2 * rw2) from by ring,
        Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hrw2sq]
    have hNinv : ((N : ℝ) : ℂ)⁻¹ * (((N : ℝ) : ℂ)⁻¹) * ((2 - 2 * s * s : ℝ) : ℂ) = 1 := by
      have hNc : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hNpos)
      have hNc2 : (N : ℂ) * (N : ℂ) = ((2 - 2 * s * s : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hN2]
        congr 1
        ring
      rw [← hNc2]
      field_simp

    have hbal0 : eP * zP + eM * zM = 0 := by
      rw [hzPdef, hzMdef]
      ring
    have hbalP : eP + eM = 2 * (rw2 : ℂ) := by
      rw [hePdef, heMdef]
      ring
    have hcoef1 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * (((N : ℝ) : ℂ)⁻¹ * (2 * (rw2 : ℂ))) = 1 := by
      have hr : (1 / Real.sqrt 2 : ℝ) * (N⁻¹ * (2 * rw2)) = 1 := by
        rw [hNdef, one_div]
        have hrne : rw2 ≠ 0 := ne_of_gt hrw2pos
        have hrtne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        field_simp
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [show (2 : ℂ) * ((rw2 : ℂ)) = ((2 * rw2 : ℝ) : ℂ) from by
          rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, ← Complex.ofReal_mul],
        ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hr, Complex.ofReal_one]
    have hbal : u = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
        (eP • (((N : ℝ) : ℂ)⁻¹ • (u - zP • v))
          + eM • (((N : ℝ) : ℂ)⁻¹ • (u - zM • v))) := by
      have h1 : eP • (((N : ℝ) : ℂ)⁻¹ • (u - zP • v))
          + eM • (((N : ℝ) : ℂ)⁻¹ • (u - zM • v))
          = (((N : ℝ) : ℂ)⁻¹ * (eP + eM)) • u
            - (((N : ℝ) : ℂ)⁻¹ * (eP * zP + eM * zM)) • v := by
        module
      rw [h1, hbal0, mul_zero, zero_smul, sub_zero, hbalP, smul_smul, hcoef1, one_smul]

    have hsmP : (fun j => ((N : ℝ) : ℂ)⁻¹ * (u - zP • v) j)
        = ((N : ℝ) : ℂ)⁻¹ • (u - zP • v) := by
      funext j; rw [Pi.smul_apply, smul_eq_mul]
    have hsmM : (fun j => ((N : ℝ) : ℂ)⁻¹ * (u - zM • v) j)
        = ((N : ℝ) : ℂ)⁻¹ • (u - zM • v) := by
      funext j; rw [Pi.smul_apply, smul_eq_mul]
    have hstarc : star (((N : ℝ) : ℂ)⁻¹) = ((N : ℝ) : ℂ)⁻¹ := by
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have hdP : star (((N : ℝ) : ℂ)⁻¹ • (u - zP • v)) ⬝ᵥ (((N : ℝ) : ℂ)⁻¹ • (u - zP • v))
        = 1 := by
      rw [star_smul, hdotsmul, hstarc, hnormP, hNinv]
    have hdM : star (((N : ℝ) : ℂ)⁻¹ • (u - zM • v)) ⬝ᵥ (((N : ℝ) : ℂ)⁻¹ • (u - zM • v))
        = 1 := by
      rw [star_smul, hdotsmul, hstarc, hnormM, hNinv]
    have hdOrth : star (((N : ℝ) : ℂ)⁻¹ • (u - zP • v)) ⬝ᵥ (((N : ℝ) : ℂ)⁻¹ • (u - zM • v))
        = 0 := by
      rw [star_smul, hdotsmul, hstarc, horth, mul_zero]
    refine ⟨fun j => ((N : ℝ) : ℂ)⁻¹ * (u - zP • v) j,
      fun j => ((N : ℝ) : ℂ)⁻¹ * (u - zM • v) j,
      -Real.arcsin s, Real.arcsin s, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsmP]
      have h2 := lcStarDot_self_eq (((N : ℝ) : ℂ)⁻¹ • (u - zP • v))
      rw [hdP] at h2
      exact Complex.ofReal_eq_one.mp h2.symm
    · rw [hsmM]
      have h2 := lcStarDot_self_eq (((N : ℝ) : ℂ)⁻¹ • (u - zM • v))
      rw [hdM] at h2
      exact Complex.ofReal_eq_one.mp h2.symm
    · intro _
      rw [hsmP, hsmM]
      exact hdOrth
    · refine ⟨V, hVU, by rw [hVdef, hMdef]; simp only [two_smul ℂ, two_smul ℕ], ?_, ?_⟩
      · rw [hsmP, Matrix.mulVec_smul, hVfP, hexpM]
        rw [show ((N : ℝ) : ℂ)⁻¹ • (eM • (u - zP • v))
            = eM • (((N : ℝ) : ℂ)⁻¹ • (u - zP • v)) from smul_comm _ _ _]
      · rw [hsmM, Matrix.mulVec_smul, hVfM,
          show -((Real.arcsin s : ℝ) : ℂ) = ((-Real.arcsin s : ℝ) : ℂ) from by
            rw [Complex.ofReal_neg],
          hexpP]
        module
    · rw [hsmP, hsmM, hexpP, hexpM]
      exact hbal
  · have hs2 : s * s = 1 := le_antisymm hs2le (le_of_not_gt hsq)
    have hq0 : star (u - (s : ℂ) • v) ⬝ᵥ (u - (s : ℂ) • v) = 0 := by
      rw [hquad, show (1 - s * s : ℝ) = 0 from by linarith, Complex.ofReal_zero]
    have huv0 : u - (s : ℂ) • v = 0 := lcStarDot_eq_zero _ hq0
    have huv : v = (s : ℂ) • u := by
      have h1 : (s : ℂ) • u = ((s * s : ℝ) : ℂ) • v := by
        rw [show u = (s : ℂ) • v from sub_eq_zero.mp huv0, smul_smul,
          show ((s : ℂ)) * ((s : ℂ)) = ((s * s : ℝ) : ℂ) from by
            rw [← Complex.ofReal_mul]]
      rw [hs2, Complex.ofReal_one, one_smul] at h1
      exact h1.symm
    have hpm : s = 1 ∨ s = -1 := sq_eq_one_iff.mp (by rw [pow_two]; exact hs2)
    rcases hpm with hs1 | hs1
    · rw [hs1] at huv ⊢
      have hexpI : Complex.exp (Complex.I * ((Real.arcsin (1 : ℝ) : ℂ))) = Complex.I := by
        rw [Real.arcsin_one,
          show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 * Complex.I from by
            push_cast; ring,
          Complex.exp_pi_div_two_mul_I]
      have hexpI' : -(Complex.exp (Complex.I * (-((Real.arcsin (1 : ℝ) : ℂ))))) = Complex.I := by
        rw [Real.arcsin_one,
          show Complex.I * (-((Real.pi / 2 : ℝ) : ℂ)) = -((Real.pi : ℂ) / 2 * Complex.I) from by
            push_cast; ring,
          Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
        simp
      have hunit : ∑ j, ‖u j‖ ^ 2 = 1 := by
        have h2 := lcStarDot_self_eq u
        rw [hu1] at h2
        exact Complex.ofReal_eq_one.mp h2.symm
      refine ⟨u, u, Real.pi / 4, -Real.pi / 4, hunit, hunit, ?_,
        ⟨V, hVU, by rw [hVdef, hMdef]; simp only [two_smul ℂ, two_smul ℕ], ?_, ?_⟩, ?_⟩
      · intro hlt
        simp at hlt
      · rw [hVL, huv, Complex.ofReal_one, one_smul, hexpI]
      · rw [hVL, huv, Complex.ofReal_one, one_smul, hexpI']
      · rw [← add_smul]
        have hexp : Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ))
            + Complex.exp (Complex.I * ((-Real.pi / 4 : ℝ) : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
          rw [show Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
              push_cast; ring,
            show Complex.I * ((-Real.pi / 4 : ℝ) : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
              push_cast; ring,
            Complex.exp_mul_I, Complex.exp_mul_I,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
            ← Complex.ofReal_sin,
            Real.cos_pi_div_four, Real.sin_pi_div_four,
            show (-Real.pi / 4 : ℝ) = -(Real.pi / 4) from by ring,
            Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
            Complex.ofReal_neg]
          have key : ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ)
              = ((Real.sqrt 2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_add,
              show Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 from by
                rw [show Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = 2 * (Real.sqrt 2 / 2) from by ring,
                  mul_div_cancel₀ _ two_ne_zero]]
          linear_combination key
        have hcoef2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
          rw [show ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)
              = ((1 / Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) from by
              rw [← Complex.ofReal_mul],
            one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))), Complex.ofReal_one]
        rw [hexp, smul_smul, hcoef2, one_smul]
    · rw [hs1] at huv ⊢
      have hexpI : Complex.exp (Complex.I * ((Real.arcsin (-1 : ℝ) : ℂ)))
          = Complex.I * ((-1 : ℝ) : ℂ) := by
        rw [Real.arcsin_neg_one, Complex.ofReal_neg,
          show Complex.I * ((-(Real.pi / 2 : ℝ) : ℂ)) = -((Real.pi : ℂ) / 2 * Complex.I) from by
            push_cast; ring,
          Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
        push_cast
        ring
      have hexpI' : -(Complex.exp (Complex.I * (-((Real.arcsin (-1 : ℝ) : ℂ)))))
          = Complex.I * ((-1 : ℝ) : ℂ) := by
        rw [Real.arcsin_neg_one, Complex.ofReal_neg,
          show Complex.I * (-((-(Real.pi / 2 : ℝ) : ℂ))) = (Real.pi : ℂ) / 2 * Complex.I from by
            push_cast; ring,
          Complex.exp_pi_div_two_mul_I]
        push_cast
        ring
      have hunit : ∑ j, ‖u j‖ ^ 2 = 1 := by
        have h2 := lcStarDot_self_eq u
        rw [hu1] at h2
        exact Complex.ofReal_eq_one.mp h2.symm
      refine ⟨u, u, Real.pi / 4, -Real.pi / 4, hunit, hunit, ?_,
        ⟨V, hVU, by rw [hVdef, hMdef]; simp only [two_smul ℂ, two_smul ℕ], ?_, ?_⟩, ?_⟩
      · intro hlt
        simp at hlt
      · rw [hVL, huv, hexpI]
        module
      · rw [hVL, huv, hexpI']
        module
      · rw [← add_smul]
        have hexp : Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ))
            + Complex.exp (Complex.I * ((-Real.pi / 4 : ℝ) : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) := by
          rw [show Complex.I * ((Real.pi / 4 : ℝ) : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
              push_cast; ring,
            show Complex.I * ((-Real.pi / 4 : ℝ) : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I from by
              push_cast; ring,
            Complex.exp_mul_I, Complex.exp_mul_I,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
            ← Complex.ofReal_sin,
            Real.cos_pi_div_four, Real.sin_pi_div_four,
            show (-Real.pi / 4 : ℝ) = -(Real.pi / 4) from by ring,
            Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
            Complex.ofReal_neg]
          have key : ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ)
              = ((Real.sqrt 2 : ℝ) : ℂ) := by
            rw [← Complex.ofReal_add,
              show Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 from by
                rw [show Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = 2 * (Real.sqrt 2 / 2) from by ring,
                  mul_div_cancel₀ _ two_ne_zero]]
          linear_combination key
        have hcoef2 : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 1 := by
          rw [show ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ)
              = ((1 / Real.sqrt 2 * Real.sqrt 2 : ℝ) : ℂ) from by
              rw [← Complex.ofReal_mul],
            one_div_mul_cancel (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))), Complex.ofReal_one]
        rw [hexp, smul_smul, hcoef2, one_smul]

end Qatlib.Concepts.QspSimulation.SparseWalk
