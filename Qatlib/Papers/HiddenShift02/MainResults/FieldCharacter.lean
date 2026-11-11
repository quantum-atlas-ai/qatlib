/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HiddenShift02.MainResults.FourierCore
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hidden shifts of finite-field characters

This module derives Fourier identities for multiplicative characters over finite fields and
computes the final amplitude `algorithmAmplitude` of the character hidden-shift procedure. The
theorem `source_theorem1` collects the preparation and conditional recovery probabilities, each
equal to 1 − 1/|F|, together with their product.

The development follows [VanDamHallgrenIp2006].

## Main statements

* `final_amplitude`: For a nontrivial multiplicative character and a primitive additive
  character, computes the final amplitude as the common Fourier factor times |F| − 1 at x = −s
  and times −1 elsewhere.
* `success_probability`: For a nontrivial multiplicative character and primitive additive
  character over a field of size at least two, the support-normalized squared amplitude at −s is
  1 − 1/|F|.
* `source_theorem1`: For a nontrivial multiplicative character and primitive additive character,
  both preparation and support-normalized recovery have probability 1 − 1/|F|, and their product
  is (1 − 1/|F|)².

## References

* [van Dam et al., 2006][VanDamHallgrenIp2006]
-/

set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.HiddenShift02.MainResults.FourierCore
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.FieldCharacter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A multiplicative character of the field vanishes exactly at zero. -/
theorem mulChar_eq_zero_iff (χ : MulChar F ℂ) (x : F) : χ x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact ((isUnit_iff_ne_zero.mpr hx).map χ.toMonoidHom).ne_zero h
  · intro h
    rw [h]
    exact χ.map_zero

/-- A multiplicative character has complex norm one at every nonzero field element. -/
theorem norm_mulChar_apply_eq_one (χ : MulChar F ℂ) {x : F} (hx : x ≠ 0) :
    ‖χ x‖ = 1 := by
  classical
  haveI : NeZero (Fintype.card Fˣ) := ⟨Fintype.card_ne_zero⟩
  have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
  have hmem : χ.toUnitHom hu.unit ∈ rootsOfUnity (Fintype.card Fˣ) ℂ :=
    χ.apply_mem_rootsOfUnity hu.unit
  have hval : (χ.toUnitHom hu.unit : ℂ) = χ x := by
    rw [MulChar.coe_toUnitHom, IsUnit.unit_spec]
  rw [← hval]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity hmem

/-- Complex conjugation of an additive character value equals the value of the inverse
character. -/
theorem conj_addChar_eq_inv (ψ : AddChar F ℂ) (a : F) : conj (ψ a) = ψ⁻¹ a := by
  have hR : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  exact AddChar.starComp_apply hR a

/-- Inverting the multiplicatively shifted inverse additive character gives the shifted original
character. -/
theorem inv_mulShift_inv (ψ : AddChar F ℂ) (a : F) :
    ((ψ⁻¹).mulShift a)⁻¹ = ψ.mulShift a := by
  ext x
  simp [AddChar.mulShift_apply, mul_neg]

/-- At a nonzero frequency multiplier `y`, the Fourier coefficient of `χ` is `χ⁻¹ y` times its
coefficient at `ψ` ([Theorem 1][VanDamHallgrenIp2006]). -/
theorem fourier_mulShift_char (χ : MulChar F ℂ) (ψ : AddChar F ℂ) {y : F}
    (hy : y ≠ 0) : fourier χ (ψ.mulShift y) = χ⁻¹ y * fourier χ ψ := by
  classical
  set u : Fˣ := hy.isUnit.unit with hu
  have huy : (u : F) = y := IsUnit.unit_spec _
  have hmul : ψ.mulShift y = ψ.mulShift (u : F) := by rw [huy]
  have hfg : fourier χ (ψ.mulShift (u : F)) =
      fourierScale F * gaussSum χ (ψ⁻¹.mulShift (u : F)) := by
    rw [fourier_apply, gaussSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, conj_addChar_eq_inv]
    ring
  have hfψ : fourier χ ψ = fourierScale F * gaussSum χ ψ⁻¹ := by
    rw [fourier_apply, gaussSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [conj_addChar_eq_inv]
    ring
  rw [hmul, hfg, gaussSum_mulShift_eq χ ψ⁻¹ u, hfψ]
  have hcoe : χ⁻¹ (u : F) = χ⁻¹ y := by rw [huy]
  rw [hcoe]
  ring

/-- The squared norm of the normalized Fourier coefficient of a nontrivial multiplicative
character at a primitive additive character is one ([Theorem 1][VanDamHallgrenIp2006]). -/
theorem fourier_char_normSq (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) : ‖fourier χ ψ‖ ^ 2 = 1 := by
  classical
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hscale : ‖fourierScale F‖ ^ 2 = ((Fintype.card F : ℝ))⁻¹ := by
    rw [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hqR.le]
  have hfψ : fourier χ ψ = fourierScale F * gaussSum χ ψ⁻¹ := by
    rw [fourier_apply, gaussSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [conj_addChar_eq_inv]
    ring
  have hψinv : (ψ⁻¹).IsPrimitive := by
    intro a ha h
    apply hψ ha
    have h' := congrArg (fun η : AddChar F ℂ => η⁻¹) h
    simpa [inv_mulShift_inv] using h'
  have hprod : gaussSum χ ψ⁻¹ * conj (gaussSum χ ψ⁻¹) = (Fintype.card F : ℂ) := by
    have hstar : conj (gaussSum χ ψ⁻¹) = gaussSum χ⁻¹ (ψ⁻¹)⁻¹ := star_gaussSum_eq χ ψ⁻¹
    rw [hstar, inv_inv]
    simpa using gaussSum_mul_gaussSum_eq_card (χ := χ) hχ (ψ := ψ⁻¹) hψinv
  have hgnorm : ‖gaussSum χ ψ⁻¹‖ ^ 2 = (Fintype.card F : ℝ) := by
    have hsq : ‖gaussSum χ ψ⁻¹‖ ^ 2
        = (gaussSum χ ψ⁻¹ * conj (gaussSum χ ψ⁻¹)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hsq, hprod]
    simp
  rw [hfψ, norm_mul, mul_pow, hscale, hgnorm]
  exact inv_mul_cancel₀ (ne_of_gt hqR)

/-- The final amplitude sum formed by Fourier transforming the shifted character, multiplying by
`χ`, and applying the scaled additive-character sum. -/
noncomputable def algorithmAmplitude (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (s x : F) : ℂ :=
  fourierScale F * ∑ y : F,
    (ψ.mulShift y) x * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y))

/-- For a nontrivial multiplicative character and a primitive additive character, computes the
final amplitude as the common Fourier factor times |F| − 1 at x = −s and times −1 elsewhere
([Theorem 1][VanDamHallgrenIp2006]). -/
theorem final_amplitude (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (s x : F) :
    algorithmAmplitude χ ψ s x = fourierScale F * fourier χ ψ *
      ((if x + s = 0 then (Fintype.card F : ℂ) else 0) - 1) := by
  classical
  unfold algorithmAmplitude
  have hstep : ∀ y : F,
      (ψ.mulShift y) x * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y))
        = fourier χ ψ *
            ((if y = 0 then (0 : ℂ) else 1) * ((ψ.mulShift y) x * (ψ.mulShift y) s)) := by
    intro y
    by_cases hy : y = 0
    · simp [hy, MulChar.map_zero]
    · have hshift := fourier_shift (fun z => χ z) s (ψ.mulShift y)
      rw [hshift, fourier_mulShift_char χ ψ hy]
      have hχy : χ y ≠ 0 := by
        intro h
        exact hy ((mulChar_eq_zero_iff χ y).mp h)
      rw [MulChar.inv_apply_eq_inv' χ y]
      simp only [hy, if_false, one_mul]
      field_simp
      try ring
  have hsum : (∑ y : F,
        ((if y = 0 then (0 : ℂ) else 1) * ((ψ.mulShift y) x * (ψ.mulShift y) s)))
      = ((if x + s = 0 then (Fintype.card F : ℂ) else 0) - 1) := by
    have hpt : ∀ y : F,
        (if y = 0 then (0 : ℂ) else 1) * ((ψ.mulShift y) x * (ψ.mulShift y) s)
          = (ψ.mulShift y) x * (ψ.mulShift y) s - (if y = 0 then (1 : ℂ) else 0) := by
      intro y
      by_cases hy : y = 0 <;> simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => hpt y), Finset.sum_sub_distrib]
    have hone : (∑ y : F, (if y = 0 then (1 : ℂ) else 0)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ 0) h
    rw [hone]
    congr 1
    have hprod : ∀ y : F, (ψ.mulShift y) x * (ψ.mulShift y) s = ψ (y * (x + s)) := by
      intro y
      rw [AddChar.mulShift_apply, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [Finset.sum_congr rfl (fun y _ => hprod y), AddChar.sum_mulShift (x + s) hψ]
    by_cases h : x + s = 0 <;> simp [h]
  calc fourierScale F * (∑ y : F,
        (ψ.mulShift y) x * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y)))
      = fourierScale F * (∑ y : F,
          fourier χ ψ *
            ((if y = 0 then (0 : ℂ) else 1) * ((ψ.mulShift y) x * (ψ.mulShift y) s))) := by
        rw [Finset.sum_congr rfl (fun y _ => hstep y)]
    _ = fourierScale F * (fourier χ ψ * (∑ y : F,
          ((if y = 0 then (0 : ℂ) else 1) * ((ψ.mulShift y) x * (ψ.mulShift y) s)))) := by
        rw [← Finset.mul_sum]
    _ = fourierScale F * fourier χ ψ *
          ((if x + s = 0 then (Fintype.card F : ℂ) else 0) - 1) := by
        rw [hsum]
        ring

/-- For a nontrivial multiplicative character and primitive additive character over a field of
size at least two, the support-normalized squared amplitude at −s is 1 − 1/|F| ([Theorem
1][VanDamHallgrenIp2006]). -/
theorem success_probability (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (hq : 2 ≤ Fintype.card F) (s : F) :
    ‖(((Real.sqrt ((Fintype.card F : ℝ) - 1) : ℝ)) : ℂ)⁻¹ *
        algorithmAmplitude χ ψ s (-s)‖ ^ 2
      = 1 - 1 / (Fintype.card F : ℝ) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq
    linarith
  have hq1 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hq
    linarith
  have hscale : ‖fourierScale F‖ ^ 2 = ((Fintype.card F : ℝ))⁻¹ := by
    rw [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hcard.le]
  have hif : (if -s + s = 0 then (Fintype.card F : ℂ) else 0) = (Fintype.card F : ℂ) := by
    simp
  have hcast : ((Fintype.card F : ℂ) - 1) = (((Fintype.card F : ℝ) - 1 : ℝ) : ℂ) := by
    push_cast
    ring
  have hnorm_real : ‖((((Fintype.card F : ℝ) - 1 : ℝ)) : ℂ)‖
      = (Fintype.card F : ℝ) - 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq1.le]
  have hamp : algorithmAmplitude χ ψ s (-s) =
      fourierScale F * fourier χ ψ * ((((Fintype.card F : ℝ) - 1 : ℝ)) : ℂ) := by
    rw [final_amplitude χ hχ ψ hψ, hif, hcast]
  have hA : ‖algorithmAmplitude χ ψ s (-s)‖ ^ 2
      = ((Fintype.card F : ℝ) - 1) ^ 2 / (Fintype.card F : ℝ) := by
    rw [hamp, norm_mul, norm_mul, mul_pow, mul_pow, hscale,
      fourier_char_normSq χ hχ ψ hψ, hnorm_real]
    ring
  have hsqrt : ‖((((Real.sqrt ((Fintype.card F : ℝ) - 1) : ℝ)) : ℂ))⁻¹‖ ^ 2
      = ((Fintype.card F : ℝ) - 1)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hq1.le]
  rw [norm_mul, mul_pow, hsqrt, hA]
  have hne : ((Fintype.card F : ℝ) - 1) ≠ 0 := ne_of_gt hq1
  have hqne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hcard
  field_simp
  try ring

/-- The support of the character shifted by `s` is the universal finite set with −s removed. -/
theorem shiftedChar_filter (χ : MulChar F ℂ) (s : F) :
    Finset.univ.filter (fun x : F => χ (x + s) ≠ 0) = Finset.univ.erase (-s) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hx
    refine ⟨?_, trivial⟩
    intro h
    apply hx
    simp [h, MulChar.map_zero]
  · intro hx hzero
    exact hx.1 ((add_eq_zero_iff_eq_neg).mp ((mulChar_eq_zero_iff χ (x + s)).mp hzero))

/-- The support fraction of the character shifted by `s` equals 1 − 1/|F| ([Theorem
1][VanDamHallgrenIp2006]). -/
theorem prep_probability (χ : MulChar F ℂ) (s : F) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun x : F => χ (x + s) ≠ 0)).card : ℝ) /
        (Fintype.card F : ℝ) = 1 - 1 / (Fintype.card F : ℝ) := by
  classical
  rw [shiftedChar_filter, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.mpr hq
  have hq1 : 1 ≤ Fintype.card F := hq
  rw [Nat.cast_sub hq1, Nat.cast_one]
  field_simp
  try ring

/-- For a nontrivial multiplicative character and primitive additive character, both preparation
and support-normalized recovery have probability 1 − 1/|F|, and their product is (1 −
1/|F|)² ([Theorem 1][VanDamHallgrenIp2006]). -/
theorem source_theorem1 (χ : MulChar F ℂ) (hχ : χ ≠ 1) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (hq : 2 ≤ Fintype.card F) (s : F) :
    ((Finset.univ.filter (fun x : F => χ (x + s) ≠ 0)).card : ℝ) /
        (Fintype.card F : ℝ) = 1 - 1 / (Fintype.card F : ℝ) ∧
      ‖(((Real.sqrt ((Fintype.card F : ℝ) - 1) : ℝ)) : ℂ)⁻¹ *
          algorithmAmplitude χ ψ s (-s)‖ ^ 2
        = 1 - 1 / (Fintype.card F : ℝ) ∧
      (1 - 1 / (Fintype.card F : ℝ)) * (1 - 1 / (Fintype.card F : ℝ))
        = (1 - 1 / (Fintype.card F : ℝ)) ^ 2 :=
  ⟨prep_probability χ s (by omega), success_probability χ hχ ψ hψ hq s, by ring⟩

end Qatlib.Papers.HiddenShift02.MainResults.FieldCharacter
