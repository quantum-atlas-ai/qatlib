/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HiddenShift02.MainResults.FourierCore
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.HiddenShift02.MainResults.FourierCore
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.RingCharacter

noncomputable def unitFraction (R : Type*) [Monoid R] [Fintype R] [DecidableEq R] : ℝ :=
  (Fintype.card Rˣ : ℝ) / (Fintype.card R : ℝ)

theorem unitFraction_zmod (n : ℕ) [NeZero n] :
    unitFraction (ZMod n) = (Nat.totient n : ℝ) / (n : ℝ) := by
  unfold unitFraction
  rw [ZMod.card_units_eq_totient, ZMod.card]

theorem cubic_bound {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 3 ≤ a * b ^ 2 := by
  have hb : 0 ≤ b := le_trans ha hab
  have h2 : a * a ≤ b * b := mul_self_le_mul_self ha hab
  nlinarith

theorem mulChar_apply_ne_zero_iff (R : Type*) [CommRing R] (χ : MulChar R ℂ) (x : R) :
    χ x ≠ 0 ↔ IsUnit x := by
  constructor
  · intro h
    by_contra hx
    exact h (χ.map_nonunit hx)
  · intro hx h
    exact (hx.map χ.toMonoidHom).ne_zero h

noncomputable def unitsEquivIsUnit (R : Type*) [Monoid R] : Rˣ ≃ {x : R // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.2.unit
  left_inv u := Units.ext (IsUnit.unit_spec u.isUnit)
  right_inv x := Subtype.ext (IsUnit.unit_spec x.2)

theorem card_units_filter (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] :
    (Finset.univ.filter (fun x : R => IsUnit x)).card = Fintype.card Rˣ := by
  classical
  rw [← Fintype.card_subtype (fun x : R => IsUnit x)]
  exact Fintype.card_congr (unitsEquivIsUnit R).symm

theorem shifted_support_card (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (χ : MulChar R ℂ) (s : R) :
    (Finset.univ.filter (fun x : R => χ (x + s) ≠ 0)).card = Fintype.card Rˣ := by
  classical
  have h1 : Finset.univ.filter (fun x : R => χ (x + s) ≠ 0)
      = Finset.univ.filter (fun x : R => IsUnit (x + s)) := by
    ext x
    simp [mulChar_apply_ne_zero_iff R χ (x + s)]
  rw [h1]
  have h2 : (Finset.univ.filter (fun x : R => IsUnit (x + s))).card
      = (Finset.univ.filter (fun y : R => IsUnit y)).card := by
    refine Finset.card_bij (fun x _ => x + s) ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x1 _ x2 _ h
      simpa using h
    · intro y hy
      refine ⟨y - s, ?_, ?_⟩
      · simpa [sub_eq_add_neg, add_assoc] using hy
      · abel
  rw [h2, card_units_filter R]

theorem prep_probability (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (χ : MulChar R ℂ) (s : R) :
    ((Finset.univ.filter (fun x : R => χ (x + s) ≠ 0)).card : ℝ) / (Fintype.card R : ℝ)
      = unitFraction R := by
  rw [shifted_support_card R χ s]
  unfold unitFraction
  rfl

theorem inv_mulShift_inv (R : Type*) [CommRing R] (ψ : AddChar R ℂ) (a : R) :
    ((ψ⁻¹).mulShift a)⁻¹ = ψ.mulShift a := by
  ext x
  simp [AddChar.mulShift_apply, mul_neg]

theorem conj_addChar_eq_inv (R : Type*) [CommRing R] [Fintype R] (ψ : AddChar R ℂ) (a : R) :
    conj (ψ a) = ψ⁻¹ a := by
  have hR : 0 < ringChar R := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite R)
  exact AddChar.starComp_apply hR a

theorem fourier_mulShift_char (R : Type*) [CommRing R] [Fintype R] (χ : MulChar R ℂ)
    (ψ : AddChar R ℂ) {y : R} (hy : IsUnit y) :
    fourier χ (ψ.mulShift y) = χ⁻¹ y * fourier χ ψ := by
  classical
  set u : Rˣ := hy.unit with hu
  have huy : (u : R) = y := IsUnit.unit_spec _
  have hmul : ψ.mulShift y = ψ.mulShift (u : R) := by rw [huy]
  have hfg : fourier χ (ψ.mulShift (u : R)) =
      fourierScale R * gaussSum χ (ψ⁻¹.mulShift (u : R)) := by
    rw [fourier_apply, gaussSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply,
      conj_addChar_eq_inv R ψ (u * x)]
    ring
  have hfψ : fourier χ ψ = fourierScale R * gaussSum χ ψ⁻¹ := by
    rw [fourier_apply, gaussSum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [conj_addChar_eq_inv R ψ x]
    ring
  rw [hmul, hfg, gaussSum_mulShift_eq χ ψ⁻¹ u, hfψ]
  have hcoe : χ⁻¹ (u : R) = χ⁻¹ y := by rw [huy]
  rw [hcoe]
  ring

noncomputable def algorithmAmplitude (R : Type*) [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (s x : R) : ℂ :=
  fourierScale R * ∑ y : R,
    (ψ.mulShift y) x * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y))

theorem algorithm_amplitude_neg (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (s : R) :
    algorithmAmplitude R χ ψ s (-s) =
      fourierScale R * fourier χ ψ * ((Fintype.card Rˣ : ℕ) : ℂ) := by
  classical
  unfold algorithmAmplitude
  have hstep : ∀ y : R,
      (ψ.mulShift y) (-s) * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y))
        = fourier χ ψ *
            ((if χ y = 0 then (0 : ℂ) else 1) *
              ((ψ.mulShift y) (-s) * (ψ.mulShift y) s)) := by
    intro y
    by_cases h0 : χ y = 0
    · simp [h0]
    · have hunit : IsUnit y := (mulChar_apply_ne_zero_iff R χ y).mp h0
      have hshift := fourier_shift (fun z => χ z) s (ψ.mulShift y)
      rw [hshift, fourier_mulShift_char R χ ψ hunit]
      simp only [h0, if_false, one_mul]
      rw [MulChar.inv_apply_eq_inv' χ y]
      field_simp
  have hterm_one : ∀ y : R, (ψ.mulShift y) (-s) * (ψ.mulShift y) s = 1 := by
    intro y
    rw [AddChar.mulShift_apply, AddChar.mulShift_apply, ← AddChar.map_add_eq_mul,
      show y * -s + y * s = 0 by ring, AddChar.map_zero_eq_one]
  have hsum : (∑ y : R,
        ((if χ y = 0 then (0 : ℂ) else 1) *
          ((ψ.mulShift y) (-s) * (ψ.mulShift y) s)))
      = ((Fintype.card Rˣ : ℕ) : ℂ) := by
    have hfilter : (Finset.univ.filter (fun y : R => χ y ≠ 0)).card = Fintype.card Rˣ := by
      rw [show Finset.univ.filter (fun y : R => χ y ≠ 0)
            = Finset.univ.filter (fun y : R => IsUnit y) from by
            ext y
            simp [mulChar_apply_ne_zero_iff R χ y]]
      exact card_units_filter R
    rw [Finset.sum_congr rfl (fun y _ => by rw [hterm_one y, mul_one])]
    have hconv : ∀ y : R, (if χ y = 0 then (0 : ℂ) else 1)
        = (if χ y ≠ 0 then (1 : ℂ) else 0) := by
      intro y
      by_cases hy : χ y = 0 <;> simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => hconv y)]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hfilter]
  calc fourierScale R * (∑ y : R,
        (ψ.mulShift y) (-s) * (χ y * fourier (fun z => χ (z + s)) (ψ.mulShift y)))
      = fourierScale R * (∑ y : R,
          fourier χ ψ *
            ((if χ y = 0 then (0 : ℂ) else 1) *
              ((ψ.mulShift y) (-s) * (ψ.mulShift y) s))) := by
        rw [Finset.sum_congr rfl (fun y _ => hstep y)]
    _ = fourierScale R * (fourier χ ψ * (∑ y : R,
          ((if χ y = 0 then (0 : ℂ) else 1) *
            ((ψ.mulShift y) (-s) * (ψ.mulShift y) s)))) := by
        rw [← Finset.mul_sum]
    _ = fourierScale R * fourier χ ψ * ((Fintype.card Rˣ : ℕ) : ℂ) := by
        rw [hsum]
        ring

theorem measurement_probability (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (s : R)
    (hR : 0 < Fintype.card R) (hU : 0 < Fintype.card Rˣ)
    (hψhat : ‖fourier χ ψ‖ = 1) :
    ‖(((Real.sqrt ((Fintype.card Rˣ : ℝ))) : ℝ) : ℂ)⁻¹ *
        algorithmAmplitude R χ ψ s (-s)‖ ^ 2 = unitFraction R := by
  classical
  have hq : (0 : ℝ) < (Fintype.card R : ℝ) := Nat.cast_pos.mpr hR
  have hUR : (0 : ℝ) < (Fintype.card Rˣ : ℝ) := Nat.cast_pos.mpr hU
  have hscale : ‖fourierScale R‖ ^ 2 = ((Fintype.card R : ℝ))⁻¹ := by
    rw [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hq.le]
  have hsqrt : ‖((((Real.sqrt ((Fintype.card Rˣ : ℝ))) : ℝ)) : ℂ)⁻¹‖ ^ 2
      = ((Fintype.card Rˣ : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hUR.le]
  have hcardnorm : ‖(((Fintype.card Rˣ : ℕ)) : ℂ)‖ = ((Fintype.card Rˣ : ℕ) : ℝ) :=
    Complex.norm_natCast _
  rw [algorithm_amplitude_neg R χ ψ s]
  simp only [norm_mul, mul_pow, hscale, hψhat, hsqrt, hcardnorm]
  unfold unitFraction
  have hRne : (Fintype.card R : ℝ) ≠ 0 := ne_of_gt hq
  have hUne : (Fintype.card Rˣ : ℝ) ≠ 0 := ne_of_gt hUR
  field_simp

theorem source_theorem2 {n ell : ℕ} [NeZero n] [NeZero ell]
    (χ : MulChar (ZMod n) ℂ) (ψ : AddChar (ZMod n) ℂ) (s : ZMod n)
    (χ' : MulChar (ZMod ell) ℂ) (ψ' : AddChar (ZMod ell) ℂ) (s' : ZMod ell)
    (hUn : 0 < Fintype.card (ZMod n)ˣ) (hUl : 0 < Fintype.card (ZMod ell)ˣ)
    (hψ : ‖fourier χ ψ‖ = 1) (hψ' : ‖fourier χ' ψ'‖ = 1)
    (hmono : (Nat.totient n : ℝ) / (n : ℝ) ≤ (Nat.totient ell : ℝ) / (ell : ℝ)) :
    ((Finset.univ.filter (fun x : ZMod n => χ (x + s) ≠ 0)).card : ℝ) /
        (Fintype.card (ZMod n) : ℝ)
        = (Nat.totient n : ℝ) / (n : ℝ) ∧
      ‖(((Real.sqrt ((Fintype.card (ZMod ell)ˣ : ℝ))) : ℝ) : ℂ)⁻¹ *
          algorithmAmplitude (ZMod ell) χ' ψ' s' (-s')‖ ^ 2
        = (Nat.totient ell : ℝ) / (ell : ℝ) ∧
      ((Nat.totient n : ℝ) / (n : ℝ)) * ((Nat.totient ell : ℝ) / (ell : ℝ)) ^ 2
        ≥ ((Nat.totient n : ℝ) / (n : ℝ)) ^ 3 := by
  have hRl : 0 < Fintype.card (ZMod ell) := Fintype.card_pos
  have hprep : ((Finset.univ.filter (fun x : ZMod n => χ (x + s) ≠ 0)).card : ℝ) /
      (Fintype.card (ZMod n) : ℝ) = unitFraction (ZMod n) := prep_probability _ χ s
  have hmeas : ‖(((Real.sqrt ((Fintype.card (ZMod ell)ˣ : ℝ))) : ℝ) : ℂ)⁻¹ *
      algorithmAmplitude (ZMod ell) χ' ψ' s' (-s')‖ ^ 2 = unitFraction (ZMod ell) :=
    measurement_probability _ χ' ψ' s' hRl hUl hψ'
  have ha : 0 ≤ (Nat.totient n : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hprep, unitFraction_zmod]
  · rw [hmeas, unitFraction_zmod]
  · exact cubic_bound ha hmono

end Qatlib.Papers.HiddenShift02.MainResults.RingCharacter
