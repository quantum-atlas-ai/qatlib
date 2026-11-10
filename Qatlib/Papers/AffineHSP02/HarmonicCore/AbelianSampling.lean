/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AffineHSP02.HarmonicCore.GaussSums

set_option autoImplicit false

open AddChar MulChar BigOperators

namespace Qatlib.Papers.AffineHSP02.HarmonicCore

noncomputable section

def abelianProb (p : ℕ) [NeZero p] (b ℓ : ZMod p) (χ : MulChar (ZMod p) ℂ) : ℝ :=
  ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(ℓ * b)))‖ ^ 2 /
    ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)

section Prime

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem cast_pred (hp : 2 ≤ p) : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  norm_num

theorem cast_p_ne_zero : (p : ℝ) ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  positivity

theorem cast_pred_ne_zero : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [cast_pred hp]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

theorem norm_gauss_one_one : ‖gaussSum (1 : MulChar (ZMod p) ℂ)
    (1 : AddChar (ZMod p) ℂ)‖ = ((p - 1 : ℕ) : ℝ) := by
  rw [gauss_one_one]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [show ((p : ℂ) - 1) = (((p - 1 : ℕ) : ℝ) : ℂ) by
    rw [cast_pred hp]; push_cast; ring]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

theorem abelianProb_triv_triv (b : ZMod p) :
    abelianProb p b 0 (1 : MulChar (ZMod p) ℂ) = 1 / (p : ℝ) := by
  unfold abelianProb
  rw [zero_mul, neg_zero, AddChar.mulShift_zero, norm_gauss_one_one]
  have hpred : ((p - 1 : ℕ) : ℝ) ≠ 0 := cast_pred_ne_zero
  have hp0 : (p : ℝ) ≠ 0 := cast_p_ne_zero
  field_simp

theorem abelianProb_triv_nonzero (b ℓ : ZMod p) (hb : b ≠ 0) (hℓ : ℓ ≠ 0) :
    abelianProb p b ℓ (1 : MulChar (ZMod p) ℂ) =
      1 / ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2) := by
  have hshift : ZMod.stdAddChar.mulShift (-(ℓ * b)) ≠ 1 := by
    have hne : -(ℓ * b) ≠ 0 := by
      intro h
      apply mul_ne_zero hℓ hb
      exact neg_eq_zero.mp h
    exact (ZMod.isPrimitive_stdAddChar p) hne
  unfold abelianProb
  rw [gauss_one_add _ hshift]
  norm_num

theorem abelianProb_nonzero_triv (b : ZMod p) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    abelianProb p b 0 χ = 0 := by
  unfold abelianProb
  rw [zero_mul, neg_zero, AddChar.mulShift_zero, gauss_mul_one χ hχ]
  simp

theorem abelianProb_nonzero_nonzero (b ℓ : ZMod p) (hb : b ≠ 0) (hℓ : ℓ ≠ 0)
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    abelianProb p b ℓ χ = 1 / (((p - 1 : ℕ) : ℝ) ^ 2) := by
  have hshift : ZMod.stdAddChar.mulShift (-(ℓ * b)) ≠ 1 := by
    have hne : -(ℓ * b) ≠ 0 := by
      intro h
      apply mul_ne_zero hℓ hb
      exact neg_eq_zero.mp h
    exact (ZMod.isPrimitive_stdAddChar p) hne
  unfold abelianProb
  rw [gauss_norm_sqrt χ hχ _ hshift, ZMod.card,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p)]
  have hpred : ((p - 1 : ℕ) : ℝ) ≠ 0 := cast_pred_ne_zero
  have hp0 : (p : ℝ) ≠ 0 := cast_p_ne_zero
  field_simp

theorem abelianProb_independent_of_b (b b' : ZMod p) (hb : b ≠ 0) (hb' : b' ≠ 0)
    (ℓ : ZMod p) (χ : MulChar (ZMod p) ℂ) :
    abelianProb p b ℓ χ = abelianProb p b' ℓ χ := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    by_cases hχ : χ = 1
    · subst hχ
      rw [abelianProb_triv_triv, abelianProb_triv_triv]
    · rw [abelianProb_nonzero_triv b χ hχ, abelianProb_nonzero_triv b' χ hχ]
  · by_cases hχ : χ = 1
    · subst hχ
      rw [abelianProb_triv_nonzero b ℓ hb hℓ,
        abelianProb_triv_nonzero b' ℓ hb' hℓ]
    · rw [abelianProb_nonzero_nonzero b ℓ hb hℓ χ hχ,
        abelianProb_nonzero_nonzero b' ℓ hb' hℓ χ hχ]

end Prime

end

end Qatlib.Papers.AffineHSP02.HarmonicCore
