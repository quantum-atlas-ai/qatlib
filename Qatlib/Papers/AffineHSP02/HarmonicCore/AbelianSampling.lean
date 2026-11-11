/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AffineHSP02.HarmonicCore.GaussSums

/-!
# Abelian Fourier sampling probabilities

Defines `abelianProb` through normalized squared Gauss-sum norms and evaluates it according to
whether the multiplicative character and additive frequency are trivial. Over a prime field, the
resulting distribution is independent of the nonzero hidden conjugate parameter. See
[MooreEtAl2002].

## Main statements

* `abelianProb`: the sampling probability expressed by a Gauss sum.
* `abelianProb_independent_of_b`: all nonzero conjugate parameters give the same probabilities.

## References

* [Moore et al., 2002][MooreEtAl2002]
-/

set_option autoImplicit false

open AddChar MulChar BigOperators

namespace Qatlib.Papers.AffineHSP02.HarmonicCore

noncomputable section

/-- The abelian sampling probability given by the squared norm of the Gauss sum with additive
shift `-(ℓ * b)`, divided by `p * (p - 1)^2`. -/
def abelianProb (p : ℕ) [NeZero p] (b ℓ : ZMod p) (χ : MulChar (ZMod p) ℂ) : ℝ :=
  ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(ℓ * b)))‖ ^ 2 /
    ((p : ℝ) * ((p - 1 : ℕ) : ℝ) ^ 2)

section Prime

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- For `p ≥ 2`, casting `p - 1` from the natural numbers to the reals agrees with subtracting
one after casting. -/
theorem cast_pred (hp : 2 ≤ p) : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  norm_num

/-- The real cast of the prime `p` is nonzero. -/
theorem cast_p_ne_zero : (p : ℝ) ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  positivity

/-- The real cast of `p - 1` is nonzero for prime `p`. -/
theorem cast_pred_ne_zero : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [cast_pred hp]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

/-- The Gauss sum of the trivial multiplicative and additive characters has norm `p - 1`. -/
theorem norm_gauss_one_one : ‖gaussSum (1 : MulChar (ZMod p) ℂ)
    (1 : AddChar (ZMod p) ℂ)‖ = ((p - 1 : ℕ) : ℝ) := by
  rw [gauss_one_one]
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  rw [show ((p : ℂ) - 1) = (((p - 1 : ℕ) : ℝ) : ℂ) by
    rw [cast_pred hp]; push_cast; ring]
  rw [Complex.norm_real, Real.norm_of_nonneg]
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp
  linarith

/-- At zero additive frequency and the trivial multiplicative character, the abelian sampling
probability is `1 / p` [MooreEtAl2002]. -/
theorem abelianProb_triv_triv (b : ZMod p) :
    abelianProb p b 0 (1 : MulChar (ZMod p) ℂ) = 1 / (p : ℝ) := by
  unfold abelianProb
  rw [zero_mul, neg_zero, AddChar.mulShift_zero, norm_gauss_one_one]
  have hpred : ((p - 1 : ℕ) : ℝ) ≠ 0 := cast_pred_ne_zero
  have hp0 : (p : ℝ) ≠ 0 := cast_p_ne_zero
  field_simp

/-- For nonzero `b` and `ℓ` and the trivial multiplicative character, the sampling probability
is `1 / (p * (p - 1)^2)` [MooreEtAl2002]. -/
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

/-- A nontrivial multiplicative character has zero sampling probability at zero additive
frequency [MooreEtAl2002]. -/
theorem abelianProb_nonzero_triv (b : ZMod p) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    abelianProb p b 0 χ = 0 := by
  unfold abelianProb
  rw [zero_mul, neg_zero, AddChar.mulShift_zero, gauss_mul_one χ hχ]
  simp

/-- For nonzero `b` and `ℓ` and a nontrivial multiplicative character, the sampling probability
is `1 / (p - 1)^2` [MooreEtAl2002]. -/
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

/-- Abelian Fourier sampling gives identical probabilities for any two nonzero hidden conjugate
parameters `b` and `b'` [MooreEtAl2002]. -/
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
