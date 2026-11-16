/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SoftDecoder24.MainResults.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Interval square-sum identities and convolution norm monotonicity. No decoder algorithm is asserted. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.SoftDecoder24.MainResults.FourierBounds
open Qatlib.Papers.SoftDecoder24.MainResults.Basic

/-- Sum of squares of a translated integer interval, written over the rationals. -/
theorem squareSum (A : ℚ) (ℓ : ℕ) :
    (∑ x ∈ Finset.Icc 1 ℓ, (A - (x : ℚ)) ^ 2) =
      ℓ * A ^ 2 - A * ℓ * (ℓ + 1) + ℓ * (ℓ + 1) * (2 * ℓ + 1) / 6 := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The interval square-sum polynomial identity in the legacy uniform RSC model. -/
theorem source_lemma3 (q u ℓ : ℕ) (hℓ : ℓ + (2 * u + 1) = q) :
    let ρ : ℚ := (2 * (u : ℚ) + 1) / (q : ℚ)
    2 * ∑ x ∈ Finset.Icc 1 ℓ, ((2 * (u : ℚ) + 1) - (x : ℚ)) ^ 2
      = ρ ^ 3 * (-(14 * (q : ℚ) ^ 3) / 3)
        + ρ ^ 2 * (8 * (q : ℚ) ^ 3 + 3 * (q : ℚ) ^ 2)
        + ρ * (-4 * (q : ℚ) ^ 3 - 4 * (q : ℚ) ^ 2 - (q : ℚ) / 3)
        + 2 * (q : ℚ) ^ 3 / 3 + (q : ℚ) ^ 2 + (q : ℚ) / 3 := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : (ℓ : ℚ) = q - (2 * u + 1) := by
    have he' : (ℓ : ℚ) + (2 * u + 1) = q := by exact_mod_cast hℓ
    linarith
  dsimp
  rw [squareSum]
  rw [he]
  field_simp
  ring

/-- The companion interval polynomial identity in the legacy uniform RSC model. -/
theorem source_lemma4 (q u ℓ : ℕ) (hℓ : ℓ + (2 * u + 1) = q) :
    let A : ℚ := 2 * (u : ℚ) + 1
    let ρ : ℚ := A / (q : ℚ)
    A ^ 2 + ((q : ℚ) - (2 * (ℓ : ℚ) + 1)) * (A - (ℓ : ℚ)) ^ 2
      = ρ ^ 3 * (8 * (q : ℚ) ^ 3) + ρ ^ 2 * (-12 * (q : ℚ) ^ 3 - 3 * (q : ℚ) ^ 2)
        + ρ * (6 * (q : ℚ) ^ 3 + 4 * (q : ℚ) ^ 2) - (q : ℚ) ^ 3 - (q : ℚ) ^ 2 := by
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : (ℓ : ℚ) = q - (2 * u + 1) := by
    have he' : (ℓ : ℚ) + (2 * u + 1) = q := by exact_mod_cast hℓ
    linarith
  dsimp
  rw [he]
  field_simp
  ring

/-- Replacing Fourier amplitudes by their norms increases the convolution fourth moment. -/
theorem conv_norm_mono {G : Type*} [AddGroup G] [Fintype G] (f g : G → ℂ)
    (hg : ∀ y, g y = ((‖f y‖ : ℝ) : ℂ)) :
    ∑ x, ‖conv g g x‖ ^ 2 ≥ ∑ x, ‖conv f f x‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro x _
  apply pow_le_pow_left₀ (norm_nonneg _) _
  have heq : conv g g x =
      ((∑ y, ‖f y‖ * ‖f (x - y)‖ : ℝ) : ℂ) := by
    simp only [conv, hg, Complex.ofReal_mul, Complex.ofReal_sum]
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
  simpa only [conv, norm_mul] using
    (norm_sum_le (Finset.univ) (fun y => f y * f (x - y)))


/-- Replacing normalized Fourier amplitudes by their absolute values increases their convolution energy. -/
theorem source_lemma5 {q : ℕ} [NeZero q] (f g : ZMod q → ℂ)
    (hg : ∀ y, dft1 g y = ((‖dft1 f y‖ : ℝ) : ℂ)) :
    ∑ x, ‖conv (dft1 g) (dft1 g) x‖ ^ 2 ≥
      ∑ x, ‖conv (dft1 f) (dft1 f) x‖ ^ 2 :=
  conv_norm_mono (dft1 f) (dft1 g) hg

end Qatlib.Papers.SoftDecoder24.MainResults.FourierBounds
