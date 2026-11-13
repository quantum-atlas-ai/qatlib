/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SoftDecoder24.MainResults.Basic
import Qatlib.Papers.SoftDecoder24.MainResults.Characters.SourceCharacters

set_option backward.isDefEq.respectTransparency false

/-!
# Fourth-Moment Fourier Convolution Identity and Additive-Energy Corollary

This module proves Proposition 8 and Corollary 2: over `ZMod q`, the fourth
moment `∑_x ‖f(x)‖⁴` equals `(1 / q) ∑_x ‖(f̂ ⋆ f̂)(x)‖²`, and when `f̂ = 1_S` is
the indicator of a subset `S ⊆ ZMod q`, it reduces to `(1 / q) ∑_x N_S(x)²`
where `N_S(x) = |{(a, b) ∈ S × S : a + b = x}|`.

## Main statements

* `indicator`, `Nset`: subset indicator on `ZMod q` and additive representation count `N_S(x)`.
* `source_proposition8`, `source_proposition8_p`: fourth-moment Fourier convolution identity.
* `source_corollary2`: additive-energy specialization when `dft1 f = indicator S`.

## References

* [Chailloux and Tillich, 2024][ChaillouxTillich2024], Proposition 8 and Corollary 2, pp. 20--21.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open scoped Classical
open Finset

namespace Qatlib.Papers.SoftDecoder24.MainResults.FourierFourth

open Qatlib.Papers.SoftDecoder24.MainResults.Basic

variable {q : ℕ} [NeZero q]

/-- The indicator function `1_S` of a finite set `S ⊆ ZMod q`. -/
def indicator (S : Finset (ZMod q)) : ZMod q → ℂ := fun y => if y ∈ S then 1 else 0

/-- `N_S(x) = |{(a, b) ∈ S × S : a + b = x}|`. -/
def Nset (S : Finset (ZMod q)) (x : ZMod q) : ℕ :=
  ((S ×ˢ S).filter (fun ab : ZMod q × ZMod q => ab.1 + ab.2 = x)).card

private theorem sum_char_products (g h : ZMod q → ℂ) :
    ∑ y, (∑ a, char y a * g a) * (∑ b, star (char y b) * h b) =
      (q : ℂ) * ∑ a, g a * h a := by
  calc
    _ = ∑ a, ∑ b, (∑ y, char y a * star (char y b)) * (g a * h b) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by
      simp only [Characters.sum_char_mul_star]
      simp [Finset.mul_sum, ite_mul]

private theorem dftNorm_cancel :
    dftNorm q * star (dftNorm q) * (q : ℂ) = 1 := by
  have hs : ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  simp only [dftNorm]
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_inv, ← pow_two, hs]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne q))

private theorem parseval_dft1 (g : ZMod q → ℂ) :
    ∑ y, ‖dft1 g y‖ ^ 2 = ∑ x, ‖g x‖ ^ 2 := by
  have h : ∑ y, dft1 g y * star (dft1 g y) = ∑ x, g x * star (g x) := by
    simp only [dft1, Complex.star_def, map_mul, map_sum]
    simp only [← Complex.star_def]
    calc
      _ = (dftNorm q * star (dftNorm q)) *
          ∑ y, (∑ a, char y a * g a) * (∑ b, star (char y b) * star (g b)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [sum_char_products, ← mul_assoc, dftNorm_cancel, one_mul]
  simpa only [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, Complex.re_sum,
    Complex.ofReal_re] using congrArg Complex.re h

private theorem conv_dft1 (f : ZMod q → ℂ) (y : ZMod q) :
    conv (dft1 f) (dft1 f) y =
      ((Real.sqrt (q : ℝ) : ℝ) : ℂ) * dft1 (fun a => f a * f a) y := by
  have hc (z b : ZMod q) : char (y - z) b = char y b * star (char z b) := by
    rw [Characters.char_symm b (y - z), ← Characters.char_mul_star,
      Characters.char_symm y b, Characters.char_symm z b]
  have hs : ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg q)
  have hn : ((Real.sqrt (q : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (NeZero.pos q)))
  unfold conv dft1
  simp only [hc]
  calc
    _ = (dftNorm q) ^ 2 *
        ∑ z, (∑ a, char z a * f a) *
          (∑ b, star (char z b) * (char y b * f b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have hsum : (∑ b, char y b * star (char z b) * f b) =
          ∑ b, star (char z b) * (char y b * f b) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      rw [hsum]
      ring
    _ = _ := by
      rw [sum_char_products]
      have hsum : (∑ a, f a * (char y a * f a)) = ∑ a, char y a * (f a * f a) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      rw [hsum, dftNorm, ← hs]
      field_simp

/-- **Proposition 8**: `∑_x ‖f(x)‖⁴ = (1 / q) ∑_x ‖(f̂ ⋆ f̂)(x)‖²`. -/
theorem source_proposition8 (f : ZMod q → ℂ) :
    ∑ x, ‖f x‖ ^ 4 = (1 / (q : ℝ)) * ∑ x, ‖conv (dft1 f) (dft1 f) x‖ ^ 2 := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  simp_rw [conv_dft1, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg q)]
  rw [← Finset.mul_sum, parseval_dft1, ← mul_assoc, one_div_mul_cancel hq, one_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [norm_mul]
  ring

/-- **Proposition 8** (`p = |f|²` form): `∑_x (‖f(x)‖²)² = (1 / q) ∑_x ‖(f̂ ⋆ f̂)(x)‖²`. -/
theorem source_proposition8_p (f : ZMod q → ℂ) :
    ∑ x, (‖f x‖ ^ 2) ^ 2 = (1 / (q : ℝ)) * ∑ x, ‖conv (dft1 f) (dft1 f) x‖ ^ 2 := by
  have h : ∀ x, (‖f x‖ ^ 2) ^ 2 = ‖f x‖ ^ 4 := fun _ => by ring
  simp only [h]
  exact source_proposition8 f

/-- **Corollary 2**: if `dft1 f = indicator S`, then `∑_x ‖f(x)‖⁴ = (1 / q) ∑_x N_S(x)²`. -/
theorem source_corollary2 (S : Finset (ZMod q)) (f : ZMod q → ℂ)
    (hf : ∀ y, dft1 f y = indicator S y) :
    ∑ x, ‖f x‖ ^ 4 = (1 / (q : ℝ)) * ∑ x, (Nset S x : ℝ) ^ 2 := by
  have hc (x : ZMod q) : conv (indicator S) (indicator S) x = (Nset S x : ℂ) := by
    have hcard : (Finset.univ.filter (fun y : ZMod q => y ∈ S ∧ x - y ∈ S)).card =
        Nset S x := by
      apply Finset.card_bij (fun y _ => (y, x - y))
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simpa only [Finset.mem_filter, Finset.mem_product, add_sub_cancel,
          and_true] using hy
      · intro a _ b _ hab
        exact congrArg Prod.fst hab
      · rintro ⟨a, b⟩ hab
        simp only [Finset.mem_filter, Finset.mem_product] at hab
        have hb : x - a = b := by rw [← hab.2]; abel
        exact ⟨a, by simp [hab.1.1, hab.1.2, hb], by simp [hb]⟩
    calc
      _ = ∑ y : ZMod q, if y ∈ S ∧ x - y ∈ S then (1 : ℂ) else 0 := by
        unfold conv indicator
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> simp_all
      _ = _ := by rw [← Finset.sum_filter]; simp [hcard]
  rw [source_proposition8 f]
  simp_rw [show dft1 f = indicator S from funext hf, hc, Complex.norm_natCast]

end Qatlib.Papers.SoftDecoder24.MainResults.FourierFourth
