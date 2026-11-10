/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT
import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2
import Mathlib.Data.Finset.NatAntidiagonal
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.NativeNumerics.NlfftPipeline
open Polynomial
open scoped BigOperators

def finiteCoefficientPolynomial (n : ℕ) (f : ℕ → ℂ) : Polynomial ℂ :=
  ∑ j : Fin n, Polynomial.monomial j.val (f j.val)

def finiteCoefficientPrefix (n : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  finiteCoefficientPolynomial n p.coeff

def finiteCoefficientConjRev (d : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  finiteCoefficientPolynomial (d + 1) (fun i => (starRingEnd ℂ) (p.coeff (d - i)))

structure FiniteFFTPolynomialMulRun where
  polynomial : Polynomial ℂ
  operations : ℕ

def finiteFFTPolynomialMul (q : ℕ) (A B : Polynomial ℂ) : FiniteFFTPolynomialMulRun :=
  let fa := radixTwoFourier q (fun j => A.coeff j.val)
  let fb := radixTwoFourier q (fun j => B.coeff j.val)
  let fi := radixTwoFourier q (fun j => fa.1 j * fb.1 j)
  let c : ℂ := ((2 ^ q : ℕ) : ℂ)⁻¹
  let coeff : ℕ → ℂ := fun j =>
    c * fi.1 ⟨((2 ^ q : ℕ) - j) % (2 ^ q),
      Nat.mod_lt _ (by positivity)⟩
  { polynomial := finiteCoefficientPolynomial (2 ^ q) coeff
    operations := fa.2.1 + fa.2.2 + fb.2.1 + fb.2.2 + fi.2.1 + fi.2.2
      + 2 * 2 ^ q + 1 }

theorem finiteCoefficientPolynomial_coeff (n : ℕ) (f : ℕ → ℂ) (i : ℕ) :
    (finiteCoefficientPolynomial n f).coeff i = if i < n then f i else 0 := by
  classical
  unfold finiteCoefficientPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hi : i < n
  · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg]
      intro hcon
      exact hb (Fin.val_inj.mp hcon)
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · rw [if_neg hi]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Polynomial.coeff_monomial, if_neg]
    intro hcon
    rw [← hcon] at hi
    exact hi j.isLt

theorem finiteCoefficientPolynomial_degree_lt (n : ℕ) (f : ℕ → ℂ) :
    (finiteCoefficientPolynomial n f).degree < (n : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [finiteCoefficientPolynomial_coeff, if_neg (by omega)]

theorem finiteCoefficientPrefix_eq_mod (n : ℕ) (p : Polynomial ℂ) :
    finiteCoefficientPrefix n p = p % X ^ n := by
  refine Polynomial.ext fun i => ?_
  by_cases hi : i < n
  · rw [finiteCoefficientPrefix, finiteCoefficientPolynomial_coeff, if_pos hi,
      coeff_mod_X_pow p n i hi]
  · rw [finiteCoefficientPrefix, finiteCoefficientPolynomial_coeff, if_neg hi]
    have hdeg : (p % X ^ n).degree < (n : WithBot ℕ) := by
      rw [← Polynomial.modByMonic_eq_mod p (Polynomial.monic_X_pow n)]
      have hlt := Polynomial.degree_modByMonic_lt p (Polynomial.monic_X_pow n)
      rwa [Polynomial.degree_X_pow] at hlt
    rw [Polynomial.degree_lt_iff_coeff_zero] at hdeg
    exact (hdeg i (by omega)).symm

theorem finiteCoefficientConjRev_eq (d : ℕ) (p : Polynomial ℂ) (hp : p.natDegree ≤ d) :
    finiteCoefficientConjRev d p = conjRevN d p := by
  refine Polynomial.ext fun i => ?_
  by_cases hi : i ≤ d
  · rw [finiteCoefficientConjRev, finiteCoefficientPolynomial_coeff,
      if_pos (by omega : i < d + 1), conjRevN_coeff d p i hi]
  · rw [finiteCoefficientConjRev, finiteCoefficientPolynomial_coeff,
      if_neg (by omega : ¬ i < d + 1)]
    have hd' := conjRevN_natDegree_le d p hp
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem finiteFFTPolynomialMul_operations (q : ℕ) (A B : Polynomial ℂ) :
    (finiteFFTPolynomialMul q A B).operations ≤ 10 * 2 ^ q * (q + 1) := by
  have key : ∀ f g : Fin (2 ^ q) → ℂ,
      (radixTwoFourier q f).2.1 + (radixTwoFourier q f).2.2
        + (radixTwoFourier q g).2.1 + (radixTwoFourier q g).2.2
        + (radixTwoFourier q
              (fun j => (radixTwoFourier q f).1 j * (radixTwoFourier q g).1 j)).2.1
        + (radixTwoFourier q
              (fun j => (radixTwoFourier q f).1 j * (radixTwoFourier q g).1 j)).2.2
        + 2 * 2 ^ q + 1 ≤ 10 * 2 ^ q * (q + 1) := by
    intro f g
    obtain ⟨h1, h2⟩ := radixTwoFourier_cost q f
    obtain ⟨h3, h4⟩ := radixTwoFourier_cost q g
    obtain ⟨h5, h6⟩ := radixTwoFourier_cost q
      (fun j => (radixTwoFourier q f).1 j * (radixTwoFourier q g).1 j)
    have hd1 : q * 2 ^ q / 2 ≤ q * 2 ^ q := Nat.div_le_self _ _
    have hpos : (1 : ℕ) ≤ 2 ^ q := Nat.one_le_two_pow
    nlinarith
  simpa only [finiteFFTPolynomialMul] using! key
    (fun j => A.coeff j.val) (fun j => B.coeff j.val)

private theorem expI_two_pi_int (n : ℤ) :
    Complex.exp ((n * (2 * Real.pi)) * Complex.I) = 1 := by
  have h := Complex.exp_eq_exp_iff_exists_int
    (x := (n * (2 * Real.pi)) * Complex.I) (y := 0)
  rw [Complex.exp_zero] at h
  refine h.mpr ⟨n, ?_⟩
  ring

private theorem sum_exp_char (S : ℕ) (hS : 0 < S) (r : ℤ) :
    ∑ t : Fin S, Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)
      = if (S : ℤ) ∣ r then (S : ℂ) else 0 := by
  have hcS : ((S : ℝ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hcSc : (((S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  set ζ : ℂ := Complex.exp ((-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I) with hζ
  have hterm : ∀ t : ℕ,
      Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I) = ζ ^ t := by
    intro t
    have h1 : ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)
        = (t * ((-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I)) := by
      push_cast
      field_simp
    rw [h1]
    exact (Complex.exp_nat_mul _ t).trans (by rw [hζ])
  have hζS : ζ ^ S = 1 := by
    have h2 : (((S : ℕ) : ℂ)) * ((-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I)
        = (((-r : ℤ) * (2 * Real.pi)) * Complex.I) := by
      push_cast
      field_simp
    rw [hζ, ← Complex.exp_nat_mul, h2]
    exact expI_two_pi_int (-r)
  by_cases hd : (S : ℤ) ∣ r
  · rw [if_pos hd]
    obtain ⟨c, hc⟩ := hd
    have hζ1 : ζ = 1 := by
      have h3 : ((-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I)
          = (((-c : ℤ) * (2 * Real.pi)) * Complex.I) := by
        rw [hc]
        push_cast
        field_simp
      rw [hζ, h3]
      exact expI_two_pi_int (-c)
    calc ∑ t : Fin S, Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)
        = ∑ t ∈ Finset.range S,
            Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I) :=
          Fin.sum_univ_eq_sum_range
            (fun t => Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)) S
      _ = ∑ t ∈ Finset.range S, ζ ^ t :=
          Finset.sum_congr rfl fun t _ => hterm t
      _ = ∑ t ∈ Finset.range S, (1 : ℂ) :=
          Finset.sum_congr rfl fun t _ => by rw [hζ1]; simp
      _ = (S : ℂ) := by simp
  · rw [if_neg hd]
    have hζne : ζ ≠ 1 := by
      intro hcon
      apply hd
      have hx1 : Complex.exp ((-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I) = 1 := by
        rw [← hζ]
        exact hcon
      obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int
        (x := (-2 * Real.pi * ((r : ℝ) / (S : ℝ))) * Complex.I) (y := 0) |>.mp
        (by rw [Complex.exp_zero]; exact hx1)
      rw [zero_add] at hn
      have him := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.mul_re, Complex.div_natCast_re, Complex.div_natCast_im,
        Complex.ofReal_natCast, Complex.ofReal_intCast, Complex.ofReal_re, Complex.ofReal_im,
        Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
        Complex.neg_re, Complex.neg_im, Complex.re_ofNat, Complex.im_ofNat,
        mul_zero, add_zero, mul_one, zero_mul, sub_zero] at him
      have himS : (-2 : ℝ) * Real.pi * ((r : ℝ)) = (n : ℝ) * (2 * Real.pi) * ((S : ℝ)) := by
        field_simp at him
        linarith
      have hfinal : ((r : ℝ)) = -(n : ℝ) * ((S : ℝ)) := by
        have hzero : (((r : ℝ)) + ((n : ℝ)) * ((S : ℝ))) * ((2 : ℝ) * Real.pi) = 0 := by
          linear_combination (-1 : ℝ) * himS
        have hsum : ((r : ℝ)) + ((n : ℝ)) * ((S : ℝ)) = 0 := by
          refine mul_right_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) ?_
          rw [zero_mul]
          exact hzero
        linarith
      refine ⟨-n, ?_⟩
      have hcomm : ((r : ℝ)) = ((S : ℝ)) * (-(n : ℝ)) := by rw [hfinal]; ring
      exact_mod_cast hcomm
    have hgeo := geom_sum_mul ζ S
    rw [hζS, sub_self] at hgeo
    rcases mul_eq_zero.mp hgeo with h | h
    · calc ∑ t : Fin S, Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)
          = ∑ t ∈ Finset.range S,
              Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I) :=
            Fin.sum_univ_eq_sum_range
              (fun t => Complex.exp ((-2 * Real.pi * ((r * (t : ℤ) : ℝ) / (S : ℝ))) * Complex.I)) S
        _ = ∑ t ∈ Finset.range S, ζ ^ t :=
            Finset.sum_congr rfl fun t _ => hterm t
        _ = 0 := h
    · exact absurd (sub_eq_zero.mp h) hζne

private theorem exp_fold_add (S : ℕ) (hS : 0 < S) (m m' t : ℕ) :
    (Complex.exp ((-2 * Real.pi * ((m * t : ℕ) / S : ℝ)) * Complex.I)
      * Complex.exp ((-2 * Real.pi * ((m' * t : ℕ) / S : ℝ)) * Complex.I))
      = Complex.exp ((-2 * Real.pi * (((m + m') * t : ℕ) / S : ℝ)) * Complex.I) := by
  have hcSc : (((S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem sum_exp_char_nat (S : ℕ) (hS : 0 < S) (n : ℕ) :
    ∑ t : Fin S, Complex.exp ((-2 * Real.pi * ((n * t.val : ℕ) / S : ℝ)) * Complex.I)
      = if (S : ℤ) ∣ (n : ℤ) then (S : ℂ) else 0 := by
  refine Eq.trans ?_ (sum_exp_char S hS (n : ℤ))
  refine Finset.sum_congr rfl fun t _ => ?_
  refine congrArg Complex.exp ?_
  push_cast
  field_simp

private theorem cyclic_convolution (S : ℕ) (hS : 0 < S) (a b : Fin S → ℂ) (k : ℕ) (hk : k < S) :
    ((S : ℂ)⁻¹ * ∑ t : Fin S,
        ((∑ l : Fin S, a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
          * (∑ l : Fin S, b l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)))
          * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))
      = ∑ l : Fin S, ∑ l' : Fin S,
          if (S : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (k : ℤ)) then a l * b l' else 0 := by
  have hcSc : (((S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'

  have hinner : ∀ l l' : Fin S,
      (∑ t : Fin S, (((S : ℂ)⁻¹
          * ((a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
            * (b l' * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))))
          * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)))
      = if (S : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (k : ℤ)) then a l * b l' else 0 := by
    intro l l'
    have hfold : ∀ t : Fin S,
        ((Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)
          * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I)))
          * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)
        = Complex.exp ((-2 * Real.pi *
            (((l.val + l'.val + (S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I) := by
      intro t
      have h1 : (Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)
            * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))
          = Complex.exp ((-2 * Real.pi *
              (((l.val + l'.val) * t.val : ℕ) / S : ℝ)) * Complex.I) := by
        rw [show t.val * l.val = l.val * t.val from Nat.mul_comm _ _,
          show t.val * l'.val = l'.val * t.val from Nat.mul_comm _ _]
        exact exp_fold_add S hS l.val l'.val t.val
      have h2 : (Complex.exp ((-2 * Real.pi *
              (((l.val + l'.val) * t.val : ℕ) / S : ℝ)) * Complex.I)
            * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))
          = Complex.exp ((-2 * Real.pi *
              (((l.val + l'.val + (S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I) :=
        exp_fold_add S hS (l.val + l'.val) ((S - k) % S) t.val
      rw [h1, h2]

    have hsumand : ∀ t : Fin S,
        (((S : ℂ)⁻¹
          * ((a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
            * (b l' * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))))
          * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))
        = (((S : ℂ)⁻¹ * (a l) * (b l'))
            * Complex.exp ((-2 * Real.pi *
                (((l.val + l'.val + (S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)) := by
      intro t
      calc (((S : ℂ)⁻¹
            * ((a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
              * (b l' * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))))
            * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))
          = (((S : ℂ)⁻¹ * (a l) * (b l'))
              * ((Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)
                * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))
                * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))) := by
              ring
        _ = (((S : ℂ)⁻¹ * (a l) * (b l'))
            * Complex.exp ((-2 * Real.pi *
                (((l.val + l'.val + (S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)) := by
              rw [hfold t]
    have hbr : ((S : ℤ)) ∣ ((((l.val + l'.val + (S - k) % S : ℕ) : ℤ))
        - (((l : ℤ) + (l' : ℤ)) - (k : ℤ))) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · refine ⟨0, ?_⟩
        rw [hk0]
        simp only [Nat.sub_zero, Nat.mod_self]
        omega
      · have hmod : ((S - k) % S : ℕ) = S - k := Nat.mod_eq_of_lt (by omega)
        refine ⟨1, ?_⟩
        rw [hmod]
        omega
    rw [Finset.sum_congr rfl fun t _ => hsumand t, ← Finset.mul_sum,
      sum_exp_char_nat S hS (l.val + l'.val + (S - k) % S)]
    by_cases hSd : (S : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (k : ℤ))
    · obtain ⟨d, hd⟩ := hbr
      have hn : ((S : ℤ)) ∣ ((((l.val + l'.val + (S - k) % S : ℕ) : ℤ))) := by
        obtain ⟨c, hc⟩ := hSd
        refine ⟨c + d, ?_⟩
        linear_combination hc + hd
      rw [if_pos hn, if_pos hSd]
      calc (((S : ℂ)⁻¹ * (a l) * (b l'))) * ((S : ℂ))
          = (((S : ℂ)⁻¹ * ((S : ℂ)))) * (a l * b l') := by ring
        _ = a l * b l' := by rw [inv_mul_cancel₀ hcSc, one_mul]
    · obtain ⟨d, hd⟩ := hbr
      have hn : ¬((S : ℤ)) ∣ ((((l.val + l'.val + (S - k) % S : ℕ) : ℤ))) := by
        intro hcon
        apply hSd
        obtain ⟨e, he⟩ := hcon
        refine ⟨e - d, ?_⟩
        linear_combination he - hd
      rw [if_neg hn, if_neg hSd, mul_zero]

  calc ((S : ℂ)⁻¹ * ∑ t : Fin S,
          (((∑ l : Fin S, a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
            * (∑ l : Fin S, b l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)))
            * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)))
      = ∑ t : Fin S, ((S : ℂ)⁻¹
          * (((∑ l : Fin S, a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
            * (∑ l : Fin S, b l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I)))
            * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I))) := by
          simp only [Finset.mul_sum]
    _ = ∑ t : Fin S, ∑ l : Fin S, ∑ l' : Fin S,
            (((S : ℂ)⁻¹
              * ((a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
                * (b l' * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))))
              * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_mul_sum]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
    _ = ∑ l : Fin S, ∑ l' : Fin S, ∑ t : Fin S,
            (((S : ℂ)⁻¹
              * ((a l * Complex.exp ((-2 * Real.pi * ((t.val * l.val : ℕ) / S : ℝ)) * Complex.I))
                * (b l' * Complex.exp ((-2 * Real.pi * ((t.val * l'.val : ℕ) / S : ℝ)) * Complex.I))))
              * Complex.exp ((-2 * Real.pi * ((((S - k) % S) * t.val : ℕ) / S : ℝ)) * Complex.I)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l : Fin S, ∑ l' : Fin S,
            if (S : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (k : ℤ)) then a l * b l' else 0 :=
          Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => hinner l l'

private theorem exp_sem_bridge (S j l : ℕ) :
    Complex.exp ((-2*Real.pi*j*l/(S : ℕ) : ℝ)*Complex.I)
      = Complex.exp ((-2 * Real.pi * ((j * l : ℕ) / S : ℝ)) * Complex.I) := by
  refine congrArg Complex.exp ?_
  push_cast
  field_simp

private theorem dvd_sub_range_cases (S : ℕ) (u v i : ℕ) (hi : i < S)
    (hu : u + v < 2 * S)
    (hd : (S : ℤ) ∣ (((u : ℤ) + (v : ℤ)) - (i : ℤ))) :
    u + v = i ∨ u + v = i + S := by
  rcases Nat.lt_or_ge (u + v) i with hlt | hge
  · exfalso
    have hneg : (((u : ℤ) + (v : ℤ)) - (i : ℤ)) = -(((i - u - v : ℕ) : ℤ)) := by
      omega
    rw [hneg] at hd
    have hd2 : ((S : ℤ)) ∣ (((i - u - v : ℕ) : ℤ)) := (dvd_neg.mp hd)
    have hd3 : S ∣ (i - u - v) := Int.natCast_dvd.mp hd2
    have h0 : i - u - v = 0 := Nat.eq_zero_of_dvd_of_lt hd3 (by omega)
    omega
  · have hc : (((u : ℤ) + (v : ℤ)) - (i : ℤ)) = (((u + v - i : ℕ) : ℤ)) := by
      omega
    rw [hc] at hd
    have hd2 : S ∣ (u + v - i) := Int.natCast_dvd.mp hd
    rcases Nat.lt_or_ge (u + v - i) S with hlt2 | hge2
    · left
      have h0 : u + v - i = 0 := Nat.eq_zero_of_dvd_of_lt hd2 hlt2
      omega
    · right
      have hd3 : S ∣ (u + v - i - S) := Nat.dvd_sub hd2 dvd_rfl
      have h0 : u + v - i - S = 0 := Nat.eq_zero_of_dvd_of_lt hd3 (by omega)
      omega

private theorem sum_antidiagonal_eq_range (f : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ x ∈ Finset.antidiagonal n, f x.1 x.2
      = ∑ j ∈ Finset.range (n + 1), f j (n - j) := by
  rw [Finset.Nat.antidiagonal_eq_image n,
    Finset.sum_image (fun a _ b _ hab => by
      have h := congrArg Prod.fst hab
      simp only at h
      exact h)]

theorem finiteFFTPolynomialMul_semantics (q : ℕ) (A B : Polynomial ℂ)
    (h : A.natDegree + B.natDegree < 2 ^ q) :
    (finiteFFTPolynomialMul q A B).polynomial = A * B := by
  have hS : 0 < 2 ^ q := Nat.two_pow_pos q
  simp only [finiteFFTPolynomialMul]
  refine Polynomial.ext fun i => ?_
  rw [finiteCoefficientPolynomial_coeff]
  by_cases hi : i < 2 ^ q
  · rw [if_pos hi]
    refine Eq.trans (Eq.trans ?_ (cyclic_convolution (2 ^ q) hS
      (fun l => A.coeff l.val) (fun l => B.coeff l.val) i hi)) ?_
    · simp only [radixTwoFourier_semantics, exp_sem_bridge]
    · (try dsimp only)
      have hpair : ∀ l l' : Fin (2 ^ q),
          (if ((2 ^ q : ℕ) : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (i : ℤ)) then A.coeff l.val * B.coeff l'.val else 0)
            = (if l.val + l'.val = i then A.coeff l.val * B.coeff l'.val else 0) := by
        intro l l'
        by_cases hsum : l.val + l'.val = i
        · have hd0 : ((2 ^ q : ℕ) : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (i : ℤ)) := by
            rw [show (((l : ℤ) + (l' : ℤ)) - (i : ℤ)) = 0 from by omega]
            exact dvd_zero _
          rw [if_pos hd0, if_pos hsum]
        · by_cases hd : ((2 ^ q : ℕ) : ℤ) ∣ (((l : ℤ) + (l' : ℤ)) - (i : ℤ))
          · rcases dvd_sub_range_cases (2 ^ q) l.val l'.val i hi
              (by have := l.isLt; have := l'.isLt; omega) hd with h1 | h1
            · exact absurd h1 hsum
            · have hprod : A.coeff l.val * B.coeff l'.val = 0 := by
                by_contra hne
                obtain ⟨hA0, hB0⟩ := mul_ne_zero_iff.mp hne
                have hA1 := Polynomial.le_natDegree_of_ne_zero hA0
                have hB1 := Polynomial.le_natDegree_of_ne_zero hB0
                omega
              rw [if_pos hd, if_neg hsum, hprod]
          · rw [if_neg hd, if_neg hsum]
      rw [Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun l' _ => hpair l l']
      rw [Polynomial.coeff_mul, sum_antidiagonal_eq_range (fun a b => A.coeff a * B.coeff b) i]
      rw [Fin.sum_univ_eq_sum_range
        (fun a => ∑ l' : Fin (2 ^ q), if a + l'.val = i then A.coeff a * B.coeff l'.val else 0)
        (2 ^ q)]
      rw [Finset.sum_congr rfl fun a _ =>
        Fin.sum_univ_eq_sum_range
          (fun b => if a + b = i then A.coeff a * B.coeff b else 0) (2 ^ q)]
      have hin : ∀ a ∈ Finset.range (2 ^ q),
          (∑ b ∈ Finset.range (2 ^ q), if a + b = i then A.coeff a * B.coeff b else 0)
            = (if a ≤ i then A.coeff a * B.coeff (i - a) else 0) := by
        intro a ha
        by_cases hai : a ≤ i
        · have hmem : (i - a) ∈ Finset.range (2 ^ q) := Finset.mem_range.mpr (by omega)
          rw [Finset.sum_eq_single (i - a)
            (fun b _ hb => if_neg (by omega))
            (fun hcon => absurd hmem hcon)]
          rw [if_pos (by omega), if_pos hai]
        · rw [Finset.sum_eq_zero fun b _ => if_neg (by omega), if_neg hai]
      rw [Finset.sum_congr rfl hin]
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : i + 1 ≤ 2 ^ q))
        (fun a _ hx => if_neg (by
          have hx' : i + 1 ≤ a := by simpa [Finset.mem_range] using! hx
          omega))]
      exact Finset.sum_congr rfl fun a ha =>
        if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
  · rw [if_neg hi]
    refine (Polynomial.coeff_eq_zero_of_natDegree_lt ?_).symm
    have hAB : (A * B).natDegree ≤ A.natDegree + B.natDegree :=
      Polynomial.natDegree_mul_le
    omega

end Qatlib.Concepts.NativeNumerics.NlfftPipeline
