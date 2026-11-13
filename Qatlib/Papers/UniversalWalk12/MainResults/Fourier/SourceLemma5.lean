/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Qatlib.Papers.UniversalWalk12.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier-Kernel Normalization and Tail Bounds

This module formalizes Lemma 5 of Childs, Gosset, and Webb: Parseval normalization
of the two-particle Fourier kernel `A` on `[-π, π]²`, the tail bound outside
`[-ε, ε]²`, and the `L²` bound on the shifted kernel `B` inside `[-ε, ε]²`.

## Main statements

* `source_lemma5`: exact `L²` normalization `∬_{D_π} |A|² dφ / (4π²) = 1`, exterior
  tail bound `≤ 4π / (L ε)`, and interior bound on `|B|²` `≤ 16π² / (L² ε²)`.

## References

* [Childs, Gosset, and Webb, 2013][ChildsGossetWebb2013], Appendix G, Lemma 5, p. 62.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

open Qatlib.Papers.UniversalWalk12.MainResults.Model

private def dirichlet (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range L, Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))

private def kernel (L : ℕ) (θ : ℝ) : ℝ := ‖dirichlet L θ‖ ^ 2

@[fun_prop] private lemma continuous_dirichlet (L : ℕ) : Continuous (dirichlet L) := by
  unfold dirichlet
  fun_prop

@[fun_prop] private lemma continuous_kernel (L : ℕ) : Continuous (kernel L) :=
  (continuous_dirichlet L).norm.pow 2

private lemma kernel_nonneg (L : ℕ) (θ : ℝ) : 0 ≤ kernel L θ :=
  sq_nonneg _

private lemma kernel_even (L : ℕ) (θ : ℝ) : kernel L (-θ) = kernel L θ := by
  have h : dirichlet L (-θ) = (starRingEnd ℂ) (dirichlet L θ) := by
    simp only [dirichlet, map_sum, Complex.ofReal_neg]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, map_natCast, Complex.conj_ofReal]
    ring
  simp only [kernel, h, Complex.norm_conj]

private lemma kernel_periodic (L : ℕ) : Function.Periodic (kernel L) (2 * Real.pi) := by
  intro θ
  have h : dirichlet L (θ + 2 * Real.pi) = dirichlet L θ := by
    unfold dirichlet
    apply Finset.sum_congr rfl
    intro n hn
    rw [show Complex.I * (n : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) =
        Complex.I * (n : ℂ) * (θ : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      ring, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp only [kernel, h]

private lemma kernel_eq_sum_cos (L : ℕ) (θ : ℝ) :
    kernel L θ = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      Real.cos (((a : ℝ) - (b : ℝ)) * θ) := by
  have h : kernel L θ = (dirichlet L θ * (starRingEnd ℂ) (dirichlet L θ)).re := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    rfl
  rw [h]
  simp only [dirichlet, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Complex.exp_conj, ← Complex.exp_add]
  rw [show Complex.I * (a : ℂ) * (θ : ℂ) +
      (starRingEnd ℂ) (Complex.I * (b : ℂ) * (θ : ℂ)) =
      (((a : ℝ) - (b : ℝ)) * θ : ℝ) * Complex.I by
    simp
    ring]
  exact Complex.exp_ofReal_mul_I_re _

private lemma integral_cos_int (m : ℤ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos ((m : ℝ) * θ)) =
      if m = 0 then 2 * Real.pi else 0 := by
  by_cases hm : m = 0
  · simp [hm]
    ring
  · rw [ite_eq_right hm, intervalIntegral.integral_comp_mul_left Real.cos (by exact_mod_cast hm),
      integral_cos]
    simp [mul_neg, Real.sin_neg, Real.sin_int_mul_pi]

private lemma integral_kernel (L : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, kernel L θ) = 2 * Real.pi * (L : ℝ) := by
  simp_rw [kernel_eq_sum_cos]
  rw [intervalIntegral.integral_finsetSum]
  · have hsum (a : ℕ) :
        (∫ θ in (-Real.pi)..Real.pi, ∑ b ∈ Finset.range L,
          Real.cos (((a : ℝ) - (b : ℝ)) * θ)) =
          ∑ b ∈ Finset.range L, ∫ θ in (-Real.pi)..Real.pi,
            Real.cos (((a : ℝ) - (b : ℝ)) * θ) := by
      apply intervalIntegral.integral_finsetSum
      intro b hb
      exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    simp_rw [hsum, show ∀ a b : ℕ, ((a : ℝ) - (b : ℝ)) = ((a : ℤ) - (b : ℤ) : ℤ) by
      intros; push_cast; rfl]
    simp_rw [integral_cos_int, sub_eq_zero, Int.natCast_inj]
    simp [Finset.sum_ite_of_true]
    ring
  · intro a ha
    apply Continuous.intervalIntegrable
    fun_prop

private lemma dirichlet_geom (L : ℕ) (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ)) - 1) * dirichlet L θ =
      Complex.exp (Complex.I * (L : ℂ) * (θ : ℂ)) - 1 := by
  have hsum : dirichlet L θ = ∑ n ∈ Finset.range L,
      Complex.exp (Complex.I * (θ : ℂ)) ^ n := by
    unfold dirichlet
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hsum, mul_geom_sum, ← Complex.exp_nat_mul]
  congr 2
  ring

private lemma exp_sub_one_norm_sq (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ^ 2 =
      4 * Real.sin (θ / 2) ^ 2 := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  ring

private lemma kernel_le_csc_sq (L : ℕ) (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) :
    kernel L θ ≤ 1 / Real.sin (θ / 2) ^ 2 := by
  have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) (dirichlet_geom L θ)
  rw [norm_mul, mul_pow, exp_sub_one_norm_sq,
    show Complex.I * (L : ℂ) * (θ : ℂ) =
      Complex.I * (((L : ℝ) * θ : ℝ) : ℂ) by push_cast; ring,
    exp_sub_one_norm_sq] at h
  have hsin : Real.sin ((L : ℝ) * θ / 2) ^ 2 ≤ 1 :=
    Real.sin_sq_le_one _
  apply (le_div_iff₀ (sq_pos_of_ne_zero hs)).2
  dsimp only [kernel]
  nlinarith

-- FACTORIZATION SECTION

private lemma sum_positive_window (M L : ℕ) (f : ℤ → ℂ) :
    (∑ y ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)), f y) =
      ∑ b ∈ Finset.range L, f ((M : ℤ) + 1 + (b : ℤ)) := by
  symm
  refine Finset.sum_bij (fun b _ => (M : ℤ) + 1 + (b : ℤ)) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_range] at hb
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    exact_mod_cast (show (a : ℤ) = (b : ℤ) by omega)
  · intro y hy
    simp only [Finset.mem_Icc] at hy
    refine ⟨(y - ((M : ℤ) + 1)).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro b hb
    rfl

private lemma sum_negative_window (M L : ℕ) (f : ℤ → ℂ) :
    (∑ x ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)), f x) =
      ∑ a ∈ Finset.range L, f (-((M : ℤ) + 1) - (a : ℤ)) := by
  symm
  refine Finset.sum_bij (fun a _ => -((M : ℤ) + 1) - (a : ℤ)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    exact_mod_cast (show (a : ℤ) = (b : ℤ) by omega)
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    refine ⟨(-((M : ℤ) + 1) - x).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro a ha
    rfl

private lemma exp_positive_window (M L : ℕ) (t : ℝ) :
    (∑ y ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)),
      Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
      Complex.exp (Complex.I * (t : ℂ) * ((M : ℂ) + 1)) * dirichlet L t := by
  rw [sum_positive_window, dirichlet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma exp_negative_window (M L : ℕ) (t : ℝ) :
    (∑ x ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)),
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ) * ((M : ℂ) + 1)) * dirichlet L (-t) := by
  rw [sum_negative_window, dirichlet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ampA_factor (M L : ℕ) (φ1 φ2 : ℝ) :
    AmpA M L φ1 φ2 =
      ((1 / (L : ℝ) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * ((φ1 / 2 + φ2 : ℝ) : ℂ) * ((M : ℂ) + 1)) *
          dirichlet L (-(φ1 / 2 + φ2))) *
        (Complex.exp (Complex.I * ((φ1 / 2 - φ2 : ℝ) : ℂ) * ((M : ℂ) + 1)) *
          dirichlet L (φ1 / 2 - φ2)) := by
  rw [← exp_negative_window, ← exp_positive_window, AmpA, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ampB_factor (M L : ℕ) (φ1 φ2 k : ℝ) :
    AmpB M L φ1 φ2 k =
      ((1 / (L : ℝ) : ℝ) : ℂ) *
        (Complex.exp (-Complex.I * ((φ1 / 2 - (φ2 + 2 * k) : ℝ) : ℂ) *
          ((M : ℂ) + 1)) * dirichlet L (-(φ1 / 2 - (φ2 + 2 * k)))) *
        (Complex.exp (Complex.I * ((φ1 / 2 + (φ2 + 2 * k) : ℝ) : ℂ) *
          ((M : ℂ) + 1)) * dirichlet L (φ1 / 2 + (φ2 + 2 * k))) := by
  rw [← exp_negative_window, ← exp_positive_window, AmpB, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_window_phase (M : ℕ) (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * ((M : ℂ) + 1))‖ = 1 := by
  have heq : Complex.I * (t : ℂ) * ((M : ℂ) + 1) =
      Complex.I * ((t * ((M : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal]

private lemma kernel_ampA (M L : ℕ) (φ1 φ2 : ℝ) :
    ‖AmpA M L φ1 φ2‖ ^ 2 =
      (1 / (L : ℝ) ^ 2) * kernel L (φ1 / 2 + φ2) *
        kernel L (φ1 / 2 - φ2) := by
  rw [ampA_factor]
  have hphase : -Complex.I * ((φ1 / 2 + φ2 : ℝ) : ℂ) * ((M : ℂ) + 1) =
      Complex.I * ((-(φ1 / 2 + φ2) : ℝ) : ℂ) * ((M : ℂ) + 1) := by
    push_cast
    ring
  simp only [norm_mul, hphase, norm_window_phase, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_one, Nat.abs_cast, mul_pow, div_pow, one_pow]
  rw [← kernel, ← kernel, kernel_even]

private lemma kernel_ampB (M L : ℕ) (φ1 φ2 k : ℝ) :
    ‖AmpB M L φ1 φ2 k‖ ^ 2 =
      (1 / (L : ℝ) ^ 2) * kernel L (φ2 + 2 * k - φ1 / 2) *
        kernel L (φ2 + 2 * k + φ1 / 2) := by
  rw [ampB_factor]
  have hphase : -Complex.I * ((φ1 / 2 - (φ2 + 2 * k) : ℝ) : ℂ) *
      ((M : ℂ) + 1) = Complex.I * ((-(φ1 / 2 - (φ2 + 2 * k)) : ℝ) : ℂ) *
      ((M : ℂ) + 1) := by
    push_cast
    ring
  simp only [norm_mul, hphase, norm_window_phase, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_one, Nat.abs_cast, mul_pow, div_pow, one_pow]
  rw [← kernel, ← kernel]
  congr 2 <;> ring

private lemma continuous_ampA_sq (M L : ℕ) :
    Continuous (fun p : ℝ × ℝ => ‖AmpA M L p.1 p.2‖ ^ 2) := by
  simp_rw [kernel_ampA]
  exact (continuous_const.mul ((continuous_kernel L).comp
    ((continuous_fst.div_const 2).add continuous_snd))).mul
      ((continuous_kernel L).comp ((continuous_fst.div_const 2).sub continuous_snd))

private lemma continuous_ampB_sq (M L : ℕ) (k : ℝ) :
    Continuous (fun p : ℝ × ℝ => ‖AmpB M L p.1 p.2 k‖ ^ 2) := by
  simp_rw [kernel_ampB]
  exact (continuous_const.mul ((continuous_kernel L).comp
    ((continuous_snd.add continuous_const).sub (continuous_fst.div_const 2)))).mul
      ((continuous_kernel L).comp
        ((continuous_snd.add continuous_const).add (continuous_fst.div_const 2)))

-- ANALYTIC SECTION

private lemma one_div_sin_sq_le (a θ : ℝ) (ha : 0 < a)
    (h : a ≤ |Real.sin θ|) : 1 / Real.sin θ ^ 2 ≤ 1 / a ^ 2 := by
  apply one_div_le_one_div_of_le (sq_pos_of_pos ha)
  simpa only [sq_abs] using (sq_le_sq₀ ha.le (abs_nonneg (Real.sin θ))).2 h

private lemma sin_shift_lower_bound (k ε θ : ℝ)
    (hε0 : 0 < ε) (hε : ε < min (Real.pi - |k|) |k|)
    (hθ : |θ / 2 - k| ≤ 3 * ε / 4) :
    ε / (2 * Real.pi) ≤ |Real.sin (θ / 2)| := by
  have he₁ : ε < Real.pi - |k| := hε.trans_le (min_le_left _ _)
  have he₂ : ε < |k| := hε.trans_le (min_le_right _ _)
  have heπ : ε < Real.pi / 2 := by linarith
  have hu₀ : ε / 4 < |θ / 2| := by
    have ht := abs_add_le (θ / 2) (k - θ / 2)
    have hn : |k - θ / 2| = |θ / 2 - k| := abs_sub_comm _ _
    rw [show θ / 2 + (k - θ / 2) = k by ring, hn] at ht
    linarith
  have huπ : |θ / 2| < Real.pi - ε / 4 := by
    have ht := abs_add_le (θ / 2 - k) k
    rw [show θ / 2 - k + k = θ / 2 by ring] at ht
    linarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith : |θ / 2| ≤ Real.pi)]
  have hl : 2 / Real.pi * (ε / 4) ≤ Real.sin (ε / 4) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hs : Real.sin (ε / 4) ≤ Real.sin |θ / 2| := by
    by_cases hh : |θ / 2| ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hh hu₀.le
    · rw [← Real.sin_pi_sub |θ / 2|]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith) (by linarith)
  calc
    ε / (2 * Real.pi) = 2 / Real.pi * (ε / 4) := by ring
    _ ≤ Real.sin (ε / 4) := hl
    _ ≤ Real.sin |θ / 2| := hs

private lemma csc_shift_bound (k ε θ : ℝ)
    (hε0 : 0 < ε) (hε : ε < min (Real.pi - |k|) |k|)
    (hθ : |θ / 2 - k| ≤ 3 * ε / 4) :
    1 / Real.sin (θ / 2) ^ 2 ≤ 4 * Real.pi ^ 2 / ε ^ 2 := by
  calc
    1 / Real.sin (θ / 2) ^ 2 ≤ 1 / (ε / (2 * Real.pi)) ^ 2 :=
      one_div_sin_sq_le _ _ (by positivity) (sin_shift_lower_bound k ε θ hε0 hε hθ)
    _ = 4 * Real.pi ^ 2 / ε ^ 2 := by field_simp; ring

private lemma csc_sq_le_inverse_square (θ : ℝ) (hθ0 : 0 < θ)
    (hθπ : θ ≤ Real.pi) :
    1 / Real.sin (θ / 2) ^ 2 ≤ Real.pi ^ 2 / θ ^ 2 := by
  have hs : θ / Real.pi ≤ |Real.sin (θ / 2)| := by
    have h := Real.mul_le_sin (x := θ / 2) (by positivity) (by linarith)
    have hh : θ / Real.pi = 2 / Real.pi * (θ / 2) := by ring
    exact hh ▸ h.trans (le_abs_self _)
  calc
    1 / Real.sin (θ / 2) ^ 2 ≤ 1 / (θ / Real.pi) ^ 2 :=
      one_div_sin_sq_le _ _ (by positivity) hs
    _ = Real.pi ^ 2 / θ ^ 2 := by field_simp

private lemma csc_sq_le_two (θ : ℝ) (hθ₁ : Real.pi ≤ θ)
    (hθ₂ : θ ≤ 3 * Real.pi / 2) :
    1 / Real.sin (θ / 2) ^ 2 ≤ 2 := by
  have hc := Real.cos_nonpos_of_pi_div_two_le_of_le (x := θ)
    (by linarith [Real.pi_pos]) (by linarith)
  have hd := Real.cos_two_mul (θ / 2)
  have hi := Real.sin_sq_add_cos_sq (θ / 2)
  have hs : (1 : ℝ) / 2 ≤ Real.sin (θ / 2) ^ 2 := by
    rw [show 2 * (θ / 2) = θ by ring] at hd
    nlinarith
  apply (div_le_iff₀ (by linarith : 0 < Real.sin (θ / 2) ^ 2)).2
  linarith

private lemma integral_pi_sq_div_sq (ε : ℝ) (hε0 : 0 < ε) :
    (∫ θ in ε / 2..Real.pi, Real.pi ^ 2 / θ ^ 2) =
      2 * Real.pi ^ 2 / ε - Real.pi := by
  have hz := integral_zpow (a := ε / 2) (b := Real.pi) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt (by positivity) Real.pi_pos⟩)
  norm_num at hz
  calc
    (∫ θ in ε / 2..Real.pi, Real.pi ^ 2 / θ ^ 2) =
        Real.pi ^ 2 * ∫ θ in ε / 2..Real.pi, (θ ^ 2)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
    _ = 2 * Real.pi ^ 2 / ε - Real.pi := by
      rw [hz]
      field_simp [hε0.ne', Real.pi_ne_zero]
      ring

private lemma kernel_shift_bound (L : ℕ) (k ε θ : ℝ)
    (hε0 : 0 < ε) (hε : ε < min (Real.pi - |k|) |k|)
    (hθ : |θ / 2 - k| ≤ 3 * ε / 4) :
    kernel L θ ≤ 4 * Real.pi ^ 2 / ε ^ 2 := by
  have hs : Real.sin (θ / 2) ≠ 0 := by
    apply abs_pos.mp
    exact lt_of_lt_of_le (by positivity : 0 < ε / (2 * Real.pi))
      (sin_shift_lower_bound k ε θ hε0 hε hθ)
  exact (kernel_le_csc_sq L θ hs).trans (csc_shift_bound k ε θ hε0 hε hθ)

private lemma kernel_tail_integral (L : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε ≤ Real.pi / 2) :
    (∫ θ in ε / 2..(3 * Real.pi / 2), kernel L θ) ≤
      2 * Real.pi ^ 2 / ε := by
  have hab : ε / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hbc : Real.pi ≤ 3 * Real.pi / 2 := by linarith [Real.pi_pos]
  have hcont : ContinuousOn (fun θ : ℝ => Real.pi ^ 2 / θ ^ 2)
      (Icc (ε / 2) Real.pi) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by positivity : 0 < ε / 2) hθ.1))
  have hb₁ : (∫ θ in ε / 2..Real.pi, kernel L θ) ≤
      2 * Real.pi ^ 2 / ε - Real.pi := by
    rw [← integral_pi_sq_div_sq ε hε0]
    apply intervalIntegral.integral_mono_on hab
      ((continuous_kernel L).intervalIntegrable _ _) (hcont.intervalIntegrable_of_Icc hab)
    intro θ hθ
    have ht : 0 < θ := lt_of_lt_of_le (by positivity : 0 < ε / 2) hθ.1
    have hs : Real.sin (θ / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ.2])).ne'
    exact (kernel_le_csc_sq L θ hs).trans (csc_sq_le_inverse_square θ ht hθ.2)
  have hb₂ : (∫ θ in Real.pi..(3 * Real.pi / 2), kernel L θ) ≤ Real.pi := by
    have ht : (∫ θ in Real.pi..(3 * Real.pi / 2), kernel L θ) ≤
        ∫ _θ in Real.pi..(3 * Real.pi / 2), (2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hbc
        ((continuous_kernel L).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
      intro θ hθ
      have hs : Real.sin (θ / 2) ≠ 0 :=
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
          (by linarith [Real.pi_pos, hθ.2])).ne'
      exact (kernel_le_csc_sq L θ hs).trans (csc_sq_le_two θ hθ.1 hθ.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      show (3 * Real.pi / 2 - Real.pi) * 2 = Real.pi by ring] using ht
  calc
    (∫ θ in ε / 2..(3 * Real.pi / 2), kernel L θ) =
        (∫ θ in ε / 2..Real.pi, kernel L θ) +
          ∫ θ in Real.pi..(3 * Real.pi / 2), kernel L θ :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_kernel L).intervalIntegrable _ _)
        ((continuous_kernel L).intervalIntegrable _ _)).symm
    _ ≤ (2 * Real.pi ^ 2 / ε - Real.pi) + Real.pi := add_le_add hb₁ hb₂
    _ = 2 * Real.pi ^ 2 / ε := by ring

-- INTEGRATION SECTION

open MeasureTheory

private lemma setIntegralR_interval (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) :
    setIntegralR (Icc a b) f = ∫ x in a..b, f x := by
  rw [setIntegralR, intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc]

private lemma continuous_interval_param {f : ℝ → ℝ → ℝ}
    (hf : Continuous f.uncurry) (a b : ℝ) (hab : a ≤ b) :
    Continuous (fun x => ∫ y in a..b, f x y) := by
  simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact continuous_parametric_integral_of_continuous hf isCompact_Icc

private lemma interval_swap {f : ℝ → ℝ → ℝ}
    (hf : Continuous f.uncurry) (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  apply intervalIntegral_intervalIntegral_swap
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private lemma truncated_interval_le {f : ℝ → ℝ} (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) (a b A c : ℝ) (hab : a ≤ b)
    (ha : -A ≤ a) (hb : b ≤ A) (hc : 0 < c) (hcA : c ≤ A) :
    (∫ x in a..b, if c ≤ |x| then f x else 0) ≤
      (∫ x in (-A)..(-c), f x) + ∫ x in c..A, f x := by
  let s : Set ℝ := {x | c ≤ |x|}
  have hs : MeasurableSet s := (isClosed_le continuous_const continuous_abs).measurableSet
  have heq : Icc (-A) A ∩ s = Icc (-A) (-c) ∪ Icc c A := by
    ext x
    simp only [mem_inter_iff, mem_Icc, mem_union, s, mem_ofPred_eq, le_abs]
    constructor
    · rintro ⟨⟨hx1, hx2⟩, hx | hx⟩
      · exact Or.inr ⟨hx, hx2⟩
      · exact Or.inl ⟨hx1, by linarith⟩
    · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩)
      · exact ⟨⟨hx1, by linarith⟩, Or.inr (by linarith)⟩
      · exact ⟨⟨by linarith, hx2⟩, Or.inl hx1⟩
  have hd : Disjoint (Icc (-A) (-c)) (Icc c A) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    simp only [mem_Icc] at hx hy
    linarith
  calc
    _ = ∫ x in Icc a b, s.indicator f x := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      rfl
    _ ≤ ∫ x in Icc (-A) A, s.indicator f x := by
      apply setIntegral_mono_set
        ((hf.integrableOn_Icc).indicator hs)
        (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => hn _) x)
      exact Filter.Eventually.of_forall (fun _ hx => ⟨ha.trans hx.1, hx.2.trans hb⟩)
    _ = (∫ x in Icc (-A) (-c), f x) + ∫ x in Icc c A, f x := by
      rw [setIntegral_indicator hs, heq, setIntegral_union hd measurableSet_Icc
        hf.integrableOn_Icc hf.integrableOn_Icc]
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -A ≤ -c),
        ← intervalIntegral.integral_of_le hcA]

private lemma integral_kernel_sub (L : ℕ) (t : ℝ) :
    (∫ x in (-Real.pi)..Real.pi, kernel L (x - t)) =
      2 * Real.pi * (L : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_right]
  have h : (∫ x in (-Real.pi - t)..(Real.pi - t), kernel L x) =
      ∫ x in (-Real.pi)..Real.pi, kernel L x := by
    convert (kernel_periodic L).intervalIntegral_add_eq (-Real.pi - t) (-Real.pi)
      using 1 <;> congr 1 <;> ring
  rw [h, integral_kernel]

private lemma integral_kernel_product (L : ℕ) :
    (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
      kernel L (x / 2 + y) * kernel L (x / 2 - y)) =
        (2 * Real.pi * (L : ℝ)) ^ 2 := by
  have shift (x : ℝ) :
      (∫ y in (-Real.pi)..Real.pi,
        kernel L (x / 2 + y) * kernel L (x / 2 - y)) =
      ∫ y in (-Real.pi)..Real.pi, kernel L y * kernel L (x - y) := by
    have hp : Function.Periodic (fun y => kernel L y * kernel L (x - y))
        (2 * Real.pi) := by
      intro y
      dsimp only
      rw [(kernel_periodic L) y]
      congr 1
      rw [show x - (y + 2 * Real.pi) = x - y - 2 * Real.pi by ring]
      exact (kernel_periodic L).sub_eq (x - y)
    calc
      _ = ∫ y in (-Real.pi)..Real.pi,
          (fun u => kernel L u * kernel L (x - u)) (x / 2 + y) := by
        congr 1; ext y; congr 1; congr 1; ring
      _ = ∫ y in (x / 2 + -Real.pi)..(x / 2 + Real.pi),
          kernel L y * kernel L (x - y) :=
        intervalIntegral.integral_comp_add_left
          (fun u => kernel L u * kernel L (x - u)) (x / 2)
      _ = ∫ y in (-Real.pi)..Real.pi, kernel L y * kernel L (x - y) := by
        convert hp.intervalIntegral_add_eq (x / 2 + -Real.pi) (-Real.pi) using 1 <;>
          congr 1 <;> ring
  simp_rw [shift]
  rw [interval_swap (by fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, integral_kernel_sub,
    intervalIntegral.integral_mul_const, integral_kernel]
  ring

private def tailMajorant (L : ℕ) (ε x : ℝ) : ℝ :=
  (∫ u in (-(3 * Real.pi / 2))..(-ε / 2), kernel L u * kernel L (x - u)) +
    ∫ u in (ε / 2)..(3 * Real.pi / 2), kernel L u * kernel L (x - u)

private lemma continuous_tailMajorant (L : ℕ) (ε : ℝ) (hε : ε ≤ Real.pi / 2) :
    Continuous (tailMajorant L ε) := by
  unfold tailMajorant
  apply Continuous.add
  · exact continuous_interval_param (by fun_prop) _ _ (by linarith [Real.pi_pos])
  · exact continuous_interval_param (by fun_prop) _ _ (by linarith [Real.pi_pos])

private lemma integral_tailMajorant (L : ℕ) (ε : ℝ) (hε : ε ≤ Real.pi / 2) :
    (∫ x in (-Real.pi)..Real.pi, tailMajorant L ε x) =
      (2 * Real.pi * (L : ℝ)) *
        (2 * ∫ u in (ε / 2)..(3 * Real.pi / 2), kernel L u) := by
  have hn : Continuous (fun x => ∫ u in (-(3 * Real.pi / 2))..(-ε / 2),
      kernel L u * kernel L (x - u)) :=
    continuous_interval_param (by fun_prop) _ _ (by linarith [Real.pi_pos])
  have hp : Continuous (fun x => ∫ u in (ε / 2)..(3 * Real.pi / 2),
      kernel L u * kernel L (x - u)) :=
    continuous_interval_param (by fun_prop) _ _ (by linarith [Real.pi_pos])
  unfold tailMajorant
  rw [intervalIntegral.integral_add (hn.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    interval_swap (f := fun x u => kernel L u * kernel L (x - u)) (by fun_prop)
      (-Real.pi) Real.pi (-(3 * Real.pi / 2)) (-ε / 2),
    interval_swap (f := fun x u => kernel L u * kernel L (x - u)) (by fun_prop)
      (-Real.pi) Real.pi (ε / 2) (3 * Real.pi / 2)]
  simp_rw [intervalIntegral.integral_const_mul, integral_kernel_sub,
    intervalIntegral.integral_mul_const]
  have he : (∫ u in (-(3 * Real.pi / 2))..(-ε / 2), kernel L u) =
      ∫ u in (ε / 2)..(3 * Real.pi / 2), kernel L u := by
    have he := intervalIntegral.integral_comp_neg (kernel L)
      (a := ε / 2) (b := 3 * Real.pi / 2)
    simpa only [kernel_even, neg_div] using he.symm
  rw [he]
  ring

private lemma tail_inner_bound (L : ℕ) (ε x : ℝ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.pi / 2) (hx : x ∈ Icc (-Real.pi) Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
      if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0
      else kernel L (x / 2 + y) * kernel L (x / 2 - y)) ≤
        2 * tailMajorant L ε x := by
  let p : ℝ → ℝ := fun y => kernel L (x / 2 + y) * kernel L (x / 2 - y)
  let q : ℝ → ℝ := fun y => if ε / 2 ≤ |x / 2 + y| then p y else 0
  let r : ℝ → ℝ := fun y => if ε / 2 ≤ |x / 2 - y| then p y else 0
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hn (y : ℝ) : 0 ≤ p y := mul_nonneg (kernel_nonneg _ _) (kernel_nonneg _ _)
  have hq : IntegrableOn q (Icc (-Real.pi) Real.pi) := by
    exact hp.integrableOn_Icc.indicator
      (isClosed_le continuous_const ((continuous_const.add continuous_id).abs)).measurableSet
  have hr : IntegrableOn r (Icc (-Real.pi) Real.pi) := by
    exact hp.integrableOn_Icc.indicator
      (isClosed_le continuous_const ((continuous_const.sub continuous_id).abs)).measurableSet
  have hqr : (∫ y in (-Real.pi)..Real.pi, r y) =
      ∫ y in (-Real.pi)..Real.pi, q y := by
    calc
      _ = ∫ y in (-Real.pi)..Real.pi, q (-y) := by
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp [q, r, p]
        simp only [← sub_eq_add_neg, sub_neg_eq_add, mul_comm]
      _ = _ := by
        simpa only [neg_neg] using intervalIntegral.integral_comp_neg q
          (a := -Real.pi) (b := Real.pi)
  have hqt : (∫ y in (-Real.pi)..Real.pi, q y) ≤ tailMajorant L ε x := by
    calc
      _ = ∫ y in (-Real.pi)..Real.pi,
          (fun u => if ε / 2 ≤ |u| then kernel L u * kernel L (x - u) else 0)
            (x / 2 + y) := by
        congr 1; ext y
        dsimp [q, p]
        congr 1
        congr 1
        congr 1
        ring
      _ = ∫ u in (x / 2 + -Real.pi)..(x / 2 + Real.pi),
          if ε / 2 ≤ |u| then kernel L u * kernel L (x - u) else 0 :=
        intervalIntegral.integral_comp_add_left
          (fun u => if ε / 2 ≤ |u| then kernel L u * kernel L (x - u) else 0) (x / 2)
      _ ≤ tailMajorant L ε x := by
        simpa only [tailMajorant, neg_div] using
          truncated_interval_le (f := fun u => kernel L u * kernel L (x - u))
            (by fun_prop) (fun u => mul_nonneg (kernel_nonneg _ _) (kernel_nonneg _ _))
            (x / 2 + -Real.pi) (x / 2 + Real.pi) (3 * Real.pi / 2) (ε / 2)
            (by linarith [Real.pi_pos]) (by linarith [hx.1]) (by linarith [hx.2])
            (by linarith) (by linarith [Real.pi_pos])
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    _ = ∫ y in Icc (-Real.pi) Real.pi,
        if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0 else p y := by
      rw [intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ y in Icc (-Real.pi) Real.pi, q y + r y := by
      apply setIntegral_mono_of_nonneg
      · intro y hy
        split_ifs
        · exact le_rfl
        · exact hn y
      · intro y hy
        by_cases hb : x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε
        · rw [ite_eq_left hb]
          exact add_nonneg (by dsimp only [q]; split_ifs; exact hn y; exact le_rfl)
            (by dsimp only [r]; split_ifs; exact hn y; exact le_rfl)
        · rw [ite_eq_right hb]
          by_cases ha : ε / 2 ≤ |x / 2 + y|
          · dsimp [q, r]
            rw [ite_eq_left ha]
            exact le_add_of_nonneg_right (by split_ifs; exact hn y; exact le_rfl)
          · have hb' : ε / 2 ≤ |x / 2 - y| := by
              by_contra hc
              have ha' := abs_lt.mp (lt_of_not_ge ha)
              have hc' := abs_lt.mp (lt_of_not_ge hc)
              exact hb ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
            dsimp [q, r]
            rw [ite_eq_right ha, ite_eq_left hb', zero_add]
      · exact hq.add hr
    _ = (∫ y in (-Real.pi)..Real.pi, q y) +
        ∫ y in (-Real.pi)..Real.pi, r y := by
      rw [integral_add hq hr]
      simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi]
    _ ≤ _ := by rw [hqr]; linarith

private lemma exterior_bound (M L : ℕ) (hL : 0 < L) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε ≤ Real.pi / 2) :
    (setIntegralR (Icc (-Real.pi) Real.pi) (fun φ1 =>
      setIntegralR (Icc (-Real.pi) Real.pi) (fun φ2 =>
        if φ1 ∈ Icc (-ε) ε ∧ φ2 ∈ Icc (-ε) ε then 0
        else (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L φ1 φ2‖ ^ 2))) ≤
      4 * Real.pi / ((L : ℝ) * ε) := by
  let C : ℝ := (1 / (4 * Real.pi ^ 2)) * (1 / (L : ℝ) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have heq (x y : ℝ) :
      (if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0
       else (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L x y‖ ^ 2) =
      C * (if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0
        else kernel L (x / 2 + y) * kernel L (x / 2 - y)) := by
    rw [kernel_ampA]
    dsimp [C]
    split_ifs <;> ring
  have hdom :
      (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
        if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0
        else kernel L (x / 2 + y) * kernel L (x / 2 - y)) ≤
      ∫ x in (-Real.pi)..Real.pi, 2 * tailMajorant L ε x := by
    rw [intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_mono_of_nonneg
    · intro x hx
      apply intervalIntegral.integral_nonneg hpi
      intro y hy
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (kernel_nonneg _ _) (kernel_nonneg _ _)
    · intro x hx
      exact tail_inner_bound L ε x hε0 hε hx
    · exact ((continuous_tailMajorant L ε hε).const_mul 2).integrableOn_Icc
  calc
    _ = C * (∫ x in (-Real.pi)..Real.pi, ∫ y in (-Real.pi)..Real.pi,
        if x ∈ Icc (-ε) ε ∧ y ∈ Icc (-ε) ε then 0
        else kernel L (x / 2 + y) * kernel L (x / 2 - y)) := by
      simp_rw [heq, setIntegralR_interval (-Real.pi) Real.pi hpi,
        intervalIntegral.integral_const_mul]
    _ ≤ C * (∫ x in (-Real.pi)..Real.pi, 2 * tailMajorant L ε x) :=
      mul_le_mul_of_nonneg_left hdom hC
    _ = C * (2 * ((2 * Real.pi * (L : ℝ)) *
        (2 * ∫ u in (ε / 2)..(3 * Real.pi / 2), kernel L u))) := by
      rw [intervalIntegral.integral_const_mul, integral_tailMajorant L ε hε]
    _ ≤ C * (2 * ((2 * Real.pi * (L : ℝ)) * (2 * (2 * Real.pi ^ 2 / ε)))) := by
      gcongr
      exact kernel_tail_integral L ε hε0 hε
    _ = _ := by
      dsimp [C]
      have hLne : (L : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hL)
      field_simp [Real.pi_ne_zero, hLne, ne_of_gt hε0]
      ring

private lemma normalization (M L : ℕ) (hL : 0 < L) :
    (setIntegralR (Icc (-Real.pi) Real.pi) (fun φ1 =>
      setIntegralR (Icc (-Real.pi) Real.pi) (fun φ2 =>
        (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L φ1 φ2‖ ^ 2))) = 1 := by
  simp_rw [setIntegralR_interval (-Real.pi) Real.pi (by linarith [Real.pi_pos]),
    kernel_ampA, mul_assoc, intervalIntegral.integral_const_mul]
  rw [integral_kernel_product]
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hL)
  field_simp [Real.pi_ne_zero, hLne]
  norm_num

private lemma interior_bound (M L : ℕ) (hL : 0 < L) (k ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < min (Real.pi - |k|) |k|) :
    (setIntegralR (Icc (-ε) ε) (fun φ1 =>
      setIntegralR (Icc (-ε) ε) (fun φ2 =>
        (1 / (4 * Real.pi ^ 2)) * ‖AmpB M L φ1 φ2 k‖ ^ 2))) ≤
      16 * Real.pi ^ 2 / ((L : ℝ) ^ 2 * ε ^ 2) := by
  let C : ℝ := (1 / (4 * Real.pi ^ 2)) * (1 / (L : ℝ) ^ 2) *
    (4 * Real.pi ^ 2 / ε ^ 2) ^ 2
  have hab : -ε ≤ ε := by linarith
  have hc : Continuous (fun p : ℝ × ℝ =>
      (1 / (4 * Real.pi ^ 2)) * ‖AmpB M L p.1 p.2 k‖ ^ 2) :=
    continuous_const.mul (continuous_ampB_sq M L k)
  have hpoint (φ1 φ2 : ℝ) (hφ1 : φ1 ∈ Icc (-ε) ε) (hφ2 : φ2 ∈ Icc (-ε) ε) :
      (1 / (4 * Real.pi ^ 2)) * ‖AmpB M L φ1 φ2 k‖ ^ 2 ≤ C := by
    have hm := kernel_shift_bound L k ε (φ2 + 2 * k - φ1 / 2) hε0 hε
      (abs_le.mpr ⟨by linarith [hφ1.1, hφ1.2, hφ2.1, hφ2.2],
        by linarith [hφ1.1, hφ1.2, hφ2.1, hφ2.2]⟩)
    have hp := kernel_shift_bound L k ε (φ2 + 2 * k + φ1 / 2) hε0 hε
      (abs_le.mpr ⟨by linarith [hφ1.1, hφ1.2, hφ2.1, hφ2.2],
        by linarith [hφ1.1, hφ1.2, hφ2.1, hφ2.2]⟩)
    rw [kernel_ampB]
    calc
      _ = ((1 / (4 * Real.pi ^ 2)) * (1 / (L : ℝ) ^ 2)) *
          (kernel L (φ2 + 2 * k - φ1 / 2) *
            kernel L (φ2 + 2 * k + φ1 / 2)) := by ring
      _ ≤ ((1 / (4 * Real.pi ^ 2)) * (1 / (L : ℝ) ^ 2)) *
          ((4 * Real.pi ^ 2 / ε ^ 2) * (4 * Real.pi ^ 2 / ε ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hm hp (kernel_nonneg L _) (by positivity)) (by positivity)
      _ = C := by dsimp [C]; ring
  simp_rw [setIntegralR_interval (-ε) ε hab]
  calc
    _ ≤ ∫ φ1 in (-ε)..ε, ∫ _φ2 in (-ε)..ε, C := by
      apply intervalIntegral.integral_mono_on hab
        ((continuous_interval_param (f := fun φ1 φ2 =>
          (1 / (4 * Real.pi ^ 2)) * ‖AmpB M L φ1 φ2 k‖ ^ 2)
          hc (-ε) ε hab).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro φ1 hφ1
      apply intervalIntegral.integral_mono_on hab
        ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
      intro φ2 hφ2
      exact hpoint φ1 φ2 hφ1 hφ2
    _ = _ := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      dsimp [C]
      have hLne : (L : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hL)
      field_simp [Real.pi_ne_zero, hLne, ne_of_gt hε0]
      norm_num

/-- **Lemma 5**: Parseval normalization and tail bounds for the Fourier kernels
`AmpA` and `AmpB`. -/
theorem source_lemma5
    (M L : ℕ) (hL : 0 < L) (k ε : ℝ)
    (hk : k ∈ Ioo (-Real.pi) 0 ∪ Ioo 0 Real.pi)
    (hε0 : 0 < ε) (hε : ε < min (Real.pi - |k|) |k|) :
    (setIntegralR (Icc (-Real.pi) Real.pi) (fun φ1 =>
        setIntegralR (Icc (-Real.pi) Real.pi) (fun φ2 =>
          (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L φ1 φ2‖ ^ 2)) = 1)
    ∧ (setIntegralR (Icc (-Real.pi) Real.pi) (fun φ1 =>
        setIntegralR (Icc (-Real.pi) Real.pi) (fun φ2 =>
          if φ1 ∈ Icc (-ε) ε ∧ φ2 ∈ Icc (-ε) ε then 0
          else (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L φ1 φ2‖ ^ 2))
        ≤ 4 * Real.pi / ((L : ℝ) * ε))
    ∧ (setIntegralR (Icc (-ε) ε) (fun φ1 =>
        setIntegralR (Icc (-ε) ε) (fun φ2 =>
          (1 / (4 * Real.pi ^ 2)) * ‖AmpB M L φ1 φ2 k‖ ^ 2))
        ≤ 16 * Real.pi ^ 2 / ((L : ℝ) ^ 2 * ε ^ 2)) := by
  refine (And.left (b := 0 < L ∧ k ∈ Ioo (-Real.pi) 0 ∪ Ioo 0 Real.pi ∧
    0 < ε ∧ ε < min (Real.pi - |k|) |k|) ⟨?_, ⟨hL, hk, hε0, hε⟩⟩)
  have hεpi : ε ≤ Real.pi / 2 := by
    have h₁ := (lt_min_iff.mp hε).1
    have h₂ := (lt_min_iff.mp hε).2
    linarith
  exact ⟨normalization M L hL, exterior_bound M L hL ε hε0 hεpi,
    interior_bound M L hL k ε hε0 hε⟩


end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
