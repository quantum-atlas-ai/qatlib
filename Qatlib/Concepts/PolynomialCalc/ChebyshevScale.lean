/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Concepts.PolynomialCalc.ChebyshevScale

def hyperbolicScale (y x : ℝ) : ℝ := Real.cosh (y*Real.arcosh x)

def bandWidth (ε : ℝ) (k : ℕ) : ℝ :=
  (hyperbolicScale ((k : ℝ))⁻¹ (1/ε)-1)/hyperbolicScale ((k : ℝ))⁻¹ (1/ε)

def DefinedParity (p : Polynomial ℝ) : Prop :=
  (∀ x : ℝ,p.eval (-x)=p.eval x) ∨ (∀ x : ℝ,p.eval (-x)= -p.eval x)

def AdmissibleFilter (ε : ℝ) (k : ℕ) (p : Polynomial ℝ) : Prop :=
  DefinedParity p ∧ (∀ x : ℝ,p.IsRoot x → -1<x ∧ x<1) ∧ p.eval 1=1 ∧
    (∀ x : ℝ,-1+bandWidth ε k≤x → x≤1-bandWidth ε k → |p.eval x|≤ε)

def filterPolynomial (ε : ℝ) (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ε*(Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (Polynomial.C (hyperbolicScale ((k : ℝ))⁻¹ (1/ε))*Polynomial.X)

def filterValue (ε : ℝ) (k : ℕ) : ℝ → ℝ := (filterPolynomial ε k).eval

lemma abs_T_le_one_of_abs_le_one (n : ℤ) (y : ℝ) (hy : |y| ≤ 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval y| ≤ 1 := by
  have hcos : (Polynomial.Chebyshev.T ℝ n).eval y
      = Real.cos ((n : ℝ) * Real.arccos y) := by
    have h := Polynomial.Chebyshev.T_real_cos (Real.arccos y) n
    obtain ⟨hm, hM⟩ := abs_le.mp hy
    rwa [Real.cos_arccos hm hM] at h
  rw [hcos]
  exact Real.abs_cos_le_one _

lemma abs_T_le_T_of_one_le (n : ℤ) (hn : 0 ≤ n) {c y : ℝ}
    (hc : 1 ≤ c) (hy : 1 ≤ y) (hyc : y ≤ c) :
    |(Polynomial.Chebyshev.T ℝ n).eval y| ≤ (Polynomial.Chebyshev.T ℝ n).eval c := by
  have hnn : 0 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcT : (Polynomial.Chebyshev.T ℝ n).eval c
      = Real.cosh ((n : ℝ) * Real.arcosh c) := by
    have h := Polynomial.Chebyshev.T_real_cosh (Real.arcosh c) n
    rwa [Real.cosh_arcosh hc] at h
  have hyT : (Polynomial.Chebyshev.T ℝ n).eval y
      = Real.cosh ((n : ℝ) * Real.arcosh y) := by
    have h := Polynomial.Chebyshev.T_real_cosh (Real.arcosh y) n
    rwa [Real.cosh_arcosh hy] at h
  have hypos' : 0 < y := by linarith
  have hcpos : 0 < c := by linarith
  have hyarc : Real.arcosh y ≤ Real.arcosh c :=
    (Real.arcosh_le_arcosh hypos' hcpos).2 hyc
  have t1 : 0 ≤ (n : ℝ) * Real.arcosh y :=
    mul_nonneg hnn (Real.arcosh_nonneg hy)
  have t2 : 0 ≤ (n : ℝ) * Real.arcosh c :=
    mul_nonneg hnn (Real.arcosh_nonneg hc)
  rw [hyT, hcT, abs_of_nonneg (by positivity), Real.cosh_le_cosh,
    abs_of_nonneg t1, abs_of_nonneg t2]
  exact mul_le_mul_of_nonneg_left hyarc hnn

lemma abs_T_le_T_of_abs_le (n : ℤ) (hn : 0 ≤ n) {c y : ℝ}
    (hc : 1 ≤ c) (hy : |y| ≤ c) :
    |(Polynomial.Chebyshev.T ℝ n).eval y| ≤ (Polynomial.Chebyshev.T ℝ n).eval c := by
  have hcT : (Polynomial.Chebyshev.T ℝ n).eval c
      = Real.cosh ((n : ℝ) * Real.arcosh c) := by
    have h := Polynomial.Chebyshev.T_real_cosh (Real.arcosh c) n
    rwa [Real.cosh_arcosh hc] at h
  have h1c : 1 ≤ (Polynomial.Chebyshev.T ℝ n).eval c := by
    rw [hcT]; exact Real.one_le_cosh _
  by_cases hle : |y| ≤ 1
  · exact (abs_T_le_one_of_abs_le_one n y hle).trans h1c
  · push Not at hle
    by_cases hypos : 0 ≤ y
    · have habs : |y| = y := abs_of_nonneg hypos
      have hy1 : 1 ≤ y := by linarith
      have hyc : y ≤ c := by linarith
      exact abs_T_le_T_of_one_le n hn hc hy1 hyc
    · push Not at hypos
      have hyn : y ≤ 0 := le_of_lt hypos
      have habs : |y| = -y := abs_of_nonpos hyn
      have hy1 : 1 ≤ -y := by linarith
      have hnyc : -y ≤ c := by linarith
      have hev : |(Polynomial.Chebyshev.T ℝ n).eval y|
          = |(Polynomial.Chebyshev.T ℝ n).eval (-y)| := by
        have h := Polynomial.Chebyshev.T_eval_neg ℝ n (-y)
        rw [neg_neg] at h
        rw [h, abs_mul]
        simp
      rw [hev]
      exact abs_T_le_T_of_one_le n hn hc hy1 hnyc

lemma chebPoly_eval (ε : ℝ) (d : ℕ) (x : ℝ) :
    (filterPolynomial ε d).eval x
      = ε * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (hyperbolicScale ((d : ℝ))⁻¹ (1 / ε) * x) := by
  rw [filterPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

lemma eval_T_band_const (ε : ℝ) (d : ℕ) (hd : d ≠ 0) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (hyperbolicScale ((d : ℝ))⁻¹ (1 / ε)) = 1 / ε := by
  have hu : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]; rw [one_mul]; exact hε1
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hdcast : (((d : ℤ) : ℝ)) = ((d : ℝ)) := by exact_mod_cast rfl
  have hc : Real.cosh (((d : ℝ))⁻¹ * Real.arcosh (1 / ε))
      = hyperbolicScale ((d : ℝ))⁻¹ (1 / ε) := rfl
  have h := Polynomial.Chebyshev.T_real_cosh (((d : ℝ))⁻¹ * Real.arcosh (1 / ε)) (d : ℤ)
  rw [← hc, h, ← mul_assoc, hdcast, mul_inv_cancel₀ hdn, one_mul, Real.cosh_arcosh hu]

theorem filter_interval_max (ε : ℝ) (d : ℕ) (hε0 : 0<ε) (hε1 : ε≤1) (hd : 1≤d) :
    sSup (Set.range (fun x : {x : ℝ // |x|≤1} => |filterValue ε d x.1|))=1 := by

  have hu : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε0]; rw [one_mul]; exact hε1
  set c := hyperbolicScale ((d : ℝ))⁻¹ (1 / ε) with hcdef
  have hcosh : Real.cosh (((d : ℝ))⁻¹ * Real.arcosh (1 / ε)) = c := rfl
  have hc1 : 1 ≤ c := by rw [← hcosh]; exact Real.one_le_cosh _
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hdn : (d : ℝ) ≠ 0 := by positivity
  have hdz : 0 ≤ (d : ℤ) := by exact_mod_cast (Nat.zero_le d)
  have hdcast : (((d : ℤ) : ℝ)) = ((d : ℝ)) := by exact_mod_cast rfl

  have hTc : (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval c = 1 / ε := by
    have h := Polynomial.Chebyshev.T_real_cosh (((d : ℝ))⁻¹ * Real.arcosh (1 / ε)) (d : ℤ)
    rw [hcosh] at h
    rw [h, ← mul_assoc, hdcast, mul_inv_cancel₀ hdn, one_mul, Real.cosh_arcosh hu]

  have hup : ∀ t : ℝ, filterValue ε d t
      = ε * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (c * t) := by
    intro t
    show (filterPolynomial ε d).eval t = _
    rw [chebPoly_eval, ← hcdef]
  have hbound : ∀ t : ℝ, |t| ≤ 1 → |filterValue ε d t| ≤ 1 := by
    intro t ht
    have hy : |c * t| ≤ c := by
      rw [abs_mul, abs_of_pos hc0]
      simpa using mul_le_mul_of_nonneg_left ht hc0.le
    rw [hup t, abs_mul, abs_of_pos hε0]
    calc ε * |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (c * t)|
        ≤ ε * (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval c :=
          mul_le_mul_of_nonneg_left (abs_T_le_T_of_abs_le _ hdz hc1 hy) hε0.le
      _ = 1 := by rw [hTc]; field_simp
  have hval1 : filterValue ε d 1 = 1 := by
    rw [hup 1, mul_one, hTc]; field_simp

  set D : Set ℝ := Set.range (fun x : {x : ℝ // |x| ≤ 1} => |filterValue ε d x.1|) with hD
  have hDbd : BddAbove D := ⟨1, by rintro _ ⟨x, rfl⟩; exact hbound x.1 x.2⟩
  have hDne : D.Nonempty := ⟨|filterValue ε d 0|, ⟨⟨0, by simp⟩, rfl⟩⟩
  have hDsup : sSup D = 1 := by
    refine le_antisymm (csSup_le hDne ?_) ?_
    · rintro _ ⟨x, rfl⟩; exact hbound x.1 x.2
    · refine le_csSup hDbd ⟨⟨1, abs_le.2 ⟨by norm_num, by norm_num⟩⟩, ?_⟩
      show |filterValue ε d 1| = 1
      rw [hval1, abs_one]
  exact hDsup
end Qatlib.Concepts.PolynomialCalc.ChebyshevScale
