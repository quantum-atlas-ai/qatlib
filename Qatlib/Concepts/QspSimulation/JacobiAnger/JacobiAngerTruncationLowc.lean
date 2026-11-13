/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationStat
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lc17AuxBessel
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.Roots

/-!
# Jacobi–Anger polynomial truncation

The polynomials `lcJAA` and `lcJAQt` express truncated Jacobi–Anger responses through Chebyshev
polynomials and Bessel coefficients. Their parity, degree, and trigonometric evaluation formulas
yield `jacobiAngerTruncation`, with uniform error at most 4τ^q/(2^q q!) for 0 ≤ τ ≤ q − 1, as in
[LowChuang2017].

## Main statements

* `lcJAA_even`: The cosine response polynomial is even.
* `lcJAQt_odd`: The sine response polynomial is odd.
* `jacobiAngerTruncation`: The truncated polynomial pair satisfies the required parity, degree,
  and error bounds.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.JacobiAnger

open Polynomial

section Helpers

/-- For real φ, exp(iφ) + exp(−iφ) equals 2 cos φ in ℂ. -/
private theorem lcExpAddCos (φ : ℝ) :
    Complex.exp (Complex.I * ((φ : ℝ) : ℂ)) + Complex.exp (-(Complex.I * ((φ : ℝ) : ℂ)))
      = 2 * ((Real.cos φ : ℝ) : ℂ) := by
  have h1 := Complex.exp_mul_I ((φ : ℝ) : ℂ)
  have h2 := Complex.exp_mul_I (-(φ : ℝ) : ℂ)
  have hn : -(Complex.I * ((φ : ℝ) : ℂ)) = (-(φ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, neg_mul]
  rw [hn, show Complex.I * ((φ : ℝ) : ℂ) = ((φ : ℝ) : ℂ) * Complex.I from mul_comm _ _,
    h1, h2, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- For real φ, exp(−iφ) − exp(iφ) equals −2i sin φ. -/
private theorem lcExpSubSin (φ : ℝ) :
    Complex.exp (-(Complex.I * ((φ : ℝ) : ℂ))) - Complex.exp (Complex.I * ((φ : ℝ) : ℂ))
      = -(2 * Complex.I * ((Real.sin φ : ℝ) : ℂ)) := by
  have h1 := Complex.exp_mul_I ((φ : ℝ) : ℂ)
  have h2 := Complex.exp_mul_I (-(φ : ℝ) : ℂ)
  have hn : -(Complex.I * ((φ : ℝ) : ℂ)) = (-(φ : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, neg_mul]
  rw [hn, show Complex.I * ((φ : ℝ) : ℂ) = ((φ : ℝ) : ℂ) * Complex.I from mul_comm _ _,
    h1, h2, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- Every even natural power of −1 in ℂ equals one. -/
private theorem lcNegOnePowEven (m : ℕ) : (-1 : ℂ) ^ (2 * m) = 1 := by
  rw [pow_mul, neg_one_pow_two, one_pow]

/-- Every odd natural power of −1 in ℂ equals −1. -/
private theorem lcNegOnePowOdd (m : ℕ) : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
  rw [pow_add, lcNegOnePowEven, pow_one, one_mul]

/-- The real polynomial 2X² − 1 is unchanged by substituting −X for X. -/
private theorem lcQ_even :
    ((2 * X ^ 2 - 1 : Polynomial ℝ)).comp (-(X : Polynomial ℝ))
      = (2 * X ^ 2 - 1 : Polynomial ℝ) := by
  refine Polynomial.funext fun x => ?_
  simp only [eval_comp, eval_neg, eval_X, eval_pow, eval_sub, eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_ofNat, Polynomial.eval_one]
  ring

/-- The natural degree of the real polynomial 2X² − 1 is at most two. -/
private theorem lcQ_natDegree : (2 * X ^ 2 - 1 : Polynomial ℝ).natDegree ≤ 2 := by
  have hEq : (2 * X ^ 2 - 1 : Polynomial ℝ)
      = (X : Polynomial ℝ) ^ 2 + (X : Polynomial ℝ) ^ 2 - 1 := by ring
  rw [hEq]
  refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
  have h1 : ((X : Polynomial ℝ) ^ 2 + (X : Polynomial ℝ) ^ 2).natDegree ≤ 2 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp only [Polynomial.natDegree_X_pow]
    omega
  have h2 : (1 : Polynomial ℝ).natDegree ≤ 2 := by simp
  omega

/-- The Chebyshev polynomial of index 2m composed with 2X² − 1 is even. -/
private theorem lcTQ_even (m : ℕ) :
    ((Polynomial.Chebyshev.T ℝ ((2 * m : ℕ) : ℤ)).comp (2 * X ^ 2 - 1 : Polynomial ℝ)).comp
        (-(X : Polynomial ℝ))
      = (Polynomial.Chebyshev.T ℝ ((2 * m : ℕ) : ℤ)).comp (2 * X ^ 2 - 1 : Polynomial ℝ) := by
  rw [Polynomial.comp_assoc, lcQ_even]

/-- Split a complex sum over k < q into its even-indexed and odd-indexed terms. -/
private theorem lcRangeEvenOdd {F : ℕ → ℂ} (q : ℕ) :
    ∑ k ∈ Finset.range q, F k
      = ∑ m ∈ Finset.range ((q + 1) / 2), F (2 * m)
        + ∑ m ∈ Finset.range (q / 2), F (2 * m + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rcases Nat.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩
    · have h1 : (q + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (q + 1) / 2 = m := by omega
      have hq3 : q / 2 = m := by omega
      rw [Finset.sum_range_succ, ih, h1, h2, hq3, hm,
        Finset.sum_range_succ (fun i => F (2 * i)) m, Nat.two_mul m]
      ring
    · have h1 : (q + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (q + 1) / 2 = m + 1 := by omega
      have hq3 : q / 2 = m := by omega
      rw [Finset.sum_range_succ, ih, h1, h2, hq3, hm,
        Finset.sum_range_succ (fun i => F (2 * i + 1)) m]
      ring

end Helpers

/-- The even Jacobi–Anger truncation polynomial formed from the coefficients 2J₂ₘ(τ) and
Chebyshev polynomials T₂ₘ(2X² − 1), with J₀(τ) subtracted. -/
private noncomputable def lcJAA (τ : ℝ) (q : ℕ) : Polynomial ℝ :=
  (∑ m ∈ Finset.range ((q + 1) / 2),
      Polynomial.C (2 * lcBesselJ (2 * m) τ)
        * ((Polynomial.Chebyshev.T ℝ ((2 * m : ℕ) : ℤ)).comp (2 * X ^ 2 - 1)))
    - Polynomial.C (lcBesselJ 0 τ)

/-- The odd Jacobi–Anger truncation polynomial formed by summing −4J₂ₘ₊₁(τ) times XU₂ₘ(2X² − 1)
over m < q/2. -/
private noncomputable def lcJAQt (τ : ℝ) (q : ℕ) : Polynomial ℝ :=
  ∑ m ∈ Finset.range (q / 2),
    Polynomial.C (-(4 * lcBesselJ (2 * m + 1) τ))
      * (X * ((Polynomial.Chebyshev.U ℝ ((2 * m : ℕ) : ℤ)).comp (2 * X ^ 2 - 1)))

/-- The polynomial `lcJAA τ q` is even. -/
private theorem lcJAA_even (τ : ℝ) (q : ℕ) :
    (lcJAA τ q).comp (-(X : Polynomial ℝ)) = lcJAA τ q := by
  rw [lcJAA, Polynomial.sub_comp, Polynomial.sum_comp, Polynomial.C_comp]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, lcTQ_even]

/-- The polynomial `lcJAQt τ q` is odd. -/
private theorem lcJAQt_odd (τ : ℝ) (q : ℕ) :
    (lcJAQt τ q).comp (-(X : Polynomial ℝ)) = -(lcJAQt τ q) := by
  rw [lcJAQt, Polynomial.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp,
    Polynomial.comp_assoc, lcQ_even, neg_mul, mul_neg]

/-- The degree of `lcJAA τ q` is at most 2(q − 1), with subtraction taken in ℕ. -/
private theorem lcJAA_degree (τ : ℝ) (q : ℕ) :
    (lcJAA τ q).degree ≤ ((2 * (q - 1) : ℕ) : WithBot ℕ) := by
  rw [lcJAA]
  refine le_trans (Polynomial.degree_sub_le _ _) ?_
  refine max_le ?_ ?_
  · refine le_trans (Polynomial.degree_sum_le _ _) ?_
    refine Finset.sup_le fun m hm => ?_
    have hm' : 2 * m ≤ q - 1 := by
      have h1 := Finset.mem_range.mp hm
      have h2 : m + 1 ≤ (q + 1) / 2 := h1
      have h3 : 2 * (m + 1) ≤ 2 * ((q + 1) / 2) := Nat.mul_le_mul_left 2 h2
      have h4 : 2 * ((q + 1) / 2) ≤ q + 1 := Nat.mul_div_le (q + 1) 2
      omega
    have hC : (Polynomial.C (2 * lcBesselJ (2 * m) τ)).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_C]
    have hT : ((Polynomial.Chebyshev.T ℝ ((2 * m : ℕ) : ℤ)).comp
        (2 * X ^ 2 - 1 : Polynomial ℝ)).natDegree ≤ 2 * (2 * m) := by
      refine le_trans Polynomial.natDegree_comp_le ?_
      rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      refine le_trans (mul_le_mul_right lcQ_natDegree (2 * m)) ?_
      omega
    refine le_trans (Polynomial.degree_le_of_natDegree_le
      (show (Polynomial.C (2 * lcBesselJ (2 * m) τ)
          * ((Polynomial.Chebyshev.T ℝ ((2 * m : ℕ) : ℤ)).comp
              (2 * X ^ 2 - 1 : Polynomial ℝ))).natDegree ≤ 2 * (q - 1) from by
        exact le_trans (Polynomial.natDegree_mul_le) (by omega))) ?_
    exact_mod_cast (by omega : (2 * (q - 1) : ℕ) ≤ 2 * (q - 1))
  · have h0 : (Polynomial.C (lcBesselJ 0 τ)).degree ≤ (0 : WithBot ℕ) :=
      Polynomial.degree_C_le
    exact le_trans h0 (by exact_mod_cast (by omega : (0 : ℕ) ≤ 2 * (q - 1)))

/-- The degree of `lcJAQt τ q` is strictly below 2(q − 1), with subtraction taken in ℕ. -/
private theorem lcJAQt_degree (τ : ℝ) (q : ℕ) :
    (lcJAQt τ q).degree < ((2 * (q - 1) : ℕ) : WithBot ℕ) := by
  rcases le_or_gt q 1 with hq | hq
  · have hr : q / 2 = 0 := by omega
    rw [lcJAQt, hr, Finset.range_zero, Finset.sum_empty]
    simp only [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · rw [lcJAQt]
    have hsup : (Finset.sup (Finset.range (q / 2)) fun m =>
        (Polynomial.C (-(4 * lcBesselJ (2 * m + 1) τ))
          * (X * ((Polynomial.Chebyshev.U ℝ ((2 * m : ℕ) : ℤ)).comp
              (2 * X ^ 2 - 1 : Polynomial ℝ)))).degree) ≤ ((2 * q - 3 : ℕ) : WithBot ℕ) := by
      refine Finset.sup_le fun m hm => ?_
      have hm' : 2 * m + 1 ≤ q - 1 := by
        have h1 := Finset.mem_range.mp hm
        have h2 : m + 1 ≤ q / 2 := h1
        have h3 : 2 * (m + 1) ≤ 2 * (q / 2) := Nat.mul_le_mul_left 2 h2
        have h4 : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
        omega
      have hC : (Polynomial.C (-(4 * lcBesselJ (2 * m + 1) τ))).natDegree ≤ 0 := by
        rw [Polynomial.natDegree_C]
      have hXU : (X * ((Polynomial.Chebyshev.U ℝ ((2 * m : ℕ) : ℤ)).comp
          (2 * X ^ 2 - 1 : Polynomial ℝ))).natDegree ≤ 2 * (2 * m) + 1 := by
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        have hX : (X : Polynomial ℝ).natDegree ≤ 1 := by
          rw [Polynomial.natDegree_X]
        have hU : ((Polynomial.Chebyshev.U ℝ ((2 * m : ℕ) : ℤ)).comp
            (2 * X ^ 2 - 1 : Polynomial ℝ)).natDegree ≤ 2 * (2 * m) := by
          refine le_trans Polynomial.natDegree_comp_le ?_
          rw [Polynomial.Chebyshev.natDegree_U_natCast]
          refine le_trans (mul_le_mul_right lcQ_natDegree (2 * m)) ?_
          omega
        omega
      refine le_trans (Polynomial.degree_le_of_natDegree_le
        (show (Polynomial.C (-(4 * lcBesselJ (2 * m + 1) τ))
            * (X * ((Polynomial.Chebyshev.U ℝ ((2 * m : ℕ) : ℤ)).comp
                (2 * X ^ 2 - 1 : Polynomial ℝ)))).natDegree ≤ 2 * q - 3 from by
          exact le_trans (Polynomial.natDegree_mul_le) (by omega))) ?_
      exact_mod_cast (by omega : (2 * q - 3 : ℕ) ≤ 2 * q - 3)
    refine lt_of_le_of_lt (le_trans (Polynomial.degree_sum_le _ _) hsup) ?_
    exact_mod_cast (by omega : 2 * q - 3 < 2 * (q - 1))

/-- Evaluating `lcJAA τ q` at cos(θ/2) gives the finite sum of 2J₂ₘ(τ) cos(2mθ), with J₀(τ)
subtracted. -/
private theorem lcJAA_eval (τ : ℝ) (q : ℕ) (θ : ℝ) :
    (lcJAA τ q).eval (Real.cos (θ / 2))
      = (∑ m ∈ Finset.range ((q + 1) / 2),
          2 * lcBesselJ (2 * m) τ * Real.cos (((2 * m : ℕ) : ℝ) * θ))
        - lcBesselJ 0 τ := by
  have hcosθ : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at h
    exact h
  have hQeval : (2 * X ^ 2 - 1 : Polynomial ℝ).eval (Real.cos (θ / 2)) = Real.cos θ := by
    simp only [eval_sub, eval_mul, eval_pow, eval_X, Polynomial.eval_natCast,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    rw [hcosθ]
  rw [lcJAA, eval_sub, Polynomial.eval_finsetSum, eval_C]
  simp only [eval_mul, eval_C, eval_comp]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hQeval, Polynomial.Chebyshev.T_real_cos]
  push_cast
  ring

/-- Multiplying the value of `lcJAQt τ q` at cos(θ/2) by sin(θ/2) gives the finite sum of
−2J₂ₘ₊₁(τ) sin((2m + 1)θ). -/
private theorem lcJAQt_sinmul_eval (τ : ℝ) (q : ℕ) (θ : ℝ) :
    Real.sin (θ / 2) * (lcJAQt τ q).eval (Real.cos (θ / 2))
      = ∑ m ∈ Finset.range (q / 2),
          -(2 * lcBesselJ (2 * m + 1) τ) * Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ) := by
  have hcosθ : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at h
    exact h
  have hsinθ : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    have h := Real.sin_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring] at h
    exact h
  have hQeval : (2 * X ^ 2 - 1 : Polynomial ℝ).eval (Real.cos (θ / 2)) = Real.cos θ := by
    simp only [eval_sub, eval_mul, eval_pow, eval_X, Polynomial.eval_natCast,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    rw [hcosθ]
  rw [lcJAQt, Polynomial.eval_finsetSum, Finset.mul_sum]
  simp only [eval_mul, eval_C, eval_comp, eval_X]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hQeval]
  have hU := Polynomial.Chebyshev.U_real_cos θ ((2 * m : ℕ) : ℤ)
  rw [hsinθ] at hU
  push_cast at hU ⊢
  rw [← hU]
  ring

/-- For real φ, exp(−iφ) + exp(iφ) equals 2 cos φ in ℂ. -/
private theorem lcExpCosPair (φ : ℝ) :
    Complex.exp (-(Complex.I * ((φ : ℝ) : ℂ))) + Complex.exp (Complex.I * ((φ : ℝ) : ℂ))
      = 2 * ((Real.cos φ : ℝ) : ℂ) := by
  rw [add_comm, lcExpAddCos]

/-- For q ≥ 1, the complex response formed from `lcJAA` and `lcJAQt` equals the sum of the
positive and negative Jacobi–Anger terms with indices below q, counting the zero term once. -/
private theorem lcAmp_eq (τ : ℝ) (q : ℕ) (hq : 1 ≤ q) (θ : ℝ) :
    Complex.ofReal ((lcJAA τ q).eval (Real.cos (θ / 2)))
      + Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ)
        * Complex.ofReal ((lcJAQt τ q).eval (Real.cos (θ / 2)))
      = ∑ k ∈ Finset.range q, (lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) := by

  have hEv : ∀ m ∈ Finset.range ((q + 1) / 2),
      (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (2 * m)
        = ((2 * lcBesselJ (2 * m) τ * Real.cos (((2 * m : ℕ) : ℝ) * θ) : ℝ) : ℂ)
          + (if m = 0 then (-(lcBesselJ 0 τ : ℝ) : ℂ) else 0) := by
    intro m _
    rcases eq_or_ne m 0 with rfl | hm0
    · show lcJAp τ θ (2 * 0) + (if 2 * 0 = 0 then 0 else lcJAn τ θ (2 * 0)) = _
      have h20 : (2 * 0 : ℕ) = 0 := by omega
      rw [h20, if_pos rfl, if_pos rfl, lcJAp]
      simp only [Nat.cast_zero, zero_mul, mul_zero, neg_zero,
        Complex.exp_zero, Real.cos_zero, mul_one]
      push_cast
      ring
    · have hm2 : 2 * m ≠ 0 := by omega
      show lcJAp τ θ (2 * m) + (if 2 * m = 0 then 0 else lcJAn τ θ (2 * m)) = _
      rw [if_neg hm2, if_neg hm0, lcJAp, lcJAn, lcNegOnePowEven m, one_mul]
      rw [show (((2 * m : ℕ) : ℂ) * ((θ : ℝ) : ℂ))
            = ((((2 * m : ℕ) : ℝ) * θ : ℝ) : ℂ) from by
          push_cast
          ring]
      rw [← mul_add, lcExpCosPair (((2 * m : ℕ) : ℝ) * θ), add_zero]
      rw [show ((lcBesselJ (2 * m) τ : ℝ) : ℂ)
            * (2 * ((Real.cos (((2 * m : ℕ) : ℝ) * θ) : ℝ) : ℂ))
            = ((2 * lcBesselJ (2 * m) τ
                * Real.cos (((2 * m : ℕ) : ℝ) * θ) : ℝ) : ℂ) from by
          rw [Complex.ofReal_mul, Complex.ofReal_mul]
          push_cast
          ring]

  have hOd : ∀ m ∈ Finset.range (q / 2),
      (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (2 * m + 1)
        = Complex.I * ((-(2 * lcBesselJ (2 * m + 1) τ)
            * Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
    intro m _
    have hm2 : 2 * m + 1 ≠ 0 := by omega
    show lcJAp τ θ (2 * m + 1)
        + (if 2 * m + 1 = 0 then 0 else lcJAn τ θ (2 * m + 1)) = _
    rw [if_neg hm2, lcJAp, lcJAn, lcNegOnePowOdd m, neg_one_mul, neg_mul, ← sub_eq_add_neg]
    rw [show (((2 * m + 1 : ℕ) : ℂ) * ((θ : ℝ) : ℂ))
          = ((((2 * m + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) from by
        push_cast
        ring]
    rw [← mul_sub, lcExpSubSin (((2 * m + 1 : ℕ) : ℝ) * θ)]
    rw [show ((lcBesselJ (2 * m + 1) τ : ℝ) : ℂ)
          * (-(2 * Complex.I * ((Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ)))
          = Complex.I * ((-(2 * lcBesselJ (2 * m + 1) τ)
              * Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) from by
        rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_mul]
        push_cast
        ring]

  have hzero : (0 : ℕ) ∈ Finset.range ((q + 1) / 2) := by
    simp only [Finset.mem_range]
    omega
  have hcorr : ∑ m ∈ Finset.range ((q + 1) / 2),
      (if m = 0 then (-(lcBesselJ 0 τ : ℝ) : ℂ) else 0)
      = -((lcBesselJ 0 τ : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb])
      (fun hn => absurd hzero hn), if_pos rfl]
  have hR : (∑ m ∈ Finset.range ((q + 1) / 2),
        ((2 * lcBesselJ (2 * m) τ * Real.cos (((2 * m : ℕ) : ℝ) * θ) : ℝ) : ℂ))
      - ((lcBesselJ 0 τ : ℝ) : ℂ)
      = ∑ m ∈ Finset.range ((q + 1) / 2),
        (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (2 * m) := by
    have hsum : ∑ m ∈ Finset.range ((q + 1) / 2),
        (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (2 * m)
      = (∑ m ∈ Finset.range ((q + 1) / 2),
          ((2 * lcBesselJ (2 * m) τ * Real.cos (((2 * m : ℕ) : ℝ) * θ) : ℝ) : ℂ))
        + ∑ m ∈ Finset.range ((q + 1) / 2),
          (if m = 0 then (-(lcBesselJ 0 τ : ℝ) : ℂ) else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m hm => hEv m hm
    rw [hsum, hcorr, sub_eq_add_neg]
  have hR' : Complex.I * (((∑ m ∈ Finset.range (q / 2),
          (-(2 * lcBesselJ (2 * m + 1) τ)
            * Real.sin (((2 * m + 1 : ℕ) : ℝ) * θ))) : ℝ) : ℂ)
      = ∑ m ∈ Finset.range (q / 2),
        (fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) (2 * m + 1) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m hm => (hOd m hm).symm
  rw [lcRangeEvenOdd (F := fun k => lcJAp τ θ k + (if k = 0 then 0 else lcJAn τ θ k)) q,
    mul_assoc, ← Complex.ofReal_mul, lcJAA_eval, lcJAQt_sinmul_eval,
    Complex.ofReal_sub, Complex.ofReal_sum, hR, hR']

/-- For q ≥ 1 and 0 ≤ τ ≤ q − 1, there are even and odd real polynomials with degrees
respectively at most and strictly below 2(q − 1) whose trigonometric response approximates
exp(−iτ sin θ) within 4τ^q/(2^q q!). This is the truncation guarantee associated with [Low
and Chuang, Eqs. (16)–(17)][LowChuang2017]. -/
theorem jacobiAngerTruncation : JacobiAngerTruncation := by
  intro q τ hq hτ0 hτle
  refine ⟨lcJAA τ q, lcJAQt τ q, lcJAA_even τ q, lcJAQt_odd τ q,
    lcJAA_degree τ q, lcJAQt_degree τ q, ?_⟩
  intro θ _
  rw [realEval, realEval, map_eval_ofReal, map_eval_ofReal, lcAmp_eq τ q hq θ,
    norm_sub_rev, Real.rpow_natCast τ q, Real.rpow_natCast 2 q]
  exact lcBesselJacobiAnger_tail q τ θ hτ0 hτle

end Qatlib.Concepts.QspSimulation.JacobiAnger
