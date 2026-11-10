/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ChebyshevDifferenceBoundStat
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT

open Polynomial Polynomial.Chebyshev Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open scoped Classical BigOperators

private theorem chebT_eq_eval (x : ℝ) (k : ℕ) :
    ((chebT x k : ℝ) : ℂ) = (T ℂ (k : ℤ)).eval (x : ℂ) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [chebT]
  | one => simp [chebT]
  | more k ih1 ih2 =>
    have hk2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
    have hk1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
    rw [hk1] at ih2
    have hcheb : chebT x (k + 2) = 2 * x * chebT x (k + 1) - chebT x k := rfl
    rw [hcheb, hk2, T_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    rw [← ih2, ← ih1]
    push_cast
    ring

private theorem two_mul_T_eq_U_sub (n : ℤ) :
    2 * T ℂ n = U ℂ n - U ℂ (n - 2) := by
  have h := two_mul_T_eq_U_sub_U ℂ (n - 2)
  have h1 : (n - 2 + 2 : ℤ) = n := by omega
  rw [h1] at h
  exact h

private def tVal (x : ℝ) (k : ℕ) : ℂ :=
  if k = 0 then (1 / 2 : ℂ) else (chebT x k : ℂ)

private theorem chebT_eq_half_U (x : ℝ) (k : ℕ) :
    ((chebT x k : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ((U ℂ (k : ℤ)).eval (x : ℂ) - (U ℂ ((k : ℤ) - 2)).eval (x : ℂ)) := by
  rw [chebT_eq_eval]
  have h := congr_arg (fun p : ℂ[X] => p.eval (x : ℂ)) (two_mul_T_eq_U_sub (k : ℤ))
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat] at h
  calc (T ℂ (k : ℤ)).eval (x : ℂ)
      = ((2 : ℂ) * (T ℂ (k : ℤ)).eval (x : ℂ)) / 2 := by ring
    _ = ((U ℂ (k : ℤ)).eval (x : ℂ) - (U ℂ ((k : ℤ) - 2)).eval (x : ℂ)) / 2 := by rw [h]
    _ = (1 / 2 : ℂ) * ((U ℂ (k : ℤ)).eval (x : ℂ) - (U ℂ ((k : ℤ) - 2)).eval (x : ℂ)) := by
        ring

private theorem tVal_eq_half_U (x : ℝ) (k : ℕ) :
    tVal x k = (1 / 2 : ℂ) * ((U ℂ (k : ℤ)).eval (x : ℂ)
      - (if k = 0 then (0 : ℂ) else (U ℂ ((k : ℤ) - 2)).eval (x : ℂ))) := by
  unfold tVal
  by_cases hk : k = 0
  · subst hk
    simp only [if_true]
    have hU : (U ℂ ((0 : ℕ) : ℤ)).eval (x : ℂ) = 1 := by
      have h0 : ((0 : ℕ) : ℤ) = 0 := by norm_cast
      rw [h0, U_zero]
      simp
    rw [hU]
    norm_num
  · rw [if_neg hk, if_neg hk, chebT_eq_half_U]

private theorem extendCoefficient_of_not_lt {n : ℕ} (c : Fin n → ℂ) (k : ℕ)
    (h : ¬(k < n)) : extendCoefficient c k = 0 := by
  show (if _ : k < n then _ else 0) = 0
  rw [dif_neg h]

private theorem extendCoefficient_eq {n : ℕ} (c : Fin n → ℂ) (k : ℕ) (h : k < n) :
    extendCoefficient c k = c ⟨k, h⟩ := by
  show (if _ : k < n then _ else 0) = _
  rw [dif_pos h]

private theorem c_eq_extend {n : ℕ} (c : Fin n → ℂ) (k : Fin n) :
    c k = extendCoefficient c k.val :=
  (extendCoefficient_eq c k.val k.isLt).symm

private theorem sum_extend_shift_range {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    (∑ m ∈ Finset.range n, extendCoefficient c m *
        (if m = 0 then (0 : ℂ) else (U ℂ ((m : ℤ) - 2)).eval (x : ℂ)))
      = ∑ m ∈ Finset.range n, extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ) := by
  have hR : (∑ m ∈ Finset.range n, extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ))
      = ∑ m ∈ Finset.range (n - 2), extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ) := by
    refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hkn => ?_)).symm
    · simp only [Finset.mem_range] at hk ⊢
      omega
    · simp only [Finset.mem_range] at hk hkn
      have hnk : ¬(k + 2 < n) := by omega
      rw [extendCoefficient_of_not_lt c (k + 2) hnk, zero_mul]
  have hL : (∑ m ∈ Finset.range n, extendCoefficient c m *
        (if m = 0 then (0 : ℂ) else (U ℂ ((m : ℤ) - 2)).eval (x : ℂ)))
      = ∑ m ∈ Finset.range (n - 2), extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ) := by
    by_cases hn : n ≤ 2
    · have h0 : n - 2 = 0 := by omega
      rw [h0, Finset.range_zero, Finset.sum_empty]
      interval_cases n
      · simp
      · rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        simp
      · have g0 : extendCoefficient c 0 *
            (if (0 : ℕ) = 0 then (0 : ℂ) else (U ℂ (((0 : ℕ) : ℤ) - 2)).eval (x : ℂ)) = 0 := by
          simp
        have g1 : extendCoefficient c 1 *
            (if (1 : ℕ) = 0 then (0 : ℂ) else (U ℂ (((1 : ℕ) : ℤ) - 2)).eval (x : ℂ)) = 0 := by
          have hcast : ((1 : ℕ) : ℤ) - 2 = (-1 : ℤ) := by norm_cast
          rw [hcast, U_neg_one]
          simp
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp
    · have h2 : 2 ≤ n := by omega
      have hsplit : 2 + (n - 2) = n := by omega
      have hsum := Finset.sum_range_add
        (fun m => extendCoefficient c m *
          (if m = 0 then (0 : ℂ) else (U ℂ ((m : ℤ) - 2)).eval (x : ℂ))) 2 (n - 2)
      rw [hsplit] at hsum
      have hhead : (∑ m ∈ Finset.range 2, extendCoefficient c m *
          (if m = 0 then (0 : ℂ) else (U ℂ ((m : ℤ) - 2)).eval (x : ℂ))) = 0 := by
        have g0 : extendCoefficient c 0 *
            (if (0 : ℕ) = 0 then (0 : ℂ) else (U ℂ (((0 : ℕ) : ℤ) - 2)).eval (x : ℂ)) = 0 := by
          simp
        have g1 : extendCoefficient c 1 *
            (if (1 : ℕ) = 0 then (0 : ℂ) else (U ℂ (((1 : ℕ) : ℤ) - 2)).eval (x : ℂ)) = 0 := by
          have hcast : ((1 : ℕ) : ℤ) - 2 = (-1 : ℤ) := by norm_cast
          rw [hcast, U_neg_one]
          simp
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp
      have htail : (∑ m ∈ Finset.range (n - 2), extendCoefficient c (2 + m) *
          (if (2 + m) = 0 then (0 : ℂ) else (U ℂ (((2 + m : ℕ) : ℤ) - 2)).eval (x : ℂ)))
          = ∑ m ∈ Finset.range (n - 2), extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm2 : (2 + m : ℕ) ≠ 0 := by omega
        rw [if_neg hm2]
        have hcast : (((2 + m : ℕ) : ℤ) - 2) = (m : ℤ) := by push_cast; omega
        have hadd : (2 + m : ℕ) = m + 2 := by omega
        rw [hcast, hadd]
      rw [hsum, hhead, zero_add]
      exact htail
  rw [hL, hR]

private theorem sum_extend_shift {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    (∑ k : Fin n, extendCoefficient c k.val *
        (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)))
      = ∑ k : Fin n, extendCoefficient c (k.val + 2) * (U ℂ (k.val : ℤ)).eval (x : ℂ) := by
  set f : ℕ → ℂ := fun m => extendCoefficient c m *
    (if m = 0 then (0 : ℂ) else (U ℂ ((m : ℤ) - 2)).eval (x : ℂ))
  set g : ℕ → ℂ := fun m => extendCoefficient c (m + 2) * (U ℂ (m : ℤ)).eval (x : ℂ)
  have hL : (∑ k : Fin n, f k.val) = ∑ m ∈ Finset.range n, f m :=
    Fin.sum_univ_eq_sum_range f n
  have hR : (∑ k : Fin n, g k.val) = ∑ m ∈ Finset.range n, g m :=
    Fin.sum_univ_eq_sum_range g n
  have hL' : (∑ k : Fin n, extendCoefficient c k.val *
      (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)))
      = ∑ k : Fin n, f k.val := by
    apply Finset.sum_congr rfl
    intro k _
    rfl
  have hR' : (∑ k : Fin n, extendCoefficient c (k.val + 2) * (U ℂ (k.val : ℤ)).eval (x : ℂ))
      = ∑ k : Fin n, g k.val := by
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [hL', hL, hR', hR]
  exact sum_extend_shift_range c x

private theorem chebValue_eq_sum_diffU {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    chebValue c x = (1 / 2 : ℂ) *
        ∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) * (U ℂ (k.val : ℤ)).eval (x : ℂ) := by
  have hcv : chebValue c x = ∑ k : Fin n, c k * tVal x k.val := by
    rw [chebValue]
    exact Finset.sum_congr rfl (fun k _ => rfl)
  rw [hcv]
  have ht : ∀ k : Fin n, c k * tVal x k.val
      = (1 / 2 : ℂ) * (c k * ((U ℂ (k.val : ℤ)).eval (x : ℂ)
        - (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)))) := by
    intro k
    rw [tVal_eq_half_U]
    ring
  rw [show (∑ k : Fin n, c k * tVal x k.val)
      = ∑ k : Fin n, (1 / 2 : ℂ) * (c k * ((U ℂ (k.val : ℤ)).eval (x : ℂ)
        - (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ))))
      from Finset.sum_congr rfl (fun k _ => ht k)]
  rw [← Finset.mul_sum]
  congr 1
  have hce : ∀ k : Fin n, c k = extendCoefficient c k.val := fun k => c_eq_extend c k
  have htermL : ∀ k : Fin n,
      c k * ((U ℂ (k.val : ℤ)).eval (x : ℂ)
        - (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)))
        = extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ)
          - extendCoefficient c k.val *
              (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)) := by
    intro k
    rw [hce k]
    ring
  have hL : (∑ k : Fin n, c k * ((U ℂ (k.val : ℤ)).eval (x : ℂ)
        - (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ))))
      = (∑ k : Fin n, extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ))
        - ∑ k : Fin n, extendCoefficient c k.val *
            (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)) := by
    rw [show (∑ k : Fin n, c k * ((U ℂ (k.val : ℤ)).eval (x : ℂ)
          - (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ))))
        = ∑ k : Fin n, (extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ)
          - extendCoefficient c k.val *
              (if k.val = 0 then (0 : ℂ) else (U ℂ ((k.val : ℤ) - 2)).eval (x : ℂ)))
        from Finset.sum_congr rfl (fun k _ => htermL k)]
    exact Finset.sum_sub_distrib _ _
  have htermR : ∀ k : Fin n,
      (c k - extendCoefficient c (k.val + 2)) * (U ℂ (k.val : ℤ)).eval (x : ℂ)
        = extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ)
          - extendCoefficient c (k.val + 2) * (U ℂ (k.val : ℤ)).eval (x : ℂ) := by
    intro k
    rw [hce k]
    ring
  have hR : (∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) * (U ℂ (k.val : ℤ)).eval (x : ℂ))
      = (∑ k : Fin n, extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ))
        - ∑ k : Fin n, extendCoefficient c (k.val + 2) * (U ℂ (k.val : ℤ)).eval (x : ℂ) := by
    rw [show (∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) * (U ℂ (k.val : ℤ)).eval (x : ℂ))
        = ∑ k : Fin n, (extendCoefficient c k.val * (U ℂ (k.val : ℤ)).eval (x : ℂ)
          - extendCoefficient c (k.val + 2) * (U ℂ (k.val : ℤ)).eval (x : ℂ))
        from Finset.sum_congr rfl (fun k _ => htermR k)]
    exact Finset.sum_sub_distrib _ _
  rw [hL, hR]
  congr 1
  exact sum_extend_shift c x

private theorem uEval_abs_le_sqrt_two (x : ℝ) (k : ℕ) (hx : |x| ≤ 1 / 2) :
    ‖(U ℂ (k : ℤ)).eval (x : ℂ)‖ ≤ Real.sqrt 2 := by
  have hcomp : (U ℂ (k : ℤ)).eval (x : ℂ)
      = (((S ℝ (k : ℤ)).eval (2 * x : ℝ) : ℝ) : ℂ) := by
    have h := congr_arg (fun p : ℂ[X] => p.eval (x : ℂ)) (S_comp_two_mul_X ℂ (k : ℤ))
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X] at h

    have h2 : (2 : ℂ) * (x : ℂ) = ((2 * x : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    have h4 : (S ℂ (k : ℤ)).eval ((2 * x : ℝ) : ℂ)
        = (S ℂ (k : ℤ)).eval ((2 : ℂ) * (x : ℂ)) :=
      congr_arg (fun z : ℂ => (S ℂ (k : ℤ)).eval z) h2.symm
    have h3 := algebraMap_eval_S (R := ℝ) (R' := ℂ) (2 * x) (k : ℤ)

    rw [← h, ← h4]
    exact h3.symm
  rw [hcomp, Complex.norm_real, Real.norm_eq_abs]
  have hy : |(2 * x : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_nonneg x, hx]
  have hsq := congr_arg (fun p : ℝ[X] => p.eval (2 * x)) (S_sq_add_S_sq ℝ (k : ℤ))
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one] at hsq
  set a : ℝ := (S ℝ (k : ℤ)).eval (2 * x)
  set b : ℝ := (S ℝ ((k : ℤ) + 1)).eval (2 * x)
  have hy2 : (2 * x) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact hy
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * (a - (2 * x) * b) ^ 2 + b ^ 2 * (1 - (2 * x) ^ 2 / 2) := by
    have : 0 ≤ 1 - (2 * x) ^ 2 / 2 := by nlinarith
    positivity
  have heq : (1 / 2 : ℝ) * a ^ 2 + b ^ 2 - (2 * x) * a * b
      = (1 / 2) * (a - (2 * x) * b) ^ 2 + b ^ 2 * (1 - (2 * x) ^ 2 / 2) := by ring
  have hge : (0 : ℝ) ≤ (1 / 2) * a ^ 2 + b ^ 2 - (2 * x) * a * b := by linarith
  have : (1 / 2 : ℝ) * a ^ 2 ≤ 1 := by nlinarith
  have ha : a ^ 2 ≤ 2 := by linarith
  have : |a| ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_abs a]
  exact this

private theorem norm_half (z : ℂ) : ‖(1 / 2 : ℂ) * z‖ = (1 / 2) * ‖z‖ := by
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [h12, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))]

private theorem diffNorm_nonneg {n : ℕ} (c : Fin n → ℂ) : 0 ≤ differenceNorm c := by
  show 0 ≤ Real.sqrt _
  exact Real.sqrt_nonneg _

private theorem chebValue_le {n : ℕ} (c : Fin n → ℂ) (x : ℝ) (hx : |x| ≤ 1 / 2) :
    ‖chebValue c x‖ ≤ (Real.sqrt 2 / 2) * Real.sqrt n * differenceNorm c := by
  rw [chebValue_eq_sum_diffU]
  have hhalf : ‖(1 / 2 : ℂ) *
      (∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) * (U ℂ (k.val : ℤ)).eval (x : ℂ))‖
      = (1 / 2) * ‖∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) *
        (U ℂ (k.val : ℤ)).eval (x : ℂ)‖ := norm_half _
  rw [hhalf]
  have hn : ‖∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) *
      (U ℂ (k.val : ℤ)).eval (x : ℂ)‖
      ≤ ∑ k : Fin n, ‖(c k - extendCoefficient c (k.val + 2)) *
        (U ℂ (k.val : ℤ)).eval (x : ℂ)‖ := norm_sum_le _ _
  have hm : ∀ k : Fin n, ‖(c k - extendCoefficient c (k.val + 2)) *
      (U ℂ (k.val : ℤ)).eval (x : ℂ)‖
      = ‖c k - extendCoefficient c (k.val + 2)‖ * ‖(U ℂ (k.val : ℤ)).eval (x : ℂ)‖ := by
    intro k
    exact norm_mul _ _
  have hu : ∀ k : Fin n, ‖(U ℂ (k.val : ℤ)).eval (x : ℂ)‖ ≤ Real.sqrt 2 := by
    intro k
    exact uEval_abs_le_sqrt_two x k.val hx
  have hbound : (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ *
      ‖(U ℂ (k.val : ℤ)).eval (x : ℂ)‖)
      ≤ Real.sqrt 2 * ∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ := by
    calc (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ *
          ‖(U ℂ (k.val : ℤ)).eval (x : ℂ)‖)
        ≤ ∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ * Real.sqrt 2 :=
          Finset.sum_le_sum (fun k _ =>
            mul_le_mul_of_nonneg_left (hu k) (norm_nonneg _))
      _ = ∑ k : Fin n, Real.sqrt 2 * ‖c k - extendCoefficient c (k.val + 2)‖ :=
          Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      _ = Real.sqrt 2 * ∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ :=
          (Finset.mul_sum _ _ _).symm
  have hcs : (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖)
      ≤ Real.sqrt n * differenceNorm c := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (s := (Finset.univ : Finset (Fin n)))
      (f := fun _ : Fin n => (1 : ℝ))
      (g := fun k : Fin n => ‖c k - extendCoefficient c (k.val + 2)‖)
    simp only [one_mul, one_pow] at h
    have h1 : (∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ)) = (n : ℝ) := by simp
    have h3 : Real.sqrt (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ ^ 2)
        = differenceNorm c := rfl
    rw [h1, h3] at h
    exact h
  have hle : ‖∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) *
      (U ℂ (k.val : ℤ)).eval (x : ℂ)‖
      ≤ Real.sqrt 2 * (Real.sqrt n * differenceNorm c) := by
    calc ‖∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) *
            (U ℂ (k.val : ℤ)).eval (x : ℂ)‖
        ≤ ∑ k : Fin n, ‖(c k - extendCoefficient c (k.val + 2)) *
            (U ℂ (k.val : ℤ)).eval (x : ℂ)‖ := hn
      _ = ∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ *
            ‖(U ℂ (k.val : ℤ)).eval (x : ℂ)‖ := Finset.sum_congr rfl (fun k _ => hm k)
      _ ≤ Real.sqrt 2 * ∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ := hbound
      _ ≤ Real.sqrt 2 * (Real.sqrt n * differenceNorm c) :=
            mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg 2)
  have hfin : (1 / 2 : ℝ) * ‖∑ k : Fin n, (c k - extendCoefficient c (k.val + 2)) *
      (U ℂ (k.val : ℤ)).eval (x : ℂ)‖
      ≤ (1 / 2) * (Real.sqrt 2 * (Real.sqrt n * differenceNorm c)) :=
    mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have heq : (1 / 2 : ℝ) * (Real.sqrt 2 * (Real.sqrt n * differenceNorm c))
      = (Real.sqrt 2 / 2) * Real.sqrt n * differenceNorm c := by ring
  exact hfin.trans (le_of_eq heq)

private theorem sqrt_two_div_two_le : (Real.sqrt 2 / 2 : ℝ) ≤ 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

private theorem sqrt_two_div_two_lt : (Real.sqrt 2 / 2 : ℝ) < 1 := by
  have h : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  linarith

private theorem differenceNorm_eq_zero_iff {n : ℕ} (c : Fin n → ℂ) :
    differenceNorm c = 0 ↔ ∀ k : Fin n, c k = 0 := by
  constructor
  · intro h
    have hsum : (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ ^ 2) = 0 := by
      have hsq : Real.sqrt (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ ^ 2) = 0 := h
      rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq
      exact hsq
    have hd : ∀ j : Fin n, c j - extendCoefficient c (j.val + 2) = 0 := by
      intro j
      have hterm : ‖c j - extendCoefficient c (j.val + 2)‖ ^ 2 = 0 := by
        have hne := Finset.sum_eq_zero_iff_of_nonneg
          (fun (j : Fin n) _ => sq_nonneg (‖c j - extendCoefficient c (j.val + 2)‖)) |>.mp hsum
        exact hne j (Finset.mem_univ j)
      have : ‖c j - extendCoefficient c (j.val + 2)‖ = 0 := by
        nlinarith [sq_abs (‖c j - extendCoefficient c (j.val + 2)‖),
          abs_nonneg (‖c j - extendCoefficient c (j.val + 2)‖)]
      exact norm_eq_zero.mp this
    intro k
    by_contra hc
    have hex : ∃ k : Fin n, c k ≠ 0 := ⟨k, hc⟩
    set s : Finset (Fin n) := Finset.univ.filter (fun j => c j ≠ 0) with hs
    have hsne : s.Nonempty := by
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, by simp [s, hj]⟩
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image s (fun j => j.val) hsne
    have hck : c k ≠ 0 := by simpa [s] using! hk
    have hd' : c k = extendCoefficient c (k.val + 2) := sub_eq_zero.mp (hd k)
    have hext : extendCoefficient c (k.val + 2) = 0 := by
      by_cases hlt : k.val + 2 < n
      · have h0 : c ⟨k.val + 2, hlt⟩ = 0 := by
          by_contra hcne
          have hmem : (⟨k.val + 2, hlt⟩ : Fin n) ∈ s := by
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hcne
          have hle := hkmax _ hmem
          simp only at hle
          omega
        rw [extendCoefficient_eq c (k.val + 2) hlt, h0]
      · exact extendCoefficient_of_not_lt c (k.val + 2) hlt
    rw [hd', hext] at hck
    exact hck rfl
  · intro h
    have hd : ∀ k : Fin n, c k - extendCoefficient c (k.val + 2) = 0 := by
      intro k
      have hext : extendCoefficient c (k.val + 2) = 0 := by
        by_cases hlt : k.val + 2 < n
        · rw [extendCoefficient_eq c (k.val + 2) hlt, h ⟨k.val + 2, hlt⟩]
        · exact extendCoefficient_of_not_lt c (k.val + 2) hlt
      rw [h k, hext, sub_zero]
    have hsum : (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ ^ 2) = 0 := by
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [hd k, norm_zero]
      norm_num
    have : Real.sqrt (∑ k : Fin n, ‖c k - extendCoefficient c (k.val + 2)‖ ^ 2) = 0 := by
      rw [hsum, Real.sqrt_zero]
    exact this

theorem Clause21ChebyshevDifferenceBound_answer : Clause21ChebyshevDifferenceBound := by
  intro n c
  refine ⟨?_, ?_, ?_⟩
  · intro x hx1 hx2
    have hx : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h := chebValue_le c x hx
    have hle : (Real.sqrt 2 / 2 : ℝ) ≤ 1 := sqrt_two_div_two_le
    have hnn : 0 ≤ Real.sqrt n * differenceNorm c :=
      mul_nonneg (Real.sqrt_nonneg _) (diffNorm_nonneg c)
    have hcmp : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt n * differenceNorm c)
        ≤ 1 * (Real.sqrt n * differenceNorm c) :=
      mul_le_mul_of_nonneg_right hle hnn
    have heq : (Real.sqrt 2 / 2 : ℝ) * Real.sqrt n * differenceNorm c
        = (Real.sqrt 2 / 2) * (Real.sqrt n * differenceNorm c) := by ring
    have htrans : ‖chebValue c x‖ ≤ 1 * (Real.sqrt n * differenceNorm c) := by
      rw [← heq] at hcmp
      exact h.trans hcmp
    simpa using! htrans
  · intro hcne
    obtain ⟨k, hk⟩ := hcne
    have hdn : differenceNorm c ≠ 0 := by
      intro h
      rw [differenceNorm_eq_zero_iff] at h
      exact hk (h k)
    have hdn0 : 0 < differenceNorm c :=
      lt_of_le_of_ne (diffNorm_nonneg c) (Ne.symm hdn)
    have hsup : polynomialSup c (1 / 2)
        ≤ (Real.sqrt 2 / 2) * Real.sqrt n * differenceNorm c := by
      show sSup {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧ y = ‖chebValue c x‖} ≤ _
      refine Real.sSup_le (fun y hy => ?_)
        (mul_nonneg (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
          (Real.sqrt_nonneg _)) (diffNorm_nonneg c))
      obtain ⟨x, hx1, hx2, hxy⟩ := hy
      rw [hxy]
      have hx : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact chebValue_le c x hx
    have hn_ne : n ≠ 0 := by
      rintro rfl
      exact Fin.elim0 k
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn_ne
    have hlt : (Real.sqrt 2 / 2) * Real.sqrt n * differenceNorm c
        < Real.sqrt n * differenceNorm c := by
      have h1 : Real.sqrt 2 / 2 < 1 := sqrt_two_div_two_lt
      have h2 : 0 < Real.sqrt n * differenceNorm c :=
        mul_pos (Real.sqrt_pos.mpr hn0) hdn0
      have hcmp : (Real.sqrt 2 / 2) * (Real.sqrt n * differenceNorm c)
          < 1 * (Real.sqrt n * differenceNorm c) :=
        mul_lt_mul_of_pos_right h1 h2
      have heq : (Real.sqrt 2 / 2) * Real.sqrt n * differenceNorm c
          = (Real.sqrt 2 / 2) * (Real.sqrt n * differenceNorm c) := by ring
      rw [heq]
      simpa using! hcmp
    exact lt_of_le_of_lt hsup hlt
  · intro hzero
    refine ⟨?_, ?_⟩
    · have hcv : ∀ x : ℝ, chebValue c x = 0 := by
        intro x
        rw [chebValue]
        exact Finset.sum_eq_zero (fun k _ => by rw [hzero k, zero_mul])
      have hset : {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧ y = ‖chebValue c x‖}
          = ({0} : Set ℝ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hy
          obtain ⟨x, _, _, hxy⟩ := hy
          rw [hxy, hcv x, norm_zero]
        · intro hy
          refine ⟨0, by norm_num, by norm_num, ?_⟩
          rw [hy, hcv 0, norm_zero]
      show sSup {y : ℝ | ∃ x : ℝ, -(1 / 2) ≤ x ∧ x ≤ 1 / 2 ∧ y = ‖chebValue c x‖} = 0
      rw [hset]
      exact csSup_singleton 0
    · rw [differenceNorm_eq_zero_iff]
      exact hzero

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
