/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOASupremacy16.GapModels
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Fourier inversion of bounded cost counts

`dftChar` provides finite Fourier characters and their orthogonality relation. For a bounded
natural-valued cost, Fourier inversion of `cspAmplitude` recovers `countVec` and hence
`satisfyingCount`; the final conditional implication to equality of the supplied classes uses
the assumptions packaged in `ConditionalCountingData`.

This development accompanies the study of QAOA sampling and postselection in [FarhiHarrow2016].

## Main statements

* `countVec_eq_inverse_transform`: For costs bounded by `m`, the count at `v < m + 1` is `2^n /
  (m + 1)` times the inverse Fourier transform of the sampled cost amplitudes.
* `supplied_counting_implication`: Within the supplied conditional counting data,
  `ExactMatrixElementsInP` implies equality of the specified classes `P` and `NP`.

## References

* [Farhi and Harrow, 2016][FarhiHarrow2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QAOASupremacy16.Counting

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOASupremacy16.GapModels
open Qatlib.Papers.QAOASupremacy16.CircuitDefs
open Matrix
open scoped BigOperators

variable {n : ℕ}

/-- The complex character `exp (2 * π * i * k * r / S)` for integer frequency `k` and natural
sample index `r`. -/
noncomputable def dftChar (S : ℕ) (k : ℤ) (r : ℕ) : ℂ :=
  Complex.exp (((k * (r : ℤ) : ℝ) / (S : ℝ)) * (2 * Real.pi * Complex.I))

/-- The complex exponential of an integer multiple of `2 * π * i` is one. -/
theorem exp_two_pi_int (k : ℤ) :
    Complex.exp ((k : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨k, rfl⟩

/-- A Fourier character at sample `r` is the `r`th power of its one-step exponential. -/
theorem dftChar_eq_pow (S : ℕ) (k : ℤ) (r : ℕ) :
    dftChar S k r
      = (Complex.exp (((k : ℝ) / (S : ℝ)) * (2 * Real.pi * Complex.I))) ^ r := by
  unfold dftChar
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Multiplying Fourier characters adds their integer frequencies. -/
theorem dftChar_add (S : ℕ) (a b : ℤ) (r : ℕ) :
    dftChar S a r * dftChar S b r = dftChar S (a + b) r := by
  unfold dftChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For positive `S`, the sum of a Fourier character over `Fin S` is `S` when `S` divides its
frequency and zero otherwise. -/
theorem sum_dftChar (S : ℕ) (hS : 0 < S) (k : ℤ) :
    ∑ r : Fin S, dftChar S k r.val
      = if (S : ℤ) ∣ k then (S : ℂ) else 0 := by
  set η : ℂ := Complex.exp (((k : ℝ) / (S : ℝ)) * (2 * Real.pi * Complex.I)) with hη
  have hterm : ∀ r : ℕ, dftChar S k r = η ^ r := by
    intro r
    rw [dftChar_eq_pow, hη]
  have hSreal : ((S : ℝ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hSneC : ((S : ℂ)) ≠ 0 := by exact_mod_cast hS.ne'
  have hηS : η ^ S = 1 := by
    have h2 : (S : ℂ) * (((k : ℝ) / (S : ℝ)) * (2 * Real.pi * Complex.I))
        = ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp [hSneC]
    rw [hη, ← Complex.exp_nat_mul, h2]
    exact exp_two_pi_int k
  by_cases hd : (S : ℤ) ∣ k
  · rw [if_pos hd]
    obtain ⟨c, hc⟩ := hd
    have hη1 : η = 1 := by
      rw [hη, Complex.exp_eq_one_iff]
      refine ⟨c, ?_⟩
      rw [hc]
      push_cast
      field_simp [hSneC]
    calc ∑ r : Fin S, dftChar S k r.val
        = ∑ r ∈ Finset.range S, η ^ r := by
          rw [Fin.sum_univ_eq_sum_range]
          exact Finset.sum_congr rfl fun r _ => hterm r
      _ = ∑ r ∈ Finset.range S, (1 : ℂ) := by
          exact Finset.sum_congr rfl fun r _ => by rw [hη1]; simp
      _ = (S : ℂ) := by simp
  · rw [if_neg hd]
    have hηne : η ≠ 1 := by
      intro hcon
      apply hd
      rw [hη] at hcon
      obtain ⟨c, hc⟩ := Complex.exp_eq_one_iff.mp hcon
      have hπ : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_ne_zero (mul_ne_zero two_ne_zero hp) Complex.I_ne_zero
      have hcancel : (((k : ℝ) / (S : ℝ)) : ℂ) = (c : ℂ) := by
        have hc' : ((((k : ℝ) / (S : ℝ))) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
            = (c : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
          simpa [mul_assoc] using hc
        exact mul_right_cancel₀ hπ hc'
      have hcR : (k : ℝ) = (c : ℝ) * (S : ℝ) := by
        have hq : ((k : ℝ) / (S : ℝ)) = (c : ℝ) := by exact_mod_cast hcancel
        field_simp [hSreal] at hq ⊢
        linarith
      have hkZ : k = c * (S : ℤ) := by exact_mod_cast hcR
      refine ⟨c, ?_⟩
      rw [hkZ]; ring
    have hgeo := geom_sum_mul η S
    rw [hηS, sub_self] at hgeo
    have hsum0 : ∑ r ∈ Finset.range S, η ^ r = 0 := by
      rcases mul_eq_zero.mp hgeo with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hηne
    calc ∑ r : Fin S, dftChar S k r.val
        = ∑ r ∈ Finset.range S, η ^ r := by
          rw [Fin.sum_univ_eq_sum_range]
          exact Finset.sum_congr rfl fun r _ => hterm r
      _ = 0 := hsum0

/-- For natural `a,b < S`, divisibility of their integer difference by `S` is equivalent to `a =
b`. -/
theorem dvd_iff_eq_of_bounds {S a b : ℕ} (ha : a < S) (hb : b < S) :
    (S : ℤ) ∣ ((a : ℤ) - (b : ℤ)) ↔ a = b := by
  constructor
  · intro hd
    have hx0 : (a : ℤ) - (b : ℤ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hd ?_
      have ha' : (a : ℤ) < (S : ℤ) := by exact_mod_cast ha
      have hb' : (b : ℤ) < (S : ℤ) := by exact_mod_cast hb
      have ha0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
      have hb0 : (0 : ℤ) ≤ (b : ℤ) := Int.natCast_nonneg b
      rw [abs_lt]
      constructor <;> omega
    have hab : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hab
  · intro h
    subst h
    simp

/-- The number of `n`-bit registers at which the cost equals `v`. -/
def countVec (C : Reg n → ℕ) (v : ℕ) : ℕ :=
  (Finset.univ.filter fun z => C z = v).card

/-- The number of registers whose cost equals the specified value `m`. -/
def satisfyingCount (C : Reg n → ℕ) (m : ℕ) : ℕ :=
  countVec C m

/-- At a Fourier sampling angle, the cost phase sum is `2^(-n)` times the sum of Fourier
characters with frequencies given by the negative costs. -/
theorem cspAmplitude_eq_dft (n m : ℕ) (C : Reg n → ℕ) (r : ℕ) :
    cspAmplitude (phaseAngle m r) C
      = ((2 : ℂ) ^ n)⁻¹ *
        ∑ z : Reg n, dftChar (m + 1) (-(C z : ℤ)) r := by
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  unfold cspAmplitude phaseAngle dftChar
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg Complex.exp
  push_cast
  field_simp [hm1]

/-- For costs bounded by `m`, Fourier orthogonality recovers `(m + 1)` times the number of
registers with cost `v` from the double character sum. -/
theorem dft_inversion_sum (n m : ℕ) (C : Reg n → ℕ) (hC : ∀ z, C z ≤ m)
    (v : Fin (m + 1)) :
    ∑ r : Fin (m + 1),
        (∑ z : Reg n, dftChar (m + 1) (-(C z : ℤ)) r.val)
          * dftChar (m + 1) (v.val : ℤ) r.val
      = ((m + 1 : ℕ) : ℂ) * (countVec C v.val : ℂ) := by
  have hS : 0 < m + 1 := Nat.succ_pos m
  have hind : ∑ z : Reg n, (if C z = v.val then (1 : ℂ) else 0)
      = (countVec C v.val : ℂ) := by
    rw [← Finset.sum_filter]
    simp [countVec]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc ∑ z : Reg n, ∑ r : Fin (m + 1),
          dftChar (m + 1) (-(C z : ℤ)) r.val * dftChar (m + 1) (v.val : ℤ) r.val
      = ∑ z : Reg n, ∑ r : Fin (m + 1),
          dftChar (m + 1) ((v.val : ℤ) - (C z : ℤ)) r.val := by
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro r _
        rw [dftChar_add]
        congr 1
        ring
    _ = ∑ z : Reg n,
          (if ((m + 1 : ℕ) : ℤ) ∣ ((v.val : ℤ) - (C z : ℤ))
            then ((m + 1 : ℕ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        exact sum_dftChar (m + 1) hS ((v.val : ℤ) - (C z : ℤ))
    _ = ∑ z : Reg n,
          (((m + 1 : ℕ) : ℂ) * (if C z = v.val then (1 : ℂ) else 0)) := by
        apply Finset.sum_congr rfl
        intro z _
        have hdvd : (((m + 1 : ℕ) : ℤ) ∣ ((v.val : ℤ) - (C z : ℤ)))
            ↔ C z = v.val := by
          have hb := dvd_iff_eq_of_bounds (S := m + 1) (a := v.val) (b := C z)
            v.isLt (Nat.lt_succ_of_le (hC z))
          exact hb.trans eq_comm
        by_cases hv : C z = v.val
        · rw [if_pos (hdvd.mpr hv), if_pos hv]; ring
        · rw [if_neg (fun hp => hv (hdvd.mp hp)), if_neg hv]; ring
    _ = ((m + 1 : ℕ) : ℂ) * (countVec C v.val : ℂ) := by
        rw [← hind, Finset.mul_sum]

/-- For costs bounded by `m`, the count at `v < m + 1` is `2^n / (m + 1)` times the inverse
Fourier transform of the sampled cost amplitudes. -/
theorem countVec_eq_inverse_transform (n m : ℕ) (C : Reg n → ℕ)
    (hC : ∀ z, C z ≤ m) (v : Fin (m + 1)) :
    (countVec C v.val : ℂ)
      = (((2 : ℂ) ^ n) * (((m + 1 : ℕ) : ℂ)⁻¹)) *
        ∑ r : Fin (m + 1),
          cspAmplitude (phaseAngle m r.val) C * dftChar (m + 1) (v.val : ℤ) r.val := by
  have h2n : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  have hSne : (((m + 1 : ℕ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero m)
  have hcore := dft_inversion_sum n m C hC v

  have hsum : ∑ r : Fin (m + 1),
        cspAmplitude (phaseAngle m r.val) C * dftChar (m + 1) (v.val : ℤ) r.val
      = ((2 : ℂ) ^ n)⁻¹ *
        ∑ r : Fin (m + 1),
          (∑ z : Reg n, dftChar (m + 1) (-(C z : ℤ)) r.val)
            * dftChar (m + 1) (v.val : ℤ) r.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [cspAmplitude_eq_dft]
    ring
  rw [hsum, hcore]
  field_simp [h2n, hSne]

/-- Two costs bounded by `m` with equal sampled phase amplitudes have equal counts at every
value below `m + 1`. -/
theorem countVec_eq_of_matrix_elements (n m : ℕ) (C C' : Reg n → ℕ)
    (hC : ∀ z, C z ≤ m) (hC' : ∀ z, C' z ≤ m)
    (h : ∀ r : Fin (m + 1),
      cspAmplitude (phaseAngle m r.val) C = cspAmplitude (phaseAngle m r.val) C')
    (v : Fin (m + 1)) :
    countVec C v.val = countVec C' v.val := by
  have h1 := countVec_eq_inverse_transform n m C hC v
  have h2 := countVec_eq_inverse_transform n m C' hC' v
  have hsum : ∑ r : Fin (m + 1),
        cspAmplitude (phaseAngle m r.val) C * dftChar (m + 1) (v.val : ℤ) r.val
      = ∑ r : Fin (m + 1),
        cspAmplitude (phaseAngle m r.val) C' * dftChar (m + 1) (v.val : ℤ) r.val := by
    apply Finset.sum_congr rfl
    intro r _
    rw [h r]
  rw [hsum] at h1
  have hc : (countVec C v.val : ℂ) = (countVec C' v.val : ℂ) := h1.trans h2.symm
  exact_mod_cast hc

/-- Two costs bounded by `m` with equal sampled phase amplitudes have equal counts at value `m`. -/
theorem satisfyingCount_eq_of_matrix_elements (n m : ℕ) (C C' : Reg n → ℕ)
    (hC : ∀ z, C z ≤ m) (hC' : ∀ z, C' z ≤ m)
    (h : ∀ r : Fin (m + 1),
      cspAmplitude (phaseAngle m r.val) C = cspAmplitude (phaseAngle m r.val) C') :
    satisfyingCount C m = satisfyingCount C' m :=
  countVec_eq_of_matrix_elements n m C C' hC hC' h ⟨m, Nat.lt_succ_self m⟩

/-- A package of propositions and supplied implications from exact matrix-element computation to
exact counting and then to equality of the specified language classes `P` and `NP`. -/
structure ConditionalCountingData (P NP : Set Language) where

  ExactMatrixElementsInP : Prop

  ExactCountingInP : Prop

  matrix_elements_give_counting : ExactMatrixElementsInP → ExactCountingInP

  exact_counting_yields_P_eq_NP : ExactCountingInP → P = NP

/-- Within the supplied conditional counting data, `ExactMatrixElementsInP` implies equality of
the specified classes `P` and `NP`. -/
theorem supplied_counting_implication {P NP : Set Language}
    (I : ConditionalCountingData P NP)
    (h : I.ExactMatrixElementsInP) : P = NP :=
  I.exact_counting_yields_P_eq_NP (I.matrix_elements_give_counting h)

end Qatlib.Papers.QAOASupremacy16.Counting
