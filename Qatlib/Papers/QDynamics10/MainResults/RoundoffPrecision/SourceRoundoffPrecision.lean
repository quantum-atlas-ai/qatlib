/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.RoundoffPrecision — c001 (Lemma 1)

Fixed source: arXiv:1011.3489v1, Lemma 1 (p. 6–7) and its proof in Appendix A (p. 18–19),
Eqs. (14), (15), (A4)–(A13).

Paper statement. Let `{H_μ : ℝ → ℂ^{2^n×2^n}}` be a 2-smooth, `d`-sparse family, `Δt` the
maximal interval length, and `U_k` the `k`-th order Lie–Trotter–Suzuki integrator. The
round-off error from discretising time (`n_t` bits) and matrix elements (`n_H` bits) while
simulating the product of time-evolution operators is at most `ε/2` if the bit counts obey
Eq. (14) and every subinterval has length at least `Δt/2^{n_t}` (Eq. (15)).

Formalised content. Appendix A bounds the produced-vs-exact product by
`max_p ‖H(τ_p) − H̃(τ̃_p)‖ · Σ_p |Δt_p|` (A4). The first factor splits, by the triangle
inequality, into the time-discretisation error (A7)–(A9) and the mod-elements error
(A10)–(A12), each at most `ε/(32kMd²(5/3)^{k−1}Δt)`; the second factor is at most
`8kMd²(5/3)^{k−1}Δt` (A6). Their product is `ε/2` (A13).

We prove the two precision-to-step-error implications from (14) in full
(`timePrecision_stepError`, `matrixPrecision_entryError`) and the final arithmetic
(`lemma1_roundoff_error`), and assemble them in
`lemma1_roundoff_error_from_precision`. The remaining inputs of that assembly are exactly
the paper's own intermediate statements (A8's Taylor step, A6's duration sum, A10–A12's
encoding error) and are exposed as explicitly documented hypotheses.

Boundary: the model does not construct the quantum circuit or the binary polar encoding;
`n_H`-bit modulus/phase rounding is passed as the paper's Eq. (A10)–(A12) bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.RoundoffPrecision

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The precision coefficient `B = 32 k M d² (5/3)^{k−1}` of Eq. (14) and Appendix A. -/
def precisionCoefficient (k M d : ℕ) : ℝ :=
  (32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2) * ((5 : ℝ) / 3) ^ (k - 1)

/-- The `precisionCoefficient_pos` result for the QDynamics10 paper model. -/
theorem precisionCoefficient_pos (k M d : ℕ) (hk : 1 ≤ k) (hM : 1 ≤ M) (hd : 1 ≤ d) :
    0 < precisionCoefficient k M d := by
  have h1 : (0 : ℝ) < 32 := by norm_num
  have h2 : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have h3 : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  have h4 : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h7 : (0 : ℝ) < ((d : ℝ) ^ 2) := by positivity
  have h6 : (0 : ℝ) < ((5 : ℝ) / 3) ^ (k - 1) := pow_pos (by norm_num) _
  unfold precisionCoefficient
  exact mul_pos (mul_pos (mul_pos (mul_pos h1 h2) h3) h7) h6

/-- Eq. (14a) with Eq. (A8)–(A9): if `n_t` respects the time-precision condition, then the
time-discretisation error of a single exponential, `max‖∂_t H‖ · Δt/2^{n_t}`, is at most
`ε/(32 k M d² (5/3)^{k−1} Δt)`. -/
theorem timePrecision_stepError
    (k M d : ℕ) (Xmax Δt ε : ℝ) (nt : ℕ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hd : 1 ≤ d) (hX : 0 < Xmax)
    (hΔt : 0 < Δt) (hε : 0 < ε)
    (hnt : timePrecisionBits k M d Xmax Δt ε ≤ nt) :
    Xmax * (Δt / ((2 : ℝ) ^ nt)) ≤ ε / (precisionCoefficient k M d * Δt) := by
  set A : ℝ :=
    Xmax * ((32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2)) * ((5 : ℝ) / 3) ^ (k - 1)
      * Δt ^ 2 / ε with hA
  have hk' : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hM' : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  have hd' : (0 : ℝ) < ((d : ℝ) ^ 2) := by
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    positivity
  have hcoef : (0 : ℝ) < (32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2) :=
    mul_pos (mul_pos (mul_pos (by norm_num) hk') hM') hd'
  have hApos : 0 < A := by
    rw [hA]
    exact div_pos (mul_pos (mul_pos (mul_pos hX hcoef) (pow_pos (by norm_num) _))
      (pow_pos hΔt 2)) hε
  have hce : Nat.ceil (Real.logb 2 A) ≤ nt := by
    rw [hA]
    exact hnt
  have hle : Real.logb 2 A ≤ (nt : ℝ) := Nat.ceil_le.mp hce
  have h2 : A ≤ (2 : ℝ) ^ (nt : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hApos).mp hle
  rw [Real.rpow_natCast] at h2
  have h3 : Xmax * ((32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2)) * ((5 : ℝ) / 3) ^ (k - 1)
      * Δt ^ 2 ≤ (2 : ℝ) ^ nt * ε := by
    have h2' : Xmax * ((32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2))
        * ((5 : ℝ) / 3) ^ (k - 1) * Δt ^ 2 / ε ≤ (2 : ℝ) ^ nt := by
      rw [← hA]; exact h2
    exact (div_le_iff₀ hε).mp h2'
  have hBdef : precisionCoefficient k M d
      = (32 : ℝ) * (k : ℝ) * (M : ℝ) * ((d : ℝ) ^ 2) * ((5 : ℝ) / 3) ^ (k - 1) := by
    unfold precisionCoefficient
    ring
  have hmul : Xmax * (Δt / ((2 : ℝ) ^ nt)) = Xmax * Δt / ((2 : ℝ) ^ nt) := by ring
  rw [hmul, div_le_div_iff₀ (by positivity)
    (mul_pos (precisionCoefficient_pos k M d hk hM hd) hΔt)]
  rw [hBdef]
  nlinarith [h3]

/-- Eq. (14b) with Eq. (A10)–(A12): if `n_H` respects the matrix-element precision
condition, the combined modulus/phase rounding error, `(1 + 2π) Λmax 2^{-n_H/2}`, is at
most `ε/(32 k M d² (5/3)^{k−1} Δt)`. -/
theorem matrixPrecision_entryError
    (k M d : ℕ) (Λmax Δt ε : ℝ) (nH : ℕ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hd : 1 ≤ d) (hΛ : 0 < Λmax)
    (hΔt : 0 < Δt) (hε : 0 < ε)
    (hnH : matrixPrecisionBits k M d Λmax Δt ε ≤ nH) :
    Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2) + 2 * Real.pi * Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2)
      ≤ ε / (precisionCoefficient k M d * Δt) := by
  have hB : 0 < precisionCoefficient k M d := precisionCoefficient_pos k M d hk hM hd
  set Y : ℝ := precisionCoefficient k M d * Λmax * Δt / ε with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; positivity
  set c : ℕ := Nat.ceil (Real.logb 2 Y) with hcdef
  have hcge : Real.logb 2 Y ≤ (c : ℝ) := by
    rw [hcdef]
    exact Nat.le_ceil _
  have hYle : Y ≤ (2 : ℝ) ^ c := by
    have := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hYpos).mp hcge
    rwa [Real.rpow_natCast] at this
  have hbits : matrixPrecisionBits k M d Λmax Δt ε = 2 * c + 6 := by
    unfold matrixPrecisionBits
    rw [hcdef]
    congr 1
  have hnH' : 2 * c + 6 ≤ nH := by
    rw [hbits] at hnH
    exact hnH
  have hpow : 8 * Y ≤ (2 : ℝ) ^ ((nH : ℝ) / 2) := by
    have hhalf : (((2 * c + 6 : ℕ)) : ℝ) / 2 ≤ (nH : ℝ) / 2 := by
      have : ((2 * c + 6 : ℕ) : ℝ) ≤ (nH : ℝ) := by exact_mod_cast hnH'
      linarith
    have hbase : (2 : ℝ) ^ ((((2 * c + 6 : ℕ)) : ℝ) / 2) ≤ (2 : ℝ) ^ ((nH : ℝ) / 2) :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hhalf
    have heq : (2 : ℝ) ^ ((((2 * c + 6 : ℕ)) : ℝ) / 2) = 8 * (2 : ℝ) ^ c := by
      have hcast : ((((2 * c + 6 : ℕ)) : ℝ) / 2) = (c : ℝ) + 3 := by
        push_cast
        ring
      rw [hcast, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
      norm_num
      ring
    calc 8 * Y ≤ 8 * (2 : ℝ) ^ c := by linarith [hYle]
      _ = (2 : ℝ) ^ ((((2 * c + 6 : ℕ)) : ℝ) / 2) := heq.symm
      _ ≤ (2 : ℝ) ^ ((nH : ℝ) / 2) := hbase
  have hneg : (2 : ℝ) ^ (-(nH : ℝ) / 2) ≤ 1 / (8 * Y) := by
    have hexp : -(nH : ℝ) / 2 = -((nH : ℝ) / 2) := by ring
    rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← one_div]
    exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8 * Y) hpow
  have hkey : Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2) ≤ ε / (8 * precisionCoefficient k M d * Δt) := by
    calc Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2) ≤ Λmax * (1 / (8 * Y)) :=
          mul_le_mul_of_nonneg_left hneg hΛ.le
      _ = ε / (8 * precisionCoefficient k M d * Δt) := by
          rw [hYdef]
          field_simp
          try ring
  have hπ : 1 + 2 * Real.pi ≤ 8 := by
    have := Real.pi_lt_d2
    linarith
  have hπpos : 0 ≤ 1 + 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  calc Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2) + 2 * Real.pi * Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2)
      = (1 + 2 * Real.pi) * (Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2)) := by ring
    _ ≤ (1 + 2 * Real.pi) * (ε / (8 * precisionCoefficient k M d * Δt)) :=
        mul_le_mul_of_nonneg_left hkey hπpos
    _ ≤ 8 * (ε / (8 * precisionCoefficient k M d * Δt)) := by
        apply mul_le_mul_of_nonneg_right hπ
        positivity
    _ = ε / (precisionCoefficient k M d * Δt) := by
        field_simp
        try ring

/-- Appendix A, Eq. (A13): a per-exponential error of at most `2ε/(B Δt)` distributed over
a total exponential duration of at most `B Δt/4` accumulates to at most `ε/2`, where
`B = 32 k M d² (5/3)^{k−1}`. -/
theorem lemma1_roundoff_error
    (k M d : ℕ) (ε Δt totalDuration perStepError : ℝ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hd : 1 ≤ d) (hε : 0 < ε) (hΔt : 0 < Δt)
    (hPerStep : perStepError ≤ 2 * ε / (precisionCoefficient k M d * Δt))
    (hDuration : totalDuration ≤ precisionCoefficient k M d * Δt / 4)
    (h0d : 0 ≤ totalDuration) :
    perStepError * totalDuration ≤ ε / 2 := by
  have hB : 0 < precisionCoefficient k M d := precisionCoefficient_pos k M d hk hM hd
  calc perStepError * totalDuration
      ≤ (2 * ε / (precisionCoefficient k M d * Δt)) * (precisionCoefficient k M d * Δt / 4) :=
        mul_le_mul hPerStep hDuration h0d (by positivity)
    _ = ε / 2 := by
        field_simp
        ring

/-- c001 — Lemma 1 (p. 6–7; Appendix A Eqs. (A4)–(A13)).

Round-off error bound for the product simulation over one subinterval family: if the
time-precision and matrix-element-precision hypotheses (14) hold, the Taylor/encoding error
of one exponential is the paper's `‖H(τ_p) − H̃(τ̃_p)‖ ≤ max‖∂_t H‖ σ + ε_ρ + ε_φ Λmax`
(A7)–(A12), and the total exponential duration obeys Eq. (A6), then the round-off error is
at most `ε/2`.

The hypotheses `hTaylor`/`hEntry`/`hDuration` are the paper's own intermediate bounds
(A7–A12, A6); the two precision hypotheses are discharged from Eq. (14) by
`timePrecision_stepError` and `matrixPrecision_entryError` in the assembled theorem below. -/
theorem lemma1_roundoff_error_from_precision
    (k M d : ℕ) (Xmax Λmax ε Δt totalDuration entryError : ℝ) (nt nH : ℕ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hX : 0 < Xmax) (hΛ : 0 < Λmax) (hε : 0 < ε) (hΔt : 0 < Δt)
    (hnt : timePrecisionBits k M d Xmax Δt ε ≤ nt)
    (hnH : matrixPrecisionBits k M d Λmax Δt ε ≤ nH)
    -- Eq. (A7)–(A12): the per-step matrix-element error, including the `n_H`-bit encoding.
    (hEntry : entryError ≤ Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2)
      + 2 * Real.pi * Λmax * (2 : ℝ) ^ (-(nH : ℝ) / 2))
    -- Eq. (A6): Σ_p |Δt_p| ≤ 8 k M d² (5/3)^{k−1} Δt = B Δt / 4.
    (hDuration : totalDuration ≤ precisionCoefficient k M d * Δt / 4)
    (h0d : 0 ≤ totalDuration) :
    (Xmax * (Δt / ((2 : ℝ) ^ nt)) + entryError) * totalDuration ≤ ε / 2 := by
  have hTime := timePrecision_stepError k M d Xmax Δt ε nt hk hM hd hX hΔt hε hnt
  have hEnt := matrixPrecision_entryError k M d Λmax Δt ε nH hk hM hd hΛ hΔt hε hnH
  have hPerStep : Xmax * (Δt / ((2 : ℝ) ^ nt)) + entryError
      ≤ 2 * ε / (precisionCoefficient k M d * Δt) := by
    have hsum : Xmax * (Δt / ((2 : ℝ) ^ nt)) + entryError
        ≤ ε / (precisionCoefficient k M d * Δt) + ε / (precisionCoefficient k M d * Δt) :=
      add_le_add hTime (le_trans hEntry hEnt)
    calc Xmax * (Δt / ((2 : ℝ) ^ nt)) + entryError
        ≤ ε / (precisionCoefficient k M d * Δt) + ε / (precisionCoefficient k M d * Δt) := hsum
      _ = 2 * ε / (precisionCoefficient k M d * Δt) := by ring
  exact lemma1_roundoff_error k M d ε Δt totalDuration _ hk hM hd hε hΔt hPerStep hDuration h0d

end Qatlib.Papers.QDynamics10.MainResults.RoundoffPrecision
