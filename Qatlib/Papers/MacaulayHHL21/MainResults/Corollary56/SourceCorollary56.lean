/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 5.6 — lower bound for the Boolean Macaulay matrix

Fixed paper: arXiv:2111.00405, Corollary 5.6 on p.14.

Statement (verbatim): *Let `B̂ = [M − b]` be the Boolean Macaulay matrix of `F` … Let `h` be
the minimum Hamming weight of the `t` solutions … If all the `t` solutions have the same
Hamming weight `h` or the minimum ℓ2-norm solution vector `y = M⁺b` is in the convex hull of
`y₁, …, y_t`, then the tQLScn `κ_b(M) ≥ ½√((2h−1)/t)`.`*

The paper proves `‖M‖ ≥ 1/2` (the Macaulay construction has a matrix entry of modulus at
least `1/2`) and then repeats the derivation of Theorem 4.5 with total degree `d = 1`; the
monomial solution vector of weight `h` has `‖yᵢ‖² = 2^h − 1 ≥ 2h − 1` (equation (11) with
`d = 1`).  We prove the arithmetic combination; the norm bound `‖y₀‖ ≤ √t·‖y‖` is the same
Lemma 4.3/4.4 input as in Theorem 4.5 and is kept as an explicit hypothesis.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Corollary56

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- Arithmetic fact used in Corollary 5.6: for `h ≥ 1`, `2h ≤ 2^h` (so `2^h − 1 ≥ 2h − 1`). -/
theorem two_mul_le_two_pow : ∀ h : ℕ, 1 ≤ h → 2 * h ≤ 2 ^ h
  | 1, _ => by norm_num
  | n + 2, _ => by
      have ih : 2 * (n + 1) ≤ 2 ^ (n + 1) := two_mul_le_two_pow (n + 1) (by omega)
      have h2 : (2 : ℕ) ≤ 2 ^ (n + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (n + 1) := pow_le_pow_right' (by norm_num) (by omega)
      have hstep : 2 * (n + 2) = 2 * (n + 1) + 2 := by ring
      rw [hstep]
      calc 2 * (n + 1) + 2 ≤ 2 ^ (n + 1) + 2 := Nat.add_le_add_right ih 2
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add_left h2 _
        _ = 2 ^ (n + 2) := by
              rw [show n + 2 = n + 1 + 1 by omega, pow_succ]
              ring

/-- **Corollary 5.6** (arXiv:2111.00405, p.14): if `‖y₀‖ = √(2^h − 1)`, `‖y₀‖ ≤ √t·‖y‖`,
`‖M‖ ≥ 1/2` and `‖b‖ = 1`, then `κ_b(M) ≥ ½√((2h−1)/t)`. -/
theorem corollary56
    {t h : ℕ} (ht : 0 < t) (hh : 1 ≤ h)
    {y0Norm yNorm matNorm bNorm : ℝ}
    (hy0 : y0Norm = Real.sqrt ((2 : ℝ) ^ h - 1))
    (hbound : y0Norm ≤ Real.sqrt (t : ℝ) * yNorm)
    (hM : (1 : ℝ) / 2 ≤ matNorm) (hb : bNorm = 1) :
    (1 / 2) * Real.sqrt ((2 * (h : ℝ) - 1) / (t : ℝ)) ≤ tqlscn matNorm yNorm bNorm := by
  -- `2h - 1 ≤ 2^h - 1`, hence `√(2h-1) ≤ √(2^h-1) = ‖y₀‖`
  have hpow : (2 : ℝ) * (h : ℝ) ≤ (2 : ℝ) ^ h := by
    have hnat : 2 * h ≤ 2 ^ h := two_mul_le_two_pow h hh
    exact_mod_cast hnat
  have hrad0 : (0 : ℝ) ≤ 2 * (h : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    linarith
  have hsqrt_mono : Real.sqrt (2 * (h : ℝ) - 1) ≤ Real.sqrt ((2 : ℝ) ^ h - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hnorm_bound : Real.sqrt (2 * (h : ℝ) - 1) ≤ Real.sqrt (t : ℝ) * yNorm := by
    calc Real.sqrt (2 * (h : ℝ) - 1) ≤ Real.sqrt ((2 : ℝ) ^ h - 1) := hsqrt_mono
      _ = y0Norm := hy0.symm
      _ ≤ Real.sqrt (t : ℝ) * yNorm := hbound
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hratio : Real.sqrt ((2 * (h : ℝ) - 1) / (t : ℝ)) ≤ yNorm := by
    rw [Real.sqrt_div hrad0 (t : ℝ), div_le_iff₀ (Real.sqrt_pos.mpr htpos)]
    rw [mul_comm yNorm (Real.sqrt (t : ℝ))]
    exact hnorm_bound
  have hy : 0 ≤ yNorm := le_trans (Real.sqrt_nonneg _) hratio
  have hhalf : (1 / 2 : ℝ) * Real.sqrt ((2 * (h : ℝ) - 1) / (t : ℝ)) ≤ (1 / 2) * yNorm :=
    mul_le_mul_of_nonneg_left hratio (by norm_num)
  have hkappa : (1 / 2 : ℝ) * yNorm ≤ tqlscn matNorm yNorm bNorm := by
    unfold tqlscn
    rw [hb, div_one]
    exact mul_le_mul_of_nonneg_right hM hy
  linarith [hhalf, hkappa]

end Qatlib.Papers.MacaulayHHL21.MainResults.Corollary56
