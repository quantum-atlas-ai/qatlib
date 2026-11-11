/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# VarTimeSearch23 — stage model for Algorithm 1 and Lemma 2

Source: Ambainis, Kokainis, Vihrovs, *Improved Algorithm and Lower Bound for
Variable Time Quantum Search*, fixed arXiv:2302.06749v3 (2023-08-02).

This module fixes the amplitude bookkeeping of Algorithm 1 (§3.2, p.5) that
Lemma 2 (p.5, Eq. (3.1); proof in Appendix A, p.13) is about:

* `S j` is the source's `S_j = {i ∈ [n] : (T_j < t_i) ∨ (t_i ≤ T_j ∧ x_i = 1)}`
  for the stage index `j`; `S_j` is decreasing in `j` and `s_j = |S_j|`;
* `beta j i` is the amplitude `β_i^j` of the source's `|i, a_i^j⟩` after `A_j`;
* `alpha j` is the source's `α_j`, with `sin² α_j = ∑_{i ∈ S_j} (β_i^j)²`;
* the amplification step (A.1) multiplies the amplitude on `S_j` by
  `sin(3 α_j) / sin α_j`.

The source indexes the stages `1, …, ℓ` (the base procedure `A_1` prepares the
uniform superposition and applies `CT_1`), so this file indexes them from `1`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Qatlib.Papers.VarTimeSearch23.MainResults

/-- Stage bookkeeping of the source's Algorithm 1 (§3.2) for a universe
`Fin n`.  `S j` is `S_j`, `beta j` is the amplitude vector after `A_j`, and
`alpha j` is `α_j`; the fields are exactly the source's definitions plus the
amplification recurrence (A.1) on the successful subspace. -/
structure VtsStageRun (n : ℕ) where
  /-- Number of stages `ℓ` of the source's Algorithm 1. -/
  ell : ℕ
  /-- The decreasing sets `S_j`. -/
  S : ℕ → Finset (Fin n)
  /-- The amplitude `β_i^j` after procedure `A_j`. -/
  beta : ℕ → Fin n → ℝ
  /-- The angle `α_j`. -/
  alpha : ℕ → ℝ
  /-- Source proof of Lemma 2: `[n] = S_0 ⊇ S_1 ⊇ …`, quoted in the
  decreasing form `S_{j+1} ⊆ S_j` used by the amplitude induction. -/
  S_anti : ∀ j : ℕ, 1 ≤ j → S (j + 1) ⊆ S j
  /-- Base case: `A_1` prepares the uniform superposition
  `∑_i n^{-1/2} |i⟩` and applies `CT_1`. -/
  beta_one : ∀ i : Fin n, beta 1 i = (Real.sqrt (n : ℝ))⁻¹
  /-- Source Eq. (A.1): the amplification `A_j(1)` multiplies the amplitude of
  every `i ∈ S_j` by `sin(3 α_j) / sin α_j`. -/
  beta_step : ∀ (j : ℕ) (i : Fin n), 1 ≤ j → i ∈ S j →
    beta (j + 1) i = beta j i * (Real.sin (3 * alpha j) / Real.sin (alpha j))
  /-- Source's definition `sin² α_j = ∑_{i ∈ S_j} |β_i^j|²`. -/
  sin_sq_alpha : ∀ j : ℕ, 1 ≤ j →
    Real.sin (alpha j) ^ 2 = ∑ i ∈ S j, (beta j i) ^ 2
  /-- `s_j > 0`: the source is in the regime `m = |M| ≥ 1`, and
  `S_j ⊇ S_ℓ = M`. -/
  S_pos : ∀ j : ℕ, 1 ≤ j → 0 < (S j).card

namespace VtsStageRun

variable {n : ℕ} (R : VtsStageRun n)

/-- The stage gain `sin(3 α_j) / sin α_j` of the source's Eq. (A.1). -/
def ratio (j : ℕ) : ℝ := Real.sin (3 * R.alpha j) / Real.sin (R.alpha j)

/-- The product `∏_{k=1}^{j-1} sin(3 α_k)/sin α_k` appearing in Eq. (3.1). -/
def paperProd (j : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 (j - 1), R.ratio k

/-- Source Lemma 2, Eq. (3.1), p.5: the empty product at the base stage,
`P_1 = ∏_{k=1}^{0} sin(3α_k)/sin α_k = 1`. -/
theorem paperProd_one : R.paperProd 1 = 1 := by
  unfold VtsStageRun.paperProd
  apply Finset.prod_eq_one
  intro k hk
  rw [Finset.mem_Icc] at hk
  omega

/-- Source Lemma 2, Eq. (3.1)/Eq. (A.1), p.5 and p.13: the stage recurrence of
the product, `P_{j+1} = P_j · (sin 3α_j / sin α_j)`. -/
theorem paperProd_succ (j : ℕ) (hj : 1 ≤ j) :
    R.paperProd (j + 1) = R.paperProd j * R.ratio j := by
  have hsub : j + 1 - 1 = j := by omega
  have hshift : j = (j - 1) + 1 := by omega
  unfold VtsStageRun.paperProd
  rw [hsub]
  conv_lhs => rw [hshift]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ (j - 1) + 1) (fun k => R.ratio k)]
  rw [show (j - 1) + 1 = j from hshift.symm]

/-- Source Lemma 2 (Appendix A, p.13), amplitude form: for every `j ≥ 1` and
every `i ∈ S_j`, `β_i^j = n^{-1/2} ∏_{k=1}^{j-1} sin(3 α_k)/sin α_k`.  This is
the source's statement that all amplitudes on `S_j` are equal. -/
theorem amplitude_eq (j : ℕ) (hj : 1 ≤ j) (i : Fin n) (hi : i ∈ R.S j) :
    R.beta j i = (Real.sqrt (n : ℝ))⁻¹ * R.paperProd j := by
  induction j, hj using Nat.le_induction with
  | base =>
      rw [R.beta_one i, paperProd_one R, mul_one]
  | succ j hj ih =>
      have hi' : i ∈ R.S j := R.S_anti j hj hi
      rw [R.beta_step j i hj hi', ih hi', paperProd_succ R j hj]
      rw [show Real.sin (3 * R.alpha j) / Real.sin (R.alpha j) = R.ratio j from rfl]
      ring

/-- Source Lemma 2, first part (Eq. (3.1), p.5): for every `j ≥ 1`,
`sin² α_j = (s_j / n) ∏_{k=1}^{j-1} (sin(3 α_k)/sin α_k)²`. -/
theorem lemma2_angle_identity (j : ℕ) (hj : 1 ≤ j) :
    Real.sin (R.alpha j) ^ 2
      = ((R.S j).card : ℝ) / (n : ℝ) * (R.paperProd j) ^ 2 := by
  rw [R.sin_sq_alpha j hj]
  have hterm : ∀ i ∈ R.S j,
      (R.beta j i) ^ 2
        = ((Real.sqrt (n : ℝ))⁻¹ * R.paperProd j) ^ 2 := by
    intro i hi
    rw [R.amplitude_eq j hj i hi]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  have hsqrt : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  calc ((R.S j).card : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ * R.paperProd j) ^ 2
      = ((R.S j).card : ℝ) * (((Real.sqrt (n : ℝ))⁻¹) ^ 2
          * (R.paperProd j) ^ 2) := by rw [mul_pow]
    _ = ((R.S j).card : ℝ) * (((n : ℝ))⁻¹ * (R.paperProd j) ^ 2) := by
          rw [hsqrt]
    _ = ((R.S j).card : ℝ) / (n : ℝ) * (R.paperProd j) ^ 2 := by
          rw [div_eq_mul_inv]; ring

/-- Source Lemma 2, second part (p.5): for every `i ∈ S_j` the amplitude is
`sin α_j / √s_j`.  The statement is made in the source's positive-amplitude
convention (`sin α_j ≥ 0`, `β_i^j ≥ 0`), which holds for the source's angles in
`(0, π/2)`. -/
theorem lemma2_uniform_amplitude (j : ℕ) (hj : 1 ≤ j) (i : Fin n)
    (hi : i ∈ R.S j) (halpha : 0 ≤ Real.sin (R.alpha j))
    (hbeta : 0 ≤ R.beta j i) :
    R.beta j i = Real.sin (R.alpha j) / Real.sqrt ((R.S j).card : ℝ) := by
  have hs : (0 : ℝ) < ((R.S j).card : ℝ) := by
    exact_mod_cast R.S_pos j hj
  have hkey : R.beta j i ^ 2
      = (Real.sin (R.alpha j) / Real.sqrt ((R.S j).card : ℝ)) ^ 2 := by
    rw [R.amplitude_eq j hj i hi]
    have hsin := R.lemma2_angle_identity j hj
    have hsqrt_n : ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have hsqrt_s : (Real.sqrt ((R.S j).card : ℝ)) ^ 2 = ((R.S j).card : ℝ) :=
      Real.sq_sqrt (le_of_lt hs)
    calc ((Real.sqrt (n : ℝ))⁻¹ * R.paperProd j) ^ 2
        = (((Real.sqrt (n : ℝ))⁻¹) ^ 2) * (R.paperProd j) ^ 2 := by
            rw [mul_pow]
      _ = ((n : ℝ))⁻¹ * (R.paperProd j) ^ 2 := by rw [hsqrt_n]
      _ = (Real.sin (R.alpha j)) ^ 2 / ((R.S j).card : ℝ) := by
            rw [eq_div_iff (ne_of_gt hs), hsin, div_eq_mul_inv]
            ring
      _ = (Real.sin (R.alpha j) / Real.sqrt ((R.S j).card : ℝ)) ^ 2 := by
            rw [div_pow, hsqrt_s]
  calc R.beta j i = Real.sqrt ((R.beta j i) ^ 2) := (Real.sqrt_sq hbeta).symm
    _ = Real.sqrt ((Real.sin (R.alpha j) / Real.sqrt ((R.S j).card : ℝ)) ^ 2) := by
          rw [hkey]
    _ = Real.sin (R.alpha j) / Real.sqrt ((R.S j).card : ℝ) :=
          Real.sqrt_sq (div_nonneg halpha (Real.sqrt_nonneg _))

end VtsStageRun

end Qatlib.Papers.VarTimeSearch23.MainResults
