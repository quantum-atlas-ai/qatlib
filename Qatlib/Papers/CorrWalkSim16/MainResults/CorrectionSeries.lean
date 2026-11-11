/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CorrWalkSim16.MainResults.ParitySymmetry
import Mathlib.Analysis.SpecificLimits.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# CorrWalkSim16, Lemmas 2 and 6: the correction series

Berry--Novo, arXiv:1606.03443v3, PDF pp. 9-10 (Lemma 2, Eqs. (52)-(63)) and
p. 14 (Lemma 6, Eqs. (86)-(95)).

The correction operator `V_C` is defined implicitly by

  `V^r = V_C (V_oaa)^r`,   `V_oaa = 3/2 Ṽ - 1/2 Ṽ Ṽ† Ṽ`,

so that, writing `∆ = V - Ṽ` and `W = 1/2 (V†∆ - ∆†Ṽ + V†∆V†∆ + V†∆∆†Ṽ)`
(Eq. (58)), one has the Neumann expansion

  `V_C = (1 - W)^{-r} = ∑_k (r+k-1 choose r-1) W^k`   (Eq. (57)).

This file formalizes the algebraic content of Lemma 2 and Lemma 6, namely

* `coeffL1_correctionKernel_le`: the paper's bound (Eq. (60))
  `s(W) ≤ 2δ + 9δ² + 6δ³ + δ⁴` for `s(Ṽ) ≤ 2`, `s(V) ≤ 2 + δ`, `s(∆) = δ`,
  obtained from Lemma 1 applied to the four terms of Eq. (58);
* `coeffL1_partialGeom_le`: the geometric series is bounded by
  `(1 - s W)^{-1}`, the truncations `ṼC` of the paper having
  `s(ṼC) ≤ s(V_C)`;
* `coeffL1_correction_le`: `s(ṼC) ≤ (1 - s W)^{-r}` for the `r`-fold
  compound segment;
* `lemma2_singleRound_s_bound` and `lemma6_secondRound_s_bound`: the
  `(1 - 2δ)^{-r}` shape of Lemmas 2 and 6, with `δ = s(∆)` in the first round
  and `δ = ∑_{|m|>N} |a_m|` in the second round.

The paper writes these as `≲` bounds "with higher-order terms in `∑_{|m|>M} |J_m(z)|`
omitted".  The statements below keep those higher-order terms explicitly, so
they are slightly sharper than the printed `≲` form.  The geometric series is
realized by its finite truncations, which is the object actually implemented by
Algorithms 1 and 2 (`ṼC` of Eq. (30)).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.CorrWalkSim16.MainResults

open scoped BigOperators

/-- The `k`-fold convolution power of a coefficient family: the coefficients of
`W^k`.  The zeroth power is the identity family `1 = U^0`. -/
def coeffPow (W : ℤ → ℂ) : ℕ → ℤ → ℂ
  | 0 => fun n => if n = 0 then (1 : ℂ) else 0
  | k + 1 => coeffMul (coeffPow W k) W

/-- The identity coefficient family is absolutely summable. -/
theorem summable_norm_delta :
    Summable fun n : ℤ => ‖(if n = 0 then (1 : ℂ) else 0)‖ := by
  have h : (fun n : ℤ => ‖(if n = 0 then (1 : ℂ) else 0)‖)
      = fun n : ℤ => if n = 0 then (1 : ℝ) else 0 := by
    funext n
    by_cases hn : n = 0 <;> simp [hn]
  rw [h]
  refine summable_of_ne_finset_zero (s := {0}) ?_
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [hn0]

/-- The identity family has weight one: `s(1) = 1`. -/
theorem coeffL1_delta :
    coeffL1 (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) = 1 := by
  rw [coeffL1, tsum_eq_single 0]
  · simp
  · intro b hb
    simp [hb]

/-- Powers of an absolutely summable family are absolutely summable. -/
theorem summable_norm_coeffPow (W : ℤ → ℂ) (hW : Summable fun n => ‖W n‖) :
    ∀ k : ℕ, Summable fun n => ‖coeffPow W k n‖
  | 0 => summable_norm_delta
  | k + 1 => summable_norm_coeffMul (coeffPow W k) W (summable_norm_coeffPow W hW k) hW

/-- Powers obey the submultiplicative bound `s(W^k) ≤ s(W)^k`. -/
theorem coeffL1_coeffPow_le (W : ℤ → ℂ) (hW : Summable fun n => ‖W n‖) :
    ∀ k : ℕ, coeffL1 (coeffPow W k) ≤ (coeffL1 W) ^ k
  | 0 => by
    show coeffL1 (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) ≤ (coeffL1 W) ^ 0
    rw [coeffL1_delta]
    simp
  | k + 1 => by
    have hk := summable_norm_coeffPow W hW k
    calc coeffL1 (coeffPow W (k + 1))
        = coeffL1 (coeffMul (coeffPow W k) W) := rfl
      _ ≤ coeffL1 (coeffPow W k) * coeffL1 W := coeffL1_conv_le _ _ hk hW
      _ ≤ (coeffL1 W) ^ k * coeffL1 W := by
            refine mul_le_mul_of_nonneg_right (coeffL1_coeffPow_le W hW k) (coeffL1_nonneg W)
      _ = (coeffL1 W) ^ (k + 1) := (pow_succ _ _).symm

/-- Finite sums of nonnegative summable families are summable. -/
theorem summable_finset_norm_sum {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℂ)
    (hF : ∀ i ∈ s, Summable fun n => ‖F i n‖) :
    Summable fun n => ∑ i ∈ s, ‖F i n‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have haS : Summable fun n => ‖F a n‖ := hF a (Finset.mem_insert_self a s)
      have hsS : Summable fun n => ∑ i ∈ s, ‖F i n‖ :=
        ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsplit : (fun n => ∑ i ∈ insert a s, ‖F i n‖)
          = fun n => ‖F a n‖ + ∑ i ∈ s, ‖F i n‖ := by
        funext n
        rw [Finset.sum_insert ha]
      rw [hsplit]
      exact haS.add hsS

/-- Finite sums of absolutely summable families are absolutely summable. -/
theorem summable_norm_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℂ)
    (hF : ∀ i ∈ s, Summable fun n => ‖F i n‖) :
    Summable fun n => ‖∑ i ∈ s, F i n‖ := by
  classical
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_finset_norm_sum s F hF)
  exact norm_sum_le _ _

/-- Lemma 1, Eq. (43), iterated over a finite sum. -/
theorem coeffL1_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℤ → ℂ)
    (hF : ∀ i ∈ s, Summable fun n => ‖F i n‖) :
    coeffL1 (fun n => ∑ i ∈ s, F i n) ≤ ∑ i ∈ s, coeffL1 (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffL1]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have haS : Summable fun n => ‖F a n‖ := hF a (Finset.mem_insert_self a s)
      have hsS : Summable fun n => ‖∑ i ∈ s, F i n‖ :=
        summable_norm_finset_sum s F fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsplit : (fun n => ∑ i ∈ insert a s, F i n)
          = fun n => F a n + ∑ i ∈ s, F i n := by
        funext n
        rw [Finset.sum_insert ha]
      rw [hsplit]
      refine le_trans (coeffL1_add_le (F a) (fun n => ∑ i ∈ s, F i n) haS hsS) ?_
      have := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
      linarith

/-- The partial geometric series of `W` truncated after `K` terms. -/
def partialGeom (W : ℤ → ℂ) (K : ℕ) : ℤ → ℂ :=
  fun n => ∑ k ∈ Finset.range (K + 1), coeffPow W k n

/-- The partial geometric series has weight at most `(1 - s W)^{-1}`. -/
theorem coeffL1_partialGeom_le (W : ℤ → ℂ) (hW : Summable fun n => ‖W n‖)
    (hw : coeffL1 W < 1) (K : ℕ) :
    coeffL1 (partialGeom W K) ≤ (1 - coeffL1 W)⁻¹ := by
  have h0 : 0 ≤ coeffL1 W := coeffL1_nonneg W
  have hgeom : Summable fun k : ℕ => (coeffL1 W) ^ k :=
    summable_geometric_of_lt_one h0 hw
  have hpiece : ∀ k ∈ Finset.range (K + 1), Summable fun n => ‖coeffPow W k n‖ :=
    fun k _ => summable_norm_coeffPow W hW k
  calc coeffL1 (partialGeom W K)
      ≤ ∑ k ∈ Finset.range (K + 1), coeffL1 (coeffPow W k) :=
        coeffL1_finset_sum_le _ _ hpiece
    _ ≤ ∑ k ∈ Finset.range (K + 1), (coeffL1 W) ^ k :=
        Finset.sum_le_sum fun k _ => coeffL1_coeffPow_le W hW k
    _ ≤ ∑' k : ℕ, (coeffL1 W) ^ k :=
        hgeom.sum_le_tsum _ (fun k _ => pow_nonneg h0 k)
    _ = (1 - coeffL1 W)⁻¹ := tsum_geometric_of_lt_one h0 hw

/-- Eq. (57) with the truncations of Eq. (30): the `r`-fold correction has
weight at most `(1 - s W)^{-r}`. -/
theorem coeffL1_correction_le (W : ℤ → ℂ) (hW : Summable fun n => ‖W n‖)
    (hw : coeffL1 W < 1) (K r : ℕ) :
    coeffL1 (coeffPow (partialGeom W K) r) ≤ (1 - coeffL1 W)⁻¹ ^ r := by
  have hgeo : Summable fun n => ‖partialGeom W K n‖ :=
    summable_norm_finset_sum _ _ fun k _ => summable_norm_coeffPow W hW k
  refine le_trans (coeffL1_coeffPow_le (partialGeom W K) hgeo r) ?_
  have hpos : 0 ≤ (1 - coeffL1 W)⁻¹ := by
    have : 0 < 1 - coeffL1 W := by linarith
    positivity
  exact pow_le_pow_left₀ (coeffL1_nonneg _) (coeffL1_partialGeom_le W hW hw K) r

/-- Eq. (58): the operator `W` of the Neumann expansion of `V_C`.  The family
`dV` is `∆ = V - Ṽ`; its adjoint is `coeffStar dV`. -/
def correctionKernel (V Vt dV : ℤ → ℂ) : ℤ → ℂ :=
  fun n => (2⁻¹ : ℂ) *
    ((coeffMul (coeffStar V) dV n - coeffMul (coeffStar dV) Vt n)
      + (coeffMul (coeffMul (coeffStar V) dV) (coeffMul (coeffStar V) dV) n
          + coeffMul (coeffMul (coeffMul (coeffStar V) dV) (coeffStar dV)) Vt n))

/-- Eq. (60): `s(W) ≤ 2δ + 9δ² + 6δ³ + δ⁴` for `s(Ṽ) ≤ 2`,
`s(V) ≤ 2 + δ` and `s(∆) = δ`. -/
theorem coeffL1_correctionKernel_le (V Vt dV : ℤ → ℂ)
    (hV : Summable fun n => ‖V n‖) (hVt : Summable fun n => ‖Vt n‖)
    (hdV : Summable fun n => ‖dV n‖)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hVle : coeffL1 V ≤ 2 + δ) (hVtle : coeffL1 Vt ≤ 2)
    (hdVle : coeffL1 dV ≤ δ) :
    coeffL1 (correctionKernel V Vt dV) ≤ 2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4 := by
  set A := coeffMul (coeffStar V) dV with hA
  set B := coeffMul (coeffStar dV) Vt with hB
  set C := coeffMul A A with hC
  set D := coeffMul (coeffMul A (coeffStar dV)) Vt with hD
  have hstarV : Summable fun n => ‖coeffStar V n‖ := summable_norm_coeffStar V hV
  have hstarDV : Summable fun n => ‖coeffStar dV n‖ := summable_norm_coeffStar dV hdV
  have hA' : Summable fun n => ‖A n‖ := summable_norm_coeffMul _ _ hstarV hdV
  have hB' : Summable fun n => ‖B n‖ := summable_norm_coeffMul _ _ hstarDV hVt
  have hC' : Summable fun n => ‖C n‖ := summable_norm_coeffMul _ _ hA' hA'
  have hAD : Summable fun n => ‖coeffMul A (coeffStar dV) n‖ :=
    summable_norm_coeffMul _ _ hA' hstarDV
  have hD' : Summable fun n => ‖D n‖ := summable_norm_coeffMul _ _ hAD hVt
  have hAB : coeffL1 (fun n => A n - B n) ≤ coeffL1 A + coeffL1 B := by
    have hnegB : Summable fun n => ‖(fun n => -B n) n‖ := by simpa using hB'
    have h1 : coeffL1 (fun n => -B n) = coeffL1 B := by
      have := coeffL1_smul B (-1 : ℂ)
      simpa using this
    have h2 := coeffL1_add_le A (fun n => -B n) hA' hnegB
    calc coeffL1 (fun n => A n - B n) = coeffL1 (fun n => A n + -B n) := rfl
      _ ≤ coeffL1 A + coeffL1 (fun n => -B n) := h2
      _ = coeffL1 A + coeffL1 B := by rw [h1]
  have hCD : coeffL1 (fun n => C n + D n) ≤ coeffL1 C + coeffL1 D :=
    coeffL1_add_le C D hC' hD'
  have hABs : Summable fun n => ‖(fun n => A n - B n) n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by simpa [sub_eq_add_neg] using norm_add_le (A n) (-B n)) (hA'.add hB')
  have hCDs : Summable fun n => ‖(fun n => C n + D n) n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_add_le _ _) (hC'.add hD')
  have hquad : coeffL1 (fun n => (A n - B n) + (C n + D n))
      ≤ coeffL1 A + coeffL1 B + coeffL1 C + coeffL1 D := by
    have h := coeffL1_add_le (fun n => A n - B n) (fun n => C n + D n) hABs hCDs
    linarith
  have hkern : coeffL1 (correctionKernel V Vt dV)
      ≤ (2⁻¹) * coeffL1 (fun n => (A n - B n) + (C n + D n)) := by
    have hfun : (fun n => (2⁻¹ : ℂ) * ((A n - B n) + (C n + D n)))
        = correctionKernel V Vt dV := by
      funext n
      simp only [correctionKernel, ← hA, ← hB, ← hC, ← hD]
    rw [← hfun]
    have := coeffL1_smul (fun n => (A n - B n) + (C n + D n)) (2⁻¹ : ℂ)
    rw [this]
    have hnorm : ‖(2⁻¹ : ℂ)‖ = 2⁻¹ := by norm_num
    rw [hnorm]
  have hA2 : 0 ≤ (2 + δ) * δ := by nlinarith
  have hsA : coeffL1 A ≤ (2 + δ) * δ := by
    have h := coeffL1_conv_le _ _ hstarV hdV
    rw [coeffL1_coeffStar] at h
    calc coeffL1 A ≤ coeffL1 V * coeffL1 dV := h
      _ ≤ (2 + δ) * δ := by
          refine mul_le_mul hVle hdVle (coeffL1_nonneg _) ?_
          linarith
  have hsB : coeffL1 B ≤ δ * 2 := by
    have h := coeffL1_conv_le _ _ hstarDV hVt
    rw [coeffL1_coeffStar] at h
    calc coeffL1 B ≤ coeffL1 dV * coeffL1 Vt := h
      _ ≤ δ * 2 := by
          refine mul_le_mul hdVle hVtle (coeffL1_nonneg _) (by linarith)
  have hsC : coeffL1 C ≤ ((2 + δ) * δ) ^ 2 := by
    have h := coeffL1_conv_le _ _ hA' hA'
    calc coeffL1 C ≤ coeffL1 A * coeffL1 A := h
      _ ≤ ((2 + δ) * δ) ^ 2 := by
          rw [pow_two]
          exact mul_self_le_mul_self (coeffL1_nonneg A) hsA
  have hsAD : coeffL1 (coeffMul A (coeffStar dV)) ≤ ((2 + δ) * δ) * δ := by
    have h := coeffL1_conv_le _ _ hA' hstarDV
    rw [coeffL1_coeffStar] at h
    calc coeffL1 (coeffMul A (coeffStar dV)) ≤ coeffL1 A * coeffL1 dV := h
      _ ≤ ((2 + δ) * δ) * δ := by
          refine mul_le_mul hsA hdVle (coeffL1_nonneg _) hA2
  have hsD : coeffL1 D ≤ ((2 + δ) * δ) * δ * 2 := by
    have h := coeffL1_conv_le _ _ hAD hVt
    calc coeffL1 D ≤ coeffL1 (coeffMul A (coeffStar dV)) * coeffL1 Vt := h
      _ ≤ ((2 + δ) * δ) * δ * 2 := by
          refine mul_le_mul hsAD hVtle (coeffL1_nonneg _) ?_
          nlinarith
  have hsum : coeffL1 A + coeffL1 B + coeffL1 C + coeffL1 D
      ≤ (2 + δ) * δ + δ * 2 + ((2 + δ) * δ) ^ 2 + ((2 + δ) * δ) * δ * 2 := by
    linarith
  have hpoly : (2⁻¹) * ((2 + δ) * δ + δ * 2 + ((2 + δ) * δ) ^ 2 + ((2 + δ) * δ) * δ * 2)
      = 2 * δ + (9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4) / 2 := by
    ring
  have hfin : 2 * δ + (9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4) / 2
      ≤ 2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4 := by nlinarith
  calc coeffL1 (correctionKernel V Vt dV)
      ≤ (2⁻¹) * coeffL1 (fun n => (A n - B n) + (C n + D n)) := hkern
    _ ≤ (2⁻¹) * (coeffL1 A + coeffL1 B + coeffL1 C + coeffL1 D) := by
        refine mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ ≤ (2⁻¹) * ((2 + δ) * δ + δ * 2 + ((2 + δ) * δ) ^ 2 + ((2 + δ) * δ) * δ * 2) := by
        refine mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * δ + (9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4) / 2 := hpoly
    _ ≤ 2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4 := hfin

/-- Lemma 2, Eq. (51), in the sharp form that keeps the omitted higher-order
terms: for a correction kernel with `s(W) ≤ 2δ + 9δ² + 6δ³ + δ⁴ < 1`, the
truncated correction `ṼC` has `s(ṼC) ≤ (1 - (2δ + 9δ² + 6δ³ + δ⁴))^{-r}`. -/
theorem lemma2_singleRound_s_bound (W : ℤ → ℂ) (δ : ℝ)
    (hW : Summable fun n => ‖W n‖) (_hδ : 0 ≤ δ)
    (hWle : coeffL1 W ≤ 2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4)
    (hlt : 2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4 < 1) (K r : ℕ) :
    coeffL1 (coeffPow (partialGeom W K) r)
      ≤ (1 - (2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4))⁻¹ ^ r := by
  have hw : coeffL1 W < 1 := lt_of_le_of_lt hWle hlt
  refine le_trans (coeffL1_correction_le W hW hw K r) ?_
  have hpos : 0 < 1 - (2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4) := by linarith
  have hwpos : 0 < 1 - coeffL1 W := by linarith
  have hinv : (1 - coeffL1 W)⁻¹ ≤ (1 - (2 * δ + 9 * δ ^ 2 + 6 * δ ^ 3 + δ ^ 4))⁻¹ := by
    rw [inv_le_inv₀ hwpos hpos]
    linarith
  exact pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hwpos)) hinv r

/-- Lemma 2 in the paper's `(1 - 2δ)^{-r}` shape: if the kernel satisfies
`s(W) ≤ 2δ` (the leading term of Eq. (60)) then the correction weight is at
most `(1 - 2δ)^{-r}`. -/
theorem lemma2_singleRound_twoDelta_s_bound (W : ℤ → ℂ) (δ : ℝ)
    (hW : Summable fun n => ‖W n‖) (_hδ : 0 ≤ δ) (hδ1 : δ < 1 / 2)
    (hWle : coeffL1 W ≤ 2 * δ) (K r : ℕ) :
    coeffL1 (coeffPow (partialGeom W K) r) ≤ (1 - 2 * δ)⁻¹ ^ r := by
  have hw : coeffL1 W < 1 := by linarith
  refine le_trans (coeffL1_correction_le W hW hw K r) ?_
  have hpos : 0 < 1 - 2 * δ := by linarith
  have hwpos : 0 < 1 - coeffL1 W := by linarith
  have hinv : (1 - coeffL1 W)⁻¹ ≤ (1 - 2 * δ)⁻¹ := by
    rw [inv_le_inv₀ hwpos hpos]
    linarith
  exact pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hwpos)) hinv r

/-- Lemma 6, Eq. (85): in the second round of correction the weight of `V_C'`
is bounded by `(1 - 2δ')^{-r'}` with `δ' = ∑_{|m|>N} |a_m|`, the tail of the
first-round coefficients. -/
theorem lemma6_secondRound_s_bound (W' : ℤ → ℂ) (δ' : ℝ)
    (hW' : Summable fun n => ‖W' n‖) (hδ' : 0 ≤ δ') (hδ'1 : δ' < 1 / 2)
    (hW'le : coeffL1 W' ≤ 2 * δ') (K r' : ℕ) :
    coeffL1 (coeffPow (partialGeom W' K) r') ≤ (1 - 2 * δ')⁻¹ ^ r' :=
  lemma2_singleRound_twoDelta_s_bound W' δ' hW' hδ' hδ'1 hW'le K r'

end Qatlib.Papers.CorrWalkSim16.MainResults
