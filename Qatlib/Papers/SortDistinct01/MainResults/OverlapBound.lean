/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace ComplexConjugate ComplexOrder

namespace Qatlib.Papers.SortDistinct01.MainResults.OverlapBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem overlap_numeric_bound {p q ε : ℝ}
    (hp : 1 - ε ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq : q ≤ ε)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) :
    Real.sqrt p * Real.sqrt q + Real.sqrt (1 - p) * Real.sqrt (1 - q)
      ≤ 2 * Real.sqrt (ε * (1 - ε)) := by
  have hp0 : 0 ≤ p := by linarith
  have h1p : 0 ≤ 1 - p := by linarith
  have h1q : 0 ≤ 1 - q := by linarith
  have h1ε : 0 ≤ 1 - ε := by linarith
  have hε1ε : 0 ≤ ε * (1 - ε) := mul_nonneg hε0 h1ε
  have hpq_nonneg : 0 ≤ p * q := mul_nonneg hp0 hq0
  have hp1p_nonneg : 0 ≤ p * (1 - p) := mul_nonneg hp0 h1p
  have hq1q_nonneg : 0 ≤ q * (1 - q) := mul_nonneg hq0 h1q

  set A : ℝ := Real.sqrt (p * q) with hA
  set B : ℝ := Real.sqrt ((1 - p) * (1 - q)) with hB
  have hAeq : Real.sqrt p * Real.sqrt q = A := by
    rw [hA]; exact (Real.sqrt_mul hp0 q).symm
  have hBeq : Real.sqrt (1 - p) * Real.sqrt (1 - q) = B := by
    rw [hB]; exact (Real.sqrt_mul h1p (1 - q)).symm
  rw [hAeq, hBeq]
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hg0 : 0 ≤ A + B := by positivity
  have hA2 : A ^ 2 = p * q := Real.sq_sqrt hpq_nonneg
  have hB2 : B ^ 2 = (1 - p) * (1 - q) := Real.sq_sqrt (mul_nonneg h1p h1q)

  have hAB : A * B = Real.sqrt ((p * q) * ((1 - p) * (1 - q))) := by
    rw [hA, hB, ← Real.sqrt_mul hpq_nonneg ((1 - p) * (1 - q))]
  have hrearr : (p * q) * ((1 - p) * (1 - q)) = (p * (1 - p)) * (q * (1 - q)) := by
    ring

  have hp1p_le : p * (1 - p) ≤ ε * (1 - ε) := by
    have h1 : 0 ≤ p - ε := by linarith
    have h2 : 0 ≤ p + ε - 1 := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hq1q_le : q * (1 - q) ≤ ε * (1 - ε) := by
    have h1 : q - ε ≤ 0 := by linarith
    have h2 : q + ε - 1 ≤ 0 := by linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos h1 h2]

  have hcross_le : Real.sqrt ((p * (1 - p)) * (q * (1 - q))) ≤ ε * (1 - ε) := by
    rw [Real.sqrt_le_left hε1ε]
    calc (p * (1 - p)) * (q * (1 - q))
        ≤ (ε * (1 - ε)) * (ε * (1 - ε)) :=
          mul_le_mul hp1p_le hq1q_le hq1q_nonneg hε1ε
      _ = (ε * (1 - ε)) ^ 2 := by ring

  have hdiag : p * q + (1 - p) * (1 - q) ≤ 2 * ε - 2 * ε ^ 2 := by
    have h1 : 0 ≤ (ε - (1 - p)) * (1 - 2 * q) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (ε - q) * (1 - 2 * ε) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [h1, h2]
  have hsq_bound : (A + B) ^ 2 ≤ 4 * ε * (1 - ε) := by
    have hexp : (A + B) ^ 2 = p * q + (1 - p) * (1 - q) + 2 * (A * B) := by
      have h : (A + B) ^ 2 = A ^ 2 + 2 * (A * B) + B ^ 2 := by ring
      rw [h, hA2, hB2]; ring
    rw [hexp]
    have hAB' : A * B = Real.sqrt ((p * (1 - p)) * (q * (1 - q))) := by
      rw [hAB, hrearr]
    rw [hAB']
    nlinarith [hdiag, hcross_le]
  have hrhs : (2 * Real.sqrt (ε * (1 - ε))) ^ 2 = 4 * ε * (1 - ε) := by
    have hsq := Real.sq_sqrt hε1ε
    nlinarith [hsq]
  have hrhs0 : 0 ≤ 2 * Real.sqrt (ε * (1 - ε)) := by positivity
  have hsq' : (A + B) ^ 2 ≤ (2 * Real.sqrt (ε * (1 - ε))) ^ 2 := by
    rw [hrhs]; exact hsq_bound
  have hfinal := Real.sqrt_le_sqrt hsq'
  rwa [Real.sqrt_sq hg0, Real.sqrt_sq hrhs0] at hfinal

theorem lemma4_overlap_bound
    (P : E →L[ℂ] E)
    (hidem : ∀ x, P (P x) = P x)
    (hself : ∀ x y, ⟪P x, y⟫ = ⟪x, P y⟫)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (hsucc_u : 1 - ε ≤ ‖P u‖ ^ 2) (hsucc_v : ‖P v‖ ^ 2 ≤ ε) :
    ‖⟪u, v⟫‖ ≤ 2 * Real.sqrt (ε * (1 - ε)) := by

  have hproj_self_apply : ∀ w : E, ⟪P w, P w⟫ = ⟪P w, w⟫ := by
    intro w
    have h := hself (P w) w
    rw [hidem w] at h
    exact h.symm
  have hnorm_le : ∀ w : E, ‖P w‖ ≤ ‖w‖ := by
    intro w
    have hsq : ‖P w‖ ^ 2 ≤ ‖P w‖ * ‖w‖ := by
      calc ‖P w‖ ^ 2 = RCLike.re ⟪P w, P w⟫ := (inner_self_eq_norm_sq (P w)).symm
        _ = RCLike.re ⟪P w, w⟫ := by rw [hproj_self_apply w]
        _ ≤ ‖⟪P w, w⟫‖ := RCLike.re_le_norm _
        _ ≤ ‖P w‖ * ‖w‖ := norm_inner_le_norm _ _
    by_cases h0 : ‖P w‖ = 0
    · rw [h0]; positivity
    · have hpos : 0 < ‖P w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h2 : ‖P w‖ * ‖P w‖ ≤ ‖P w‖ * ‖w‖ := by
        rw [← pow_two]; exact hsq
      exact le_of_mul_le_mul_left h2 hpos
  have hp1 : ‖P u‖ ^ 2 ≤ 1 := by
    have hn : ‖P u‖ ≤ 1 := by simpa [hu] using hnorm_le u
    have hmul : ‖P u‖ * ‖P u‖ ≤ 1 * 1 := mul_self_le_mul_self (norm_nonneg _) hn
    nlinarith [hmul]

  have horth_u : ⟪u - P u, P u⟫ = 0 := by
    rw [inner_sub_left, hproj_self_apply u, hself u u, sub_self]
  have horth_v : ⟪v - P v, P v⟫ = 0 := by
    rw [inner_sub_left, hproj_self_apply v, hself v v, sub_self]

  have hpy_u : ‖u‖ ^ 2 = ‖u - P u‖ ^ 2 + ‖P u‖ ^ 2 := by
    have horth' : ⟪P u, u - P u⟫ = 0 := by
      rw [inner_sub_right, hproj_self_apply u, sub_self]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P u) (u - P u) horth'
    have hsum : P u + (u - P u) = u := by abel
    rw [hsum] at h
    nlinarith [h]
  have hpy_v : ‖v‖ ^ 2 = ‖v - P v‖ ^ 2 + ‖P v‖ ^ 2 := by
    have horth' : ⟪P v, v - P v⟫ = 0 := by
      rw [inner_sub_right, hproj_self_apply v, sub_self]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (v - P v) horth'
    have hsum : P v + (v - P v) = v := by abel
    rw [hsum] at h
    nlinarith [h]
  have hlen_u : ‖u - P u‖ ^ 2 = 1 - ‖P u‖ ^ 2 := by
    have h := hpy_u
    rw [hu] at h
    nlinarith [h]
  have hlen_v : ‖v - P v‖ ^ 2 = 1 - ‖P v‖ ^ 2 := by
    have h := hpy_v
    rw [hv] at h
    nlinarith [h]

  have hPu : ⟪P u, P v⟫ = ⟪P u, v⟫ := by
    have h := hself (P u) v
    rw [hidem] at h
    exact h.symm
  have hcross1 : ⟪P u, v - P v⟫ = 0 := by
    rw [inner_sub_right, hPu, sub_self]
  have hcross2 : ⟪u - P u, P v⟫ = 0 := by
    rw [inner_sub_left, ← hself u v, hPu, sub_self]
  have hdecomp : ⟪u, v⟫ = ⟪P u, P v⟫ + ⟪u - P u, v - P v⟫ := by
    have hu' : u = P u + (u - P u) := by abel
    have hv' : v = P v + (v - P v) := by abel
    calc ⟪u, v⟫
        = ⟪P u, P v⟫ + ⟪P u, v - P v⟫ + ⟪u - P u, P v⟫
            + ⟪u - P u, v - P v⟫ := by
          conv_lhs => rw [hu', hv']
          rw [inner_add_left, inner_add_right, inner_add_right]
          abel
      _ = ⟪P u, P v⟫ + ⟪u - P u, v - P v⟫ := by
          rw [hcross1, hcross2]; ring

  calc ‖⟪u, v⟫‖
      = ‖⟪P u, P v⟫ + ⟪u - P u, v - P v⟫‖ := by rw [hdecomp]
    _ ≤ ‖⟪P u, P v⟫‖ + ‖⟪u - P u, v - P v⟫‖ := norm_add_le _ _
    _ ≤ Real.sqrt (‖P u‖ ^ 2) * Real.sqrt (‖P v‖ ^ 2)
          + Real.sqrt (‖u - P u‖ ^ 2) * Real.sqrt (‖v - P v‖ ^ 2) := by
        apply add_le_add
        · rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
          exact norm_inner_le_norm _ _
        · rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
          exact norm_inner_le_norm _ _
    _ = Real.sqrt (‖P u‖ ^ 2) * Real.sqrt (‖P v‖ ^ 2)
          + Real.sqrt (1 - ‖P u‖ ^ 2) * Real.sqrt (1 - ‖P v‖ ^ 2) := by
        rw [hlen_u, hlen_v]
    _ ≤ 2 * Real.sqrt (ε * (1 - ε)) :=
        overlap_numeric_bound hsucc_u hp1 (by positivity) hsucc_v hε0 hε1

end Qatlib.Papers.SortDistinct01.MainResults.OverlapBound
