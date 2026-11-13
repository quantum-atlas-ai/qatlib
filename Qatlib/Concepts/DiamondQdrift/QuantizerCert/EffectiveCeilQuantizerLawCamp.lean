/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.QuantizerCert.EffectiveCeilQuantizerLawStat

/-!
# Certified ceiling quantizer bounds

This module proves the precision, mass, and probability approximation guarantees for
`effectiveCeilQuantizer`. Rational lower approximation errors provide a sufficient precision
certificate and an explicit bound on the selected precision.

The normalized integer weights approximate the target law with total absolute error at most `4 *
L / M`, supporting finite sampling in the qDRIFT setting of [Campbell2019].

## Main statements

* `ceilQuantizerCert_of_pow_bound`: a sufficient binary precision bound.
* `effectiveCeilQuantizer_mass_and_l1`: mass and normalized probability error bounds.
* `effectiveCeilQuantizerLaw`: the complete effective quantizer specification.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Qatlib.Concepts.FairRandomBits.RationalReject

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Matrix
open scoped Classical BigOperators

/-- The rational lower mass is at most the target mass, with deficit at most `L * 2⁻ᵏ`. -/
private theorem rat_lower_mass_bounds {L : ℕ} {h : Fin L → ℝ} {q : Fin L → ℕ → ℚ}
    (hor : ∀ j, RatLowerOracle (h j) (q j)) (k : ℕ) :
    ratLowerMass q k ≤ ∑ j, h j ∧
      (∑ j, h j)-ratLowerMass q k ≤ (L : ℝ)*((2 : ℝ)⁻¹)^k := by
  refine ⟨Finset.sum_le_sum (fun j _ => (hor j k).2.1), ?_⟩
  have he : (∑ j, h j)-ratLowerMass q k = ∑ j, (h j-(q j k : ℝ)) := by
    rw [ratLowerMass, ← Finset.sum_sub_distrib]
  rw [he]
  calc (∑ j, (h j-(q j k : ℝ))) ≤ ∑ j, ((2 : ℝ)⁻¹)^k :=
        Finset.sum_le_sum (fun j _ => (hor j k).2.2)
    _ = (L : ℝ)*((2 : ℝ)⁻¹)^k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The precision inequality `L * (2 * M + 3) ≤ (∑ j, h j) * 2 ^ k` ensures the ceiling
quantizer certificate. -/
theorem ceilQuantizerCert_of_pow_bound {L M : ℕ} {h : Fin L → ℝ} {q : Fin L → ℕ → ℚ}
    (hor : ∀ j, RatLowerOracle (h j) (q j))
    {k : ℕ} (hk : (L : ℝ)*(2*(M : ℝ)+3) ≤ (∑ j, h j)*((2 : ℝ)^k)) :
    ceilQuantizerCert M q k := by
  obtain ⟨hup, hdef⟩ := rat_lower_mass_bounds hor k
  have hpow : ((2 : ℝ)^k)*((2 : ℝ)⁻¹)^k = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (by positivity : ((2 : ℝ)^k) ≠ 0)]
  have h3 : (L : ℝ)*(2*(M : ℝ)+3)*((2 : ℝ)⁻¹)^k ≤ ∑ j, h j := by
    calc (L : ℝ)*(2*(M : ℝ)+3)*((2 : ℝ)⁻¹)^k
        ≤ (∑ j, h j)*((2 : ℝ)^k)*((2 : ℝ)⁻¹)^k :=
          mul_le_mul_of_nonneg_right hk (by positivity)
      _ = ∑ j, h j := by rw [mul_assoc, hpow, mul_one]
  have hsplit : (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k+(L : ℝ)*((2 : ℝ)⁻¹)^k
      = (L : ℝ)*(2*(M : ℝ)+3)*((2 : ℝ)⁻¹)^k := by ring
  rw [← hsplit] at h3
  have hgoal : (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k ≤ ratLowerMass q k := by
    linarith only [h3, hdef]
  exact hgoal

/-- Under valid lower oracles, positive target mass and scale, and the precision certificate,
total integer weight lies between `M` and `M + 2 * L`, and normalized law error is at most
`4 * L / M`. -/
theorem effectiveCeilQuantizer_mass_and_l1 {L M : ℕ} {h : Fin L → ℝ}
    {q : Fin L → ℕ → ℚ} {k : ℕ} (hor : ∀ j, RatLowerOracle (h j) (q j))
    (hlam : 0 < ∑ j, h j) (hM : 0 < M) (hcert : ceilQuantizerCert M q k) :
    (M ≤ weightTotal (effectiveCeilQuantizer q k M) ∧
      (∑ j, ((effectiveCeilQuantizer q k M j : ℕ) : ℝ)) ≤ M+2*(L : ℝ)) ∧
    (∑ j, |(((effectiveCeilQuantizer q k M j : ℕ) : ℝ)/
        ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ))-h j/(∑ j, h j)|) ≤
      4*(L : ℝ)/M := by
  classical
  obtain ⟨hup, hdef⟩ := rat_lower_mass_bounds hor k
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hLpos : 0 < L := by
    cases L with
    | zero => rw [Fin.sum_univ_zero] at hlam; exact absurd hlam (by norm_num)
    | succ m => exact Nat.succ_pos m
  have hL1R : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
  have hqnn (j : Fin L) (k' : ℕ) : (0 : ℝ) ≤ ((q j k' : ℚ) : ℝ) := by
    exact_mod_cast (hor j k').1
  have hh (j : Fin L) : 0 ≤ h j := le_trans (hqnn j 0) (hor j 0).2.1
  have hhle (j : Fin L) : h j ≤ ∑ i, h i :=
    Finset.single_le_sum (fun i _ => hh i) (Finset.mem_univ j)
  have hcert' : (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k ≤ ratLowerMass q k := hcert
  have hdiff0 : (0 : ℝ) ≤ (∑ j, h j)-ratLowerMass q k := by linarith only [hup]

  have hR1 : (2*((M : ℝ)+1))*((∑ j, h j)-ratLowerMass q k) ≤ ratLowerMass q k := by
    calc (2*((M : ℝ)+1))*((∑ j, h j)-ratLowerMass q k)
        ≤ (2*((M : ℝ)+1))*((L : ℝ)*((2 : ℝ)⁻¹)^k) :=
          mul_le_mul_of_nonneg_left hdef (by linarith)
      _ = (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k := by ring
      _ ≤ ratLowerMass q k := hcert'
  have hlhpos : (0 : ℝ) < ratLowerMass q k := by
    rcases lt_trichotomy (ratLowerMass q k) (∑ j, h j) with hc | hc | hc
    · have h1 : (0 : ℝ) < (∑ j, h j)-ratLowerMass q k := by linarith only [hc]
      have h2 : (0 : ℝ) < (2*((M : ℝ)+1))*((∑ j, h j)-ratLowerMass q k) :=
        mul_pos (by linarith) h1
      exact h2.trans_le hR1
    · rw [hc]; exact hlam
    · exact hlam.trans hc
  have hE1 : 2*(M : ℝ)*((2 : ℝ)⁻¹)^k ≤ ∑ j, h j := by
    have hLnn : (0 : ℝ) ≤ L := by exact_mod_cast Nat.zero_le L
    have h1 : 2*(M : ℝ) ≤ 2*(L : ℝ)*((M : ℝ)+1) := by
      have hML : (M : ℝ)*((L : ℝ)-1) ≥ (0 : ℝ) :=
        mul_nonneg hMR.le (by linarith)
      nlinarith only [hML, hLnn]
    calc 2*(M : ℝ)*((2 : ℝ)⁻¹)^k ≤ (2*(L : ℝ)*((M : ℝ)+1))*((2 : ℝ)⁻¹)^k :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ratLowerMass q k := hcert'
      _ ≤ ∑ j, h j := hup

  have hynonneg (j : Fin L) : 0 ≤ (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k) :=
    div_nonneg (mul_nonneg hMR.le (hqnn j k)) hlhpos.le
  have hwdef (j : Fin L) : ((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
      = ((Nat.ceil ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)) : ℕ) : ℝ)+1 := by
    dsimp only [effectiveCeilQuantizer]
    push_cast
    rfl
  have hlo (j : Fin L) : (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1
      ≤ ((effectiveCeilQuantizer q k M j : ℕ) : ℝ) := by
    have h1 : (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)
        ≤ ((Nat.ceil ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    rw [hwdef j]
    linarith
  have hhi (j : Fin L) : ((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
      ≤ (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+2 := by
    have h1 : ((Nat.ceil ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)) : ℕ) : ℝ)
        < (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1 :=
      Nat.ceil_lt_add_one (hynonneg j)
    rw [hwdef j]
    linarith

  have hperLB (j : Fin L) :
      (M : ℝ)*(h j)/(∑ i, h i)+1/2 ≤ (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1 := by
    have hq0 : (0 : ℝ) ≤ ((q j k : ℝ)) := hqnn j k
    have herrj : h j-((q j k : ℝ)) ≤ ((2 : ℝ)⁻¹)^k := (hor j k).2.2
    have hsplit : (ratLowerMass q k)*(h j)-(∑ i, h i)*((q j k : ℝ))
        = (ratLowerMass q k)*((h j-(q j k : ℝ)))
          -((∑ i, h i)-ratLowerMass q k)*((q j k : ℝ)) := by ring
    have hle1 : (ratLowerMass q k)*(h j)-(∑ i, h i)*((q j k : ℝ))
        ≤ (ratLowerMass q k)*((2 : ℝ)⁻¹)^k := by
      rw [hsplit]
      have h1 : (ratLowerMass q k)*((h j-(q j k : ℝ)))
          ≤ (ratLowerMass q k)*((2 : ℝ)⁻¹)^k :=
        mul_le_mul_of_nonneg_left herrj hlhpos.le
      have h2 : (0 : ℝ) ≤ ((∑ i, h i)-ratLowerMass q k)*((q j k : ℝ)) :=
        mul_nonneg hdiff0 hq0
      linarith only [h1, h2]
    have hM1 : (M : ℝ)*(h j)*(ratLowerMass q k)-((M : ℝ)*((q j k : ℝ))*(∑ i, h i))
        ≤ (M : ℝ)*((ratLowerMass q k)*((2 : ℝ)⁻¹)^k) := by
      calc (M : ℝ)*(h j)*(ratLowerMass q k)-((M : ℝ)*((q j k : ℝ))*(∑ i, h i))
          = (M : ℝ)*((ratLowerMass q k)*(h j)-(∑ i, h i)*((q j k : ℝ))) := by ring
        _ ≤ (M : ℝ)*((ratLowerMass q k)*((2 : ℝ)⁻¹)^k) :=
            mul_le_mul_of_nonneg_left hle1 hMR.le
    have hM2 : ((2 : ℝ)*(M : ℝ)*((2 : ℝ)⁻¹)^k)*(ratLowerMass q k)
        ≤ (∑ i, h i)*(ratLowerMass q k) :=
      mul_le_mul_of_nonneg_right hE1 hlhpos.le
    have hdiff : (0 : ℝ) ≤ ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1)
        -((M : ℝ)*(h j)/(∑ i, h i)+1/2) := by
      have hident : ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1)
          -((M : ℝ)*(h j)/(∑ i, h i)+1/2)
          = (((∑ i, h i)*(ratLowerMass q k))
            -2*((M : ℝ)*(h j)*(ratLowerMass q k)
              -(M : ℝ)*((q j k : ℝ))*(∑ i, h i)))
            /(2*((∑ i, h i)*(ratLowerMass q k))) := by
        field_simp
        ring
      rw [hident]
      refine div_nonneg ?_ (mul_pos (by norm_num) (mul_pos hlam hlhpos)).le
      nlinarith only [hM1, hM2]
    linarith
  have hperUB (j : Fin L) :
      ((effectiveCeilQuantizer q k M j : ℕ) : ℝ) ≤ (M : ℝ)*(h j)/(∑ i, h i)+3 := by
    have hq0 : (0 : ℝ) ≤ ((q j k : ℝ)) := hqnn j k
    have hqhl : (M : ℝ)*((q j k : ℝ)) ≤ (M : ℝ)*(h j) :=
      mul_le_mul_of_nonneg_left (hor j k).2.1 hMR.le
    have hMlam : 2*((M : ℝ)*((∑ i, h i)-ratLowerMass q k)) ≤ ratLowerMass q k := by
      have h1 : ((∑ i, h i)-ratLowerMass q k)*(2*(M : ℝ))
          ≤ ((∑ i, h i)-ratLowerMass q k)*(2*((M : ℝ)+1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hdiff0
      have h2 := hR1
      linarith only [h1, h2]
    have hcross : (M : ℝ)*(h j)*((∑ i, h i))
        ≤ (M : ℝ)*(h j)*(ratLowerMass q k)+(∑ i, h i)*(ratLowerMass q k) := by
      have h1 : ((M : ℝ)*((∑ i, h i)-ratLowerMass q k))*(h j)
          ≤ (ratLowerMass q k)*((∑ i, h i)) := by
        have ha := mul_le_mul_of_nonneg_left hMlam (hh j)
        have hb := mul_le_mul_of_nonneg_right (hhle j) hlhpos.le
        have hnn : (0 : ℝ) ≤ (∑ i, h i)*(ratLowerMass q k) :=
          mul_nonneg hlam.le hlhpos.le
        nlinarith only [ha, hb, hnn]
      nlinarith only [h1]
    have hyUB : (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)
        ≤ (M : ℝ)*(h j)/((∑ i, h i))+1 := by
      have hident : ((M : ℝ)*(h j)/((∑ i, h i))+1)
          -((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k))
          = ((∑ i, h i)*(ratLowerMass q k)
            +(M : ℝ)*(h j)*(ratLowerMass q k)
            -(M : ℝ)*((q j k : ℝ))*((∑ i, h i)))
            /((∑ i, h i)*(ratLowerMass q k)) := by
        field_simp
        ring
      have hdiff : (0 : ℝ) ≤ ((M : ℝ)*(h j)/((∑ i, h i))+1)
          -((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)) := by
        rw [hident]
        refine div_nonneg ?_ (mul_pos hlam hlhpos).le
        have hqlam : (M : ℝ)*((q j k : ℝ))*((∑ i, h i))
            ≤ (M : ℝ)*(h j)*((∑ i, h i)) :=
          mul_le_mul_of_nonneg_right hqhl hlam.le
        nlinarith only [hcross, hqlam,
          mul_nonneg hMR.le (mul_nonneg hq0 hlhpos.le)]
      linarith
    linarith only [hhi j, hyUB]

  have hysum : (∑ j, (M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)) = (M : ℝ) := by
    have hs := (Finset.sum_div Finset.univ
      (fun j => (M : ℝ)*((q j k : ℝ))) (ratLowerMass q k)).symm
    have hq : (∑ j, ((q j k : ℝ))) = ratLowerMass q k := rfl
    rw [hs, ← Finset.mul_sum, hq, mul_div_assoc, div_self hlhpos.ne', mul_one]
  have hpxsum : (∑ j, (h j)/(∑ i, h i)) = 1 := by
    have hs := (Finset.sum_div Finset.univ (fun j => h j) (∑ i, h i)).symm
    rw [hs, div_self hlam.ne']
  have hsumc (c : ℝ) : (∑ j : Fin L, c) = (L : ℝ)*c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hWsum : ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)
      = ∑ j, ((effectiveCeilQuantizer q k M j : ℕ) : ℝ) := by
    simp only [weightTotal, Nat.cast_sum]
  have hsumlo : (∑ j, ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+1))
      = (M : ℝ)+(L : ℝ) := by
    have hs := (Finset.sum_div Finset.univ
      (fun j => (M : ℝ)*((q j k : ℝ))) (ratLowerMass q k)).symm
    have hq : (∑ j, ((q j k : ℝ))) = ratLowerMass q k := rfl
    rw [Finset.sum_add_distrib, hs, ← Finset.mul_sum, hq, mul_div_assoc,
      div_self hlhpos.ne', mul_one, hsumc, mul_one]
  have hsumhi : (∑ j, ((M : ℝ)*((q j k : ℝ))/(ratLowerMass q k)+2))
      = (M : ℝ)+2*(L : ℝ) := by
    have hs := (Finset.sum_div Finset.univ
      (fun j => (M : ℝ)*((q j k : ℝ))) (ratLowerMass q k)).symm
    have hq : (∑ j, ((q j k : ℝ))) = ratLowerMass q k := rfl
    rw [Finset.sum_add_distrib, hs, ← Finset.mul_sum, hq, mul_div_assoc,
      div_self hlhpos.ne', mul_one, hsumc]
    ring

  have hmasslo : (M : ℝ)+(L : ℝ)
      ≤ ∑ j, ((effectiveCeilQuantizer q k M j : ℕ) : ℝ) := by
    rw [← hsumlo]
    exact Finset.sum_le_sum (fun j _ => hlo j)
  have hmasshi : ∑ j, ((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
      ≤ M+2*(L : ℝ) := by
    rw [← hsumhi]
    exact Finset.sum_le_sum (fun j _ => hhi j)
  have hWM : ((M : ℕ) : ℝ)
      ≤ ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) := by
    rw [hWsum]
    linarith

  have hWR : (0 : ℝ) < ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) :=
    lt_of_lt_of_le hMR hWM
  have hWupper : ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)
      ≤ M+2*(L : ℝ) := by
    rw [hWsum]
    exact hmasshi
  have hdnonneg (j : Fin L) : 0 ≤ ((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
      -(M : ℝ)*(h j)/(∑ i, h i) := by
    have h1 := hperLB j
    have h2 := hlo j
    linarith
  have hdsum : (∑ j, (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
      -(M : ℝ)*(h j)/(∑ i, h i)))
      = ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ) := by
    have hsplit : (∑ j, (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)
        -(M : ℝ)*(h j)/(∑ i, h i)))
        = (∑ j, ((effectiveCeilQuantizer q k M j : ℕ) : ℝ))
          -(M : ℝ)*(∑ j, ((h j)/(∑ i, h i))) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => mul_div_assoc _ _ _)
    rw [hsplit, hpxsum, mul_one, hWsum]
  have hpoint (j : Fin L) : |(((effectiveCeilQuantizer q k M j : ℕ) : ℝ)/
      ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ))-(h j)/(∑ i, h i)| ≤
      (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)
        +(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
        *((h j)/(∑ i, h i)))/
      ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) := by
    have he : (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)/
        ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ))-(h j)/(∑ i, h i)
        = (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)
          -(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
          *((h j)/(∑ i, h i)))/
          ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) := by
      field_simp
      ring
    rw [he, abs_div, abs_of_pos hWR]
    apply div_le_div_of_nonneg_right _ hWR.le
    have hΔ : 0 ≤ ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ) := by
      rw [hWsum]
      linarith
    calc |(((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)
        -(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
        *((h j)/(∑ i, h i)))|
        ≤ |((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)|
          +|(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
            *((h j)/(∑ i, h i))| := by
          simpa only [Real.norm_eq_abs] using norm_sub_le
            (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i))
            ((((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
              *((h j)/(∑ i, h i)))
      _ = (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)
        +(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
        *((h j)/(∑ i, h i))) := by
          rw [abs_of_nonneg (hdnonneg j),
            abs_of_nonneg (mul_nonneg hΔ (div_nonneg (hh j) hlam.le))]
  refine ⟨⟨Nat.cast_le.mp hWM, hmasshi⟩, ?_⟩
  calc (∑ j, |(((effectiveCeilQuantizer q k M j : ℕ) : ℝ)/
        ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ))-(h j)/(∑ i, h i)|)
      ≤ (∑ j, (((effectiveCeilQuantizer q k M j : ℕ) : ℝ)-(M : ℝ)*(h j)/(∑ i, h i)
          +(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))
          *((h j)/(∑ i, h i)))/
          ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun j _ => hpoint j)
    _ = 2*(((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ)-(M : ℝ))/
        ((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
          hpxsum, hdsum]
        ring
    _ ≤ 4*(L : ℝ)/((weightTotal (effectiveCeilQuantizer q k M) : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hWR.le
        nlinarith only [hWupper]
    _ ≤ 4*(L : ℝ)/M :=
        div_le_div_of_nonneg_left (by positivity) hMR hWM

/-- The least certified precision exists under positive mass and scale and satisfies the stated
precision, integer mass, and normalized law approximation bounds. -/
theorem effectiveCeilQuantizerLaw : EffectiveCeilQuantizerLaw := by
  intro L M h q hor hlam hM
  (try dsimp only)
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt
    ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)) (by norm_num : (1 : ℝ) < 2)
  have hk₀' : (L : ℝ)*(2*(M : ℝ)+3) ≤ (∑ j, h j)*((2 : ℝ)^k₀) := by
    have h := (div_le_iff₀ hlam).mp (le_of_lt hk₀)
    linarith
  have hcertk₀ : ceilQuantizerCert M q k₀ := ceilQuantizerCert_of_pow_bound hor hk₀'
  have hpeq : effectiveQuantizerPrecision M q
      = sInf {k : ℕ | ceilQuantizerCert M q k} := rfl
  have hcert : ceilQuantizerCert M q (effectiveQuantizerPrecision M q) := by
    rw [hpeq]
    exact Nat.sInf_mem (⟨k₀, hcertk₀⟩ : {k : ℕ | ceilQuantizerCert M q k}.Nonempty)
  have hkb : effectiveQuantizerPrecision M q
      ≤ Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j))) := by
    have h1 : (L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)
        ≤ ((Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_ceil _
    have h2 : ((Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)) : ℕ) : ℝ)
        ≤ ((2 : ℝ)^(Nat.clog 2
            (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j))))) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) _
    have hcertkb : ceilQuantizerCert M q
        (Nat.clog 2 (Nat.ceil ((L : ℝ)*(2*(M : ℝ)+3)/(∑ j, h j)))) := by
      refine ceilQuantizerCert_of_pow_bound hor ?_
      have h := (div_le_iff₀ hlam).mp (h1.trans h2)
      linarith
    rw [hpeq]
    exact Nat.sInf_le hcertkb
  exact ⟨hcert, hkb, effectiveCeilQuantizer_mass_and_l1 hor hlam hM hcert⟩

end Qatlib.Concepts.DiamondQdrift.QuantizerCert
