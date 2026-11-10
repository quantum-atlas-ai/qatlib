/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem

open scoped BigOperators
open Finset

theorem subsystem_singleton_circuit_bound
    (Nst k r dst : ℕ) (cloc Cst : ℝ)
    (_hk : 1 ≤ k) (_hdst : 1 ≤ dst) (hcloc : 0 < cloc)
    (hAss : (Nst : ℝ) ≤ cloc * Cst)
    (hSingleton : (Nst : ℝ) ≥ (k : ℝ) + (r : ℝ) + 2 * ((dst : ℝ) - 1)) :
    (Nst : ℝ) ≥ (k : ℝ) + (r : ℝ) + 2 * ((dst : ℝ) - 1) ∧
      Cst ≥ ((k : ℝ) + (r : ℝ) + 2 * ((dst : ℝ) - 1)) / cloc := by
  refine ⟨hSingleton, ?_⟩

  rw [ge_iff_le, div_le_iff₀ hcloc]
  linarith

theorem cost_of_correcting_small_pauli_fault
    (k r t Nst dst : ℕ) (cloc Cst : ℝ)
    (hcloc : 0 < cloc) (hdst : 2 * t + 1 ≤ dst)
    (hH5 : (Nst : ℝ) ≥ (k : ℝ) + (r : ℝ) + 2 * ((dst : ℝ) - 1))
    (hAss24 : (Nst : ℝ) ≤ cloc * Cst) :
    (2 * t + 1 ≤ dst) ∧
      Cst ≥ ((k : ℝ) + (r : ℝ) + 4 * (t : ℝ)) / cloc := by
  refine ⟨hdst, ?_⟩
  rw [ge_iff_le, div_le_iff₀ hcloc]
  have hd : (dst : ℝ) ≥ 2 * (t : ℝ) + 1 := by exact_mod_cast hdst
  nlinarith [hH5, hAss24]

theorem min_mass_ge {x y r : ℝ} (_hx : 0 < x) (_hy : 0 < y) (hr : 0 < r) (_hr1 : r ≤ 1)
    (hxy : x ≤ y / r) (hyx : y ≤ x / r) :
    r / (1 + r) * (x + y) ≤ min x y := by
  have hrpos : 0 < 1 + r := by linarith
  rcases le_or_gt x y with h | h
  · rw [min_eq_left h]
    have hsum : x + y ≤ x + x / r := by linarith [hyx]
    have hmul : r / (1 + r) * (x + y) ≤ r / (1 + r) * (x + x / r) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hr.le (by linarith))
    have hsimpl : r / (1 + r) * (x + x / r) = x := by
      rw [div_mul_eq_mul_div, mul_add, mul_comm r (x / r), div_mul_cancel₀ x (ne_of_gt hr),
        div_eq_iff (ne_of_gt hrpos)]
      ring
    exact hmul.trans_eq hsimpl
  · rw [min_eq_right (le_of_lt h)]
    have hsum : x + y ≤ y / r + y := by linarith [hxy]
    have hmul : r / (1 + r) * (x + y) ≤ r / (1 + r) * (y / r + y) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hr.le (by linarith))
    have hsimpl : r / (1 + r) * (y / r + y) = y := by
      rw [div_mul_eq_mul_div, mul_add, mul_comm r (y / r), div_mul_cancel₀ y (ne_of_gt hr),
        div_eq_iff (ne_of_gt hrpos)]
      ring
    exact hmul.trans_eq hsimpl

theorem pauli_pairing_bound
    (_Nst k _r dst : ℕ) (qmin qmax : ℝ)
    (_hk : 1 ≤ k) (hqmin : 0 < qmin) (hqmax : 0 < qmax) (hqmin_le : qmin ≤ qmax)
    {G : Type*} [Fintype G] [DecidableEq G] (mulByL : G → G)
    (hinvol : ∀ F, mulByL (mulByL F) = F)
    (ν : G → ℝ) (hν_pos : ∀ F, 0 < ν F) (hν_sum : ∑ F, ν F = 1)
    (fails : G → Prop) [DecidablePred fails]
    (hfail : ∀ F, fails F ∨ fails (mulByL F))
    (hratio_lo : ∀ F, (qmin / qmax) ^ (dst : ℝ) ≤ ν (mulByL F) / ν F)
    (hratio_hi : ∀ F, ν (mulByL F) / ν F ≤ (qmin / qmax) ^ (-(dst : ℝ))) :
    (∑ F ∈ Finset.univ.filter fails, ν F)
      ≥ (1 / 2) * (∑ F, min (ν F) (ν (mulByL F))) ∧
      ∃ ρ : ℝ, ρ = qmin / qmax ∧ 0 < ρ ∧ ρ ≤ 1 ∧
        (∑ F ∈ Finset.univ.filter fails, ν F) ≥ ρ ^ (dst : ℝ) / (1 + ρ ^ (dst : ℝ)) := by
  classical

  have hreidx : ∀ g : G → ℝ, (∑ F, g (mulByL F)) = ∑ F, g F := by
    intro g
    exact Fintype.sum_equiv
      { toFun := mulByL, invFun := mulByL, left_inv := hinvol, right_inv := hinvol }
      (fun F => g (mulByL F)) g (fun _ => rfl)

  have hpoint : ∀ F : G,
      (if fails F then ν F else 0) + (if fails (mulByL F) then ν (mulByL F) else 0)
        ≥ min (ν F) (ν (mulByL F)) := by
    intro F
    rcases hfail F with hf | hf
    · by_cases hL : fails (mulByL F)
      · simp only [if_pos hf, if_pos hL]
        linarith [min_le_left (ν F) (ν (mulByL F)), (hν_pos (mulByL F)).le]
      · simp only [if_pos hf, if_neg hL, add_zero]
        linarith [min_le_left (ν F) (ν (mulByL F))]
    · by_cases hF : fails F
      · simp only [if_pos hF, if_pos hf]
        linarith [min_le_right (ν F) (ν (mulByL F)), (hν_pos F).le]
      · simp only [if_neg hF, if_pos hf, zero_add]
        linarith [min_le_right (ν F) (ν (mulByL F))]

  have hsumpair : (∑ F : G, ((if fails F then ν F else 0)
        + (if fails (mulByL F) then ν (mulByL F) else 0)))
      = 2 * (∑ F ∈ Finset.univ.filter fails, ν F) := by
    have h1 : (∑ F : G, (if fails F then ν F else 0))
        = ∑ F ∈ Finset.univ.filter fails, ν F :=
      (Finset.sum_filter fails ν).symm
    have h2 : (∑ F : G, (if fails (mulByL F) then ν (mulByL F) else 0))
        = ∑ F ∈ Finset.univ.filter fails, ν F :=
      (hreidx (fun F => if fails F then ν F else 0)).trans h1
    have hsplit : (∑ F : G, ((if fails F then ν F else 0)
          + (if fails (mulByL F) then ν (mulByL F) else 0)))
        = (∑ F : G, (if fails F then ν F else 0))
          + (∑ F : G, (if fails (mulByL F) then ν (mulByL F) else 0)) :=
      Finset.sum_add_distrib
        (f := fun F => if fails F then ν F else 0)
        (g := fun F => if fails (mulByL F) then ν (mulByL F) else 0)
    rw [hsplit, h1, h2]
    ring
  have hsummin : (∑ F, min (ν F) (ν (mulByL F)))
      ≤ (∑ F : G, ((if fails F then ν F else 0)
          + (if fails (mulByL F) then ν (mulByL F) else 0))) :=
    Finset.sum_le_sum (fun F _ => hpoint F)

  have hρpos : 0 < qmin / qmax := div_pos hqmin hqmax
  have hρle : qmin / qmax ≤ 1 := (div_le_one hqmax).2 hqmin_le
  have hrpow : 0 < (qmin / qmax) ^ (dst : ℝ) := Real.rpow_pos_of_pos hρpos _
  have hrpow_le1 : (qmin / qmax) ^ (dst : ℝ) ≤ 1 :=
    Real.rpow_le_one hρpos.le hρle (Nat.cast_nonneg _)
  have hinv : (qmin / qmax) ^ (dst : ℝ) * (qmin / qmax) ^ (-(dst : ℝ)) = 1 := by
    rw [← Real.rpow_add hρpos, add_neg_cancel, Real.rpow_zero]
  have hsumσ : (∑ F, ν (mulByL F)) = 1 := by rw [hreidx ν, hν_sum]
  have hbudget : ∀ F : G, (qmin / qmax) ^ (dst : ℝ) / (1 + (qmin / qmax) ^ (dst : ℝ))
        * (ν F + ν (mulByL F)) ≤ min (ν F) (ν (mulByL F)) := by
    intro F
    refine min_mass_ge (hν_pos F) (hν_pos _) hrpow hrpow_le1 ?_ ?_
    · refine (le_div_iff₀ hrpow).mpr ?_
      have hlo : (qmin / qmax) ^ (dst : ℝ) * ν F ≤ ν (mulByL F) :=
        (le_div_iff₀ (hν_pos F)).mp (hratio_lo F)
      rw [mul_comm]
      exact hlo
    · refine (le_div_iff₀ hrpow).mpr ?_
      have hhi : ν (mulByL F) ≤ (qmin / qmax) ^ (-(dst : ℝ)) * ν F :=
        (div_le_iff₀ (hν_pos F)).mp (hratio_hi F)
      have hcomm : (qmin / qmax) ^ (-(dst : ℝ)) * ((qmin / qmax) ^ (dst : ℝ)) = 1 := by
        rw [mul_comm]
        exact hinv
      calc ν (mulByL F) * (qmin / qmax) ^ (dst : ℝ)
          ≤ ((qmin / qmax) ^ (-(dst : ℝ)) * ν F) * (qmin / qmax) ^ (dst : ℝ) :=
            mul_le_mul_of_nonneg_right hhi hrpow.le
        _ = ν F := by
          rw [mul_assoc, mul_comm (ν F) ((qmin / qmax) ^ (dst : ℝ)),
            ← mul_assoc, hcomm, one_mul]
  have hminsum : ((qmin / qmax) ^ (dst : ℝ) / (1 + (qmin / qmax) ^ (dst : ℝ))) * 2
      ≤ (∑ F, min (ν F) (ν (mulByL F))) := by
    have h1 : (∑ F : G, ((qmin / qmax) ^ (dst : ℝ) / (1 + (qmin / qmax) ^ (dst : ℝ)))
          * (ν F + ν (mulByL F)))
        ≤ (∑ F, min (ν F) (ν (mulByL F))) :=
      Finset.sum_le_sum (fun F _ => hbudget F)
    have h2 : (∑ F : G, ((qmin / qmax) ^ (dst : ℝ) / (1 + (qmin / qmax) ^ (dst : ℝ)))
          * (ν F + ν (mulByL F)))
        = ((qmin / qmax) ^ (dst : ℝ) / (1 + (qmin / qmax) ^ (dst : ℝ))) * 2 := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, hν_sum, hsumσ]
      ring
    rwa [h2] at h1
  refine ⟨?_, qmin / qmax, rfl, hρpos, hρle, ?_⟩
  · linarith [hsummin, hsumpair]
  · linarith [hsummin, hsumpair, hminsum]

theorem accuracy_forces_distance
    (dst Nst k r : ℕ) (qmin qmax ρ PL ε cloc Cst : ℝ)
    (hdst : 1 ≤ dst) (hcloc : 0 < cloc)
    (hqmin : 0 < qmin) (hqmax : 0 < qmax) (hqlt : qmin < qmax)
    (hρ : ρ = qmin / qmax) (hρpos : 0 < ρ) (_hρlt : ρ < 1)
    (hεpos : 0 < ε) (hε : ε < 1 / 2)
    (hH20 : ρ ^ (dst : ℝ) / (1 + ρ ^ (dst : ℝ)) ≤ PL)
    (hPL : PL ≤ ε)
    (hH5 : (Nst : ℝ) ≥ (k : ℝ) + (r : ℝ) + 2 * ((dst : ℝ) - 1))
    (hAss24 : (Nst : ℝ) ≤ cloc * Cst) :
    (dst : ℝ) ≥ Real.log ((1 - ε) / ε) / Real.log (qmax / qmin) ∧
      (Nst : ℝ) ≥ max ((k : ℝ) + (r : ℝ))
        ((k : ℝ) + (r : ℝ) - 2 + 2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin))) ∧
      Cst ≥ (1 / cloc) * max ((k : ℝ) + (r : ℝ))
        ((k : ℝ) + (r : ℝ) - 2 + 2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin))) := by

  have h1mε : 0 < 1 - ε := by linarith
  have hden : 0 < 1 + ρ ^ (dst : ℝ) := by positivity
  have hle1 : ρ ^ (dst : ℝ) / (1 + ρ ^ (dst : ℝ)) ≤ ε := le_trans hH20 hPL
  have hle2 : ρ ^ (dst : ℝ) ≤ ε / (1 - ε) := by
    rw [div_le_iff₀ hden] at hle1
    rw [le_div_iff₀ h1mε]
    nlinarith [hle1]

  have hεratio : 0 < (1 - ε) / ε := by positivity
  have hlog1 : (dst : ℝ) * Real.log ρ ≤ -Real.log ((1 - ε) / ε) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hρpos _) hle2
    rw [Real.log_rpow hρpos] at h
    have hlogratio : Real.log (ε / (1 - ε)) = -Real.log ((1 - ε) / ε) := by
      rw [Real.log_div (ne_of_gt hεpos) (ne_of_gt h1mε),
          Real.log_div (ne_of_gt h1mε) (ne_of_gt hεpos)]
      ring
    rwa [hlogratio] at h
  have hlogq : Real.log (qmax / qmin) = -Real.log ρ := by
    rw [hρ, Real.log_div (ne_of_gt hqmax) (ne_of_gt hqmin),
        Real.log_div (ne_of_gt hqmin) (ne_of_gt hqmax)]
    ring
  have hMpos : 0 < Real.log ((1 - ε) / ε) := by
    apply Real.log_pos
    rw [one_lt_div hεpos]
    linarith
  have hLpos : 0 < Real.log (qmax / qmin) := by
    apply Real.log_pos
    rw [one_lt_div hqmin]
    exact hqlt
  have hdst_bound : (dst : ℝ) ≥ Real.log ((1 - ε) / ε) / Real.log (qmax / qmin) := by
    rw [ge_iff_le, div_le_iff₀ hLpos]
    have : (dst : ℝ) * Real.log (qmax / qmin) ≥ Real.log ((1 - ε) / ε) := by
      rw [hlogq]
      linarith [hlog1]
    linarith [mul_comm (dst : ℝ) (Real.log (qmax / qmin))]
  have hd1 : (1 : ℝ) ≤ dst := by exact_mod_cast hdst
  refine ⟨hdst_bound, ?_, ?_⟩

  have hbase : ((k : ℝ) + (r : ℝ)) ≤ (Nst : ℝ) := by
    nlinarith [hH5, hd1]
  have hwith : ((k : ℝ) + (r : ℝ) - 2 +
      2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin))) ≤ (Nst : ℝ) := by
    nlinarith [hH5, hdst_bound]
  exact max_le hbase hwith

  have hNmax : max ((k : ℝ) + (r : ℝ))
      ((k : ℝ) + (r : ℝ) - 2 + 2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin)))
      ≤ (Nst : ℝ) := by
    apply max_le
    · nlinarith [hH5, hd1]
    · nlinarith [hH5, hdst_bound]
  rw [ge_iff_le]
  have hdiv : (1 / cloc) * max ((k : ℝ) + (r : ℝ))
      ((k : ℝ) + (r : ℝ) - 2 + 2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin)))
      = max ((k : ℝ) + (r : ℝ))
      ((k : ℝ) + (r : ℝ) - 2 + 2 * (Real.log ((1 - ε) / ε) / Real.log (qmax / qmin))) / cloc := by
    ring
  rw [hdiv, div_le_iff₀ hcloc]
  nlinarith [hNmax, hAss24]

theorem vanishing_error_grows_protection
    (Nst k r dst : ℕ → ℕ) (ρL PL : ℕ → ℝ) (ρ0 : ℝ)
    (hρ0 : 0 < ρ0) (hρ0le : ρ0 ≤ 1)
    (hρ : ∀ lam, ρ0 ≤ ρL lam) (_hρle : ∀ lam, ρL lam ≤ 1)
    (hPL : Filter.Tendsto PL Filter.atTop (nhds 0))
    (_hdst1 : ∀ lam, 1 ≤ dst lam)
    (hH5 : ∀ lam, k lam + r lam + 2 * (dst lam - 1) ≤ Nst lam)
    (hH20 : ∀ lam, ρL lam ^ (dst lam : ℝ) / (1 + ρL lam ^ (dst lam : ℝ)) ≤ PL lam) :
    Filter.Tendsto dst Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun lam => Nst lam - k lam - r lam) Filter.atTop Filter.atTop := by

  have part1 : Filter.Tendsto dst Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro C
    by_contra hC
    push Not at hC

    have hc : 0 < ρ0 ^ (C : ℝ) / (1 + ρ0 ^ (C : ℝ)) :=
      div_pos (Real.rpow_pos_of_pos hρ0 _) (add_pos zero_lt_one (Real.rpow_pos_of_pos hρ0 _))

    have hmono : ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → t₁ / (1 + t₁) ≤ t₂ / (1 + t₂) := by
      intro t₁ t₂ ht₁ hle
      have h2 : (0 : ℝ) < 1 + t₂ := by linarith [ht₁.le.trans hle]
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + t₁) h2]
      nlinarith [hle, ht₁.le]

    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hPL
      (ρ0 ^ (C : ℝ) / (1 + ρ0 ^ (C : ℝ)) / 2) (div_pos hc (by norm_num))

    obtain ⟨lam, hlamN, hlamD⟩ := hC N₁
    have hsmall := hN₁ lam hlamN
    rw [Real.dist_eq, sub_zero, abs_lt] at hsmall

    have hposL : 0 < ρL lam := lt_of_lt_of_le hρ0 (hρ lam)
    have hpow : ρ0 ^ (C : ℝ) ≤ ρL lam ^ ((dst lam : ℕ) : ℝ) := by
      by_cases hlt : ρL lam < 1
      · have h1 : ρ0 ^ (C : ℝ) ≤ ρL lam ^ (C : ℝ) :=
          Real.rpow_le_rpow hρ0.le (hρ lam) (Nat.cast_nonneg _)
        have hle : ((dst lam : ℕ) : ℝ) ≤ (C : ℝ) := by exact_mod_cast hlamD.le
        have h2 : ρL lam ^ (C : ℝ) ≤ ρL lam ^ ((dst lam : ℕ) : ℝ) :=
          (Real.rpow_le_rpow_left_iff_of_base_lt_one hposL hlt).2 hle
        exact h1.trans h2
      · have h1 : 1 ≤ ρL lam := not_lt.mp hlt
        have hA : ρ0 ^ (C : ℝ) ≤ 1 := by
          have h : ρ0 ^ (C : ℝ) ≤ 1 ^ (C : ℝ) :=
            Real.rpow_le_rpow hρ0.le hρ0le (Nat.cast_nonneg _)
          rwa [Real.one_rpow] at h
        have hB : (1 : ℝ) ≤ ρL lam ^ ((dst lam : ℕ) : ℝ) :=
          Real.one_le_rpow h1 (Nat.cast_nonneg _)
        exact hA.trans hB

    have hchain : ρ0 ^ (C : ℝ) / (1 + ρ0 ^ (C : ℝ)) ≤ PL lam :=
      (hmono _ _ (Real.rpow_pos_of_pos hρ0 _) hpow).trans (hH20 lam)
    linarith [hchain, hsmall.1]
  constructor
  · exact part1
  · rw [Filter.tendsto_atTop_atTop]
    intro C
    obtain ⟨i, hi⟩ := (Filter.tendsto_atTop_atTop.mp part1) (C + 1)
    refine ⟨i, fun lam hlam => ?_⟩
    have h5 := hH5 lam
    have hc1 : (C + 1 : ℕ) ≤ dst lam := hi lam hlam
    omega

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem
