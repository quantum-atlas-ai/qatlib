/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.DiracSearch04.MainResults

open Finset
open scoped BigOperators

def NSites (d L : ℕ) : ℕ := L ^ d

noncomputable def kVec (d L : ℕ) (m : Fin d → Fin L) : Fin d → ℝ :=
  fun i => 2 * Real.pi * (m i : ℝ) / (L : ℝ)

noncomputable def sSq (d : ℕ) (k : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (Real.sin (k i)) ^ 2

noncomputable def cOf (d : ℕ) (k : Fin d → ℝ) : ℝ :=
  2 * ∑ i : Fin d, (1 - Real.cos (k i))

noncomputable def energyMag (d : ℕ) (ω γ : ℝ) (k : Fin d → ℝ) : ℝ :=
  Real.sqrt (ω ^ 2 * sSq d k + γ ^ 2 * (cOf d k) ^ 2)

noncomputable def nonzeroMomentum (d L : ℕ) : Finset (Fin d → Fin L) :=
  Finset.univ.filter (fun m => ∃ i : Fin d, (m i).val ≠ 0)

noncomputable def V0 (d L : ℕ) (ω γ : ℝ) : ℝ :=
  (1 / (NSites d L : ℝ)) *
    (nonzeroMomentum d L).sum (fun m => 1 / (energyMag d ω γ (kVec d L m)) ^ 2)

noncomputable def U0 (d L : ℕ) (ω γ : ℝ) : ℝ :=
  (1 / (NSites d L : ℝ)) *
    (nonzeroMomentum d L).sum
      (fun m => (γ * cOf d (kVec d L m)) / (energyMag d ω γ (kVec d L m)) ^ 2)

noncomputable def EpmMag (d L : ℕ) (ω γ : ℝ) : ℝ :=
  1 / Real.sqrt (V0 d L ω γ * (NSites d L : ℝ))

noncomputable def searchTime (d L : ℕ) (ω γ : ℝ) : ℝ :=
  Real.pi / 2 * Real.sqrt (V0 d L ω γ * (NSites d L : ℝ))

noncomputable def successProb (d L : ℕ) (ω γ : ℝ) : ℝ :=
  1 / V0 d L ω γ

theorem exp_neg_I_pi_div_two :
    Complex.exp (-(Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) = -Complex.I := by
  rw [show -(Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      (((-(Real.pi / 2)) : ℝ) : ℂ) * Complex.I by
    push_cast; ring_nf]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem exp_I_pi_div_two :
    Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem phase_half_turn_pos (E : ℝ) (hE : 0 < E) :
    Complex.exp (-(Complex.I * (E : ℂ) * ((Real.pi / (2 * E) : ℝ) : ℂ))) =
      -Complex.I := by
  have hE' : (E : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hE
  have harg : (E : ℂ) * ((Real.pi / (2 * E) : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [mul_assoc, harg, exp_neg_I_pi_div_two]

theorem phase_half_turn_neg (E : ℝ) (hE : 0 < E) :
    Complex.exp (Complex.I * (E : ℂ) * ((Real.pi / (2 * E) : ℝ) : ℂ)) =
      Complex.I := by
  have hE' : (E : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hE
  have harg : (E : ℂ) * ((Real.pi / (2 * E) : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [mul_assoc, harg, exp_I_pi_div_two]

theorem searchTime_eq_inverse_energy (d L : ℕ) (ω γ : ℝ)
    (hV : 0 < V0 d L ω γ) (hN : 0 < (NSites d L : ℝ)) :
    searchTime d L ω γ = Real.pi / (2 * EpmMag d L ω γ) := by
  have hVN : 0 < V0 d L ω γ * (NSites d L : ℝ) := mul_pos hV hN
  have hs : 0 < Real.sqrt (V0 d L ω γ * (NSites d L : ℝ)) := Real.sqrt_pos.mpr hVN
  have hsne : Real.sqrt (V0 d L ω γ * (NSites d L : ℝ)) ≠ 0 := ne_of_gt hs
  rw [searchTime, EpmMag]
  field_simp

theorem speedup_from_bounded_V0
    (d L : ℕ) (ω γ : ℝ)
    (hV : 0 < V0 d L ω γ) (hN : 0 < (NSites d L : ℝ))
    {K : ℝ} (hK : 0 < K) (hVle : V0 d L ω γ ≤ K) :
    searchTime d L ω γ ≤ (Real.pi / 2 * Real.sqrt K) * Real.sqrt (NSites d L : ℝ) ∧
      1 / K ≤ successProb d L ω γ := by
  constructor
  · rw [searchTime]
    have h1 : V0 d L ω γ * (NSites d L : ℝ) ≤ K * (NSites d L : ℝ) :=
      mul_le_mul_of_nonneg_right hVle (le_of_lt hN)
    have h2 : Real.sqrt (V0 d L ω γ * (NSites d L : ℝ)) ≤
        Real.sqrt (K * (NSites d L : ℝ)) := Real.sqrt_le_sqrt h1
    have hmul : Real.sqrt (K * (NSites d L : ℝ)) =
        Real.sqrt K * Real.sqrt (NSites d L : ℝ) := Real.sqrt_mul (le_of_lt hK) _
    have hpi2 : 0 ≤ Real.pi / 2 := by positivity
    calc Real.pi / 2 * Real.sqrt (V0 d L ω γ * (NSites d L : ℝ))
        ≤ Real.pi / 2 * Real.sqrt (K * (NSites d L : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hpi2
      _ = Real.pi / 2 * (Real.sqrt K * Real.sqrt (NSites d L : ℝ)) := by rw [hmul]
      _ = (Real.pi / 2 * Real.sqrt K) * Real.sqrt (NSites d L : ℝ) := by ring
  · rw [successProb]
    exact one_div_le_one_div_of_le hV hVle

theorem V0_pos (d L : ℕ) (ω γ : ℝ) (hω : 0 < ω) (hγ : 0 < γ)
    (hL : 2 ≤ L) (hd : 0 < d) :
    0 < V0 d L ω γ := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (by omega : 0 < L)
  have hNpos : (0 : ℝ) < (NSites d L : ℝ) := by
    unfold NSites
    push_cast
    exact pow_pos hLpos d

  let m₀ : Fin d → Fin L := fun _ => ⟨1, by omega⟩
  have hm₀ : m₀ ∈ nonzeroMomentum d L := by
    unfold nonzeroMomentum
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨⟨0, hd⟩, by simp [m₀]⟩⟩
  have hk : ∀ i : Fin d, kVec d L m₀ i = 2 * Real.pi / (L : ℝ) := by
    intro i
    unfold kVec
    simp [m₀]
  have hθpos : 0 < 2 * Real.pi / (L : ℝ) := by positivity
  have hθlt : 2 * Real.pi / (L : ℝ) < 2 * Real.pi := by
    rw [div_lt_iff₀ hLpos]
    have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    nlinarith [Real.pi_pos, mul_nonneg (le_of_lt Real.pi_pos) (by linarith : (0:ℝ) ≤ (L:ℝ) - 2)]
  have hcos : Real.cos (2 * Real.pi / (L : ℝ)) < 1 := by
    refine lt_of_le_of_ne (Real.cos_le_one _) ?_
    intro h
    have h0 := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hθlt).mp h
    linarith
  have hcpos : 0 < cOf d (kVec d L m₀) := by
    unfold cOf
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 < 1 - Real.cos (kVec d L m₀ i) := by
      intro i _
      rw [hk i]
      exact sub_pos.mpr hcos
    have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
    exact mul_pos (by norm_num) (Finset.sum_pos hterm hne)
  have hEpos : 0 < energyMag d ω γ (kVec d L m₀) := by
    unfold energyMag
    apply Real.sqrt_pos.mpr
    have hsSq : 0 ≤ sSq d (kVec d L m₀) := by
      unfold sSq
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h1 : 0 ≤ ω ^ 2 * sSq d (kVec d L m₀) :=
      mul_nonneg (le_of_lt (pow_pos hω 2)) hsSq
    have h2 : 0 < γ ^ 2 * (cOf d (kVec d L m₀)) ^ 2 :=
      mul_pos (pow_pos hγ 2) (pow_pos hcpos 2)
    linarith
  have htermpos : 0 < 1 / (energyMag d ω γ (kVec d L m₀)) ^ 2 :=
    one_div_pos.mpr (pow_pos hEpos 2)
  have hsumpos : 0 < (nonzeroMomentum d L).sum
      (fun m => 1 / (energyMag d ω γ (kVec d L m)) ^ 2) := by
    refine Finset.sum_pos' (fun m _ => ?_) ⟨m₀, hm₀, htermpos⟩
    exact div_nonneg zero_le_one (sq_nonneg _)
  unfold V0
  exact mul_pos (div_pos one_pos hNpos) hsumpos

theorem dirac_search_d_gt_2 (d : ℕ) (hd : 3 ≤ d) (ω γ : ℝ)
    (hω : 0 < ω) (hγ : 0 < γ)
    (hK : ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, 1 ≤ L → V0 d L ω γ ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ L : ℕ, 2 ≤ L →
        searchTime d L ω γ ≤ C * Real.sqrt (NSites d L : ℝ) ∧
        c ≤ successProb d L ω γ := by
  obtain ⟨K, hKpos, hKb⟩ := hK
  refine ⟨Real.pi / 2 * Real.sqrt K, ?_, 1 / K, ?_, ?_⟩
  · exact mul_pos (by positivity) (Real.sqrt_pos.mpr hKpos)
  · exact one_div_pos.mpr hKpos
  · intro L hL
    have hVpos : 0 < V0 d L ω γ := V0_pos d L ω γ hω hγ hL (by omega)
    have hNpos : (0 : ℝ) < (NSites d L : ℝ) := by
      have hLpos : 0 < L := by omega
      unfold NSites
      push_cast
      exact pow_pos (by exact_mod_cast hLpos : (0:ℝ) < (L:ℝ)) d
    exact speedup_from_bounded_V0 d L ω γ hVpos hNpos hKpos (hKb L (by omega))

theorem dirac_search_d2 (ω γ : ℝ)
    (hlog : ∃ c₀ C : ℝ, 0 < c₀ ∧ 0 < C ∧
      ∀ L : ℕ, 1 ≤ L →
        |V0 2 L ω γ - c₀ * Real.log (NSites 2 L : ℝ)| ≤ C) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      searchTime 2 L ω γ ≤ C * Real.sqrt ((NSites 2 L : ℝ) * Real.log (NSites 2 L : ℝ)) ∧
      successProb 2 L ω γ * Real.log (NSites 2 L : ℝ) ≤ K := by
  obtain ⟨c₀, C, hc₀, hC, hbd⟩ := hlog
  set t : ℝ := max 1 (2 * C / c₀) with htdef
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht2 : 2 * C / c₀ ≤ t := le_max_right _ _
  refine ⟨Real.pi / 2 * Real.sqrt (c₀ + C), 2 / c₀, ?_, ?_,
    ⟨Nat.ceil (Real.exp (t / 2)) + 1, ?_⟩⟩
  · have : 0 < c₀ + C := by linarith
    positivity
  · positivity
  · intro L hL

    have hL1 : 1 ≤ L := by omega
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hNpos : (0 : ℝ) < (NSites 2 L : ℝ) := by
      unfold NSites
      push_cast
      exact pow_pos hLpos 2
    set Lg : ℝ := Real.log (NSites 2 L : ℝ) with hLgdef
    have hlogN_eq : Lg = 2 * Real.log (L : ℝ) := by
      rw [hLgdef]
      unfold NSites
      push_cast
      rw [Real.log_pow]
      norm_num

    have hexp_le : Real.exp (t / 2) ≤ (L : ℝ) := by
      have hceil : Real.exp (t / 2) ≤ (Nat.ceil (Real.exp (t / 2)) : ℝ) := Nat.le_ceil _
      have hle : (Nat.ceil (Real.exp (t / 2)) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (t / 2)) ≤ L)
      linarith
    have hlogL : t / 2 ≤ Real.log (L : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos (t / 2)) hexp_le
      rwa [Real.log_exp] at h
    have hLg_ge : t ≤ Lg := by
      rw [hlogN_eq]; linarith
    have hLg1 : 1 ≤ Lg := le_trans ht1 hLg_ge
    have hLgpos : 0 < Lg := lt_of_lt_of_le one_pos hLg1

    have hVbd := hbd L hL1
    have hup : V0 2 L ω γ ≤ c₀ * Lg + C := by
      have := (abs_le.mp hVbd).2
      linarith
    have hlow : c₀ * Lg - C ≤ V0 2 L ω γ := by
      have := (abs_le.mp hVbd).1
      linarith
    constructor
    · have hVle : V0 2 L ω γ ≤ (c₀ + C) * Lg := by nlinarith
      have hVNle : V0 2 L ω γ * (NSites 2 L : ℝ) ≤
          (c₀ + C) * Lg * (NSites 2 L : ℝ) :=
        mul_le_mul_of_nonneg_right hVle (le_of_lt hNpos)
      have hsqrt_le : Real.sqrt (V0 2 L ω γ * (NSites 2 L : ℝ)) ≤
          Real.sqrt (c₀ + C) * Real.sqrt (Lg * (NSites 2 L : ℝ)) := by
        calc Real.sqrt (V0 2 L ω γ * (NSites 2 L : ℝ))
            ≤ Real.sqrt ((c₀ + C) * Lg * (NSites 2 L : ℝ)) := Real.sqrt_le_sqrt hVNle
          _ = Real.sqrt ((c₀ + C) * (Lg * (NSites 2 L : ℝ))) := by rw [mul_assoc]
          _ = Real.sqrt (c₀ + C) * Real.sqrt (Lg * (NSites 2 L : ℝ)) :=
              Real.sqrt_mul (by linarith) _
      unfold searchTime
      calc Real.pi / 2 * Real.sqrt (V0 2 L ω γ * (NSites 2 L : ℝ))
          ≤ Real.pi / 2 * (Real.sqrt (c₀ + C) *
              Real.sqrt (Lg * (NSites 2 L : ℝ))) :=
            mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
        _ = (Real.pi / 2 * Real.sqrt (c₀ + C)) *
              Real.sqrt ((NSites 2 L : ℝ) * Real.log (NSites 2 L : ℝ)) := by
            rw [← hLgdef, show Lg * (NSites 2 L : ℝ) = (NSites 2 L : ℝ) * Lg by ring]
            ring
    · have h2C : 2 * C ≤ c₀ * Lg := by
        have h := mul_le_mul_of_nonneg_right (le_trans ht2 hLg_ge) (le_of_lt hc₀)
        rw [div_mul_cancel₀ (2 * C) (ne_of_gt hc₀)] at h
        nlinarith
      have hlowpos : 0 < c₀ * Lg - C := by
        have hhalf : c₀ * Lg / 2 ≤ c₀ * Lg - C := by linarith
        have : 0 < c₀ * Lg / 2 := by positivity
        linarith
      have hcLgHalf : 0 < c₀ * Lg / 2 := by positivity
      have hrec : 1 / (c₀ * Lg - C) ≤ 1 / (c₀ * Lg / 2) :=
        one_div_le_one_div_of_le hcLgHalf (by linarith)
      have hsP : successProb 2 L ω γ ≤ 1 / (c₀ * Lg - C) := by
        unfold successProb
        exact one_div_le_one_div_of_le hlowpos hlow
      calc successProb 2 L ω γ * Real.log (NSites 2 L : ℝ)
          = successProb 2 L ω γ * Lg := by rw [← hLgdef]
        _ ≤ (1 / (c₀ * Lg - C)) * Lg :=
            mul_le_mul_of_nonneg_right hsP (le_of_lt hLgpos)
        _ ≤ (1 / (c₀ * Lg / 2)) * Lg :=
            mul_le_mul_of_nonneg_right hrec (le_of_lt hLgpos)
        _ = 2 / c₀ := by
            field_simp

end Qatlib.Papers.DiracSearch04.MainResults
