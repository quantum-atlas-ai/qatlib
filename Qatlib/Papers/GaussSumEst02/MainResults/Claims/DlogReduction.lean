/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost
import Qatlib.Papers.GaussSumEst02.MainResults.Source.PhaseSampling

/-!
# Discrete logarithms from Gauss-sum phases

This module relates the discrete logarithm of a nonzero field element to the ratio of two
Gauss-sum phases. The theorem `lemma2_dlogReduction` includes uniqueness of the encoded exponent
and a conditional estimation-cost bound using `PhaseAccessModel`. See [VanDamSeroussi2002].

## Main statements

* `exp_neg_two_pi_div_injective`: For positive `n`, the values `exp(-2πiℓ/n)` distinguish
  natural exponents strictly below `n`.
* `lemma2_dlogReduction`: Under the generator and character-value hypotheses, a nonzero element
  has a bounded discrete logarithm uniquely encoded by the ratio of its Gauss-sum phase to the
  phase at one. Given `PhaseAccessModel` and a polylogarithmic per-sample cost, the phase
  difference has protocols of arbitrarily small expected absolute error with the stated
  `sampleCount` cost bound.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.MainResults.Claims

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- For positive `n`, the values `exp(-2πiℓ/n)` distinguish natural exponents strictly below `n`
[VanDamSeroussi2002]. -/
lemma exp_neg_two_pi_div_injective {n : ℕ} (hn : 0 < n) :
    ∀ ℓ ℓ' : ℕ, ℓ < n → ℓ' < n →
      Complex.exp ((-(2 * Real.pi * (ℓ' : ℝ) / (n : ℝ))) * Complex.I)
        = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ) / (n : ℝ))) * Complex.I) → ℓ' = ℓ := by
  intro ℓ ℓ' hℓ hℓ' he
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set a : ℝ := -(2 * Real.pi * (ℓ' : ℝ) / (n : ℝ)) with ha
  set b : ℝ := -(2 * Real.pi * (ℓ : ℝ) / (n : ℝ)) with hb
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hcancel : (((a - b : ℝ)) : ℂ) = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
    have h : (((a - b : ℝ)) : ℂ) * Complex.I
        = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      have hk' : (a : ℂ) * Complex.I
          = (b : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        simpa [ha, hb, mul_assoc, mul_comm, mul_left_comm] using hk
      rw [sub_mul, hk']
      ring
    exact mul_right_cancel₀ hI h
  have hre : a - b = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.re hcancel
    simpa using this
  have hkey : (ℓ : ℝ) - ℓ' = (k : ℝ) * n := by
    simp only [ha, hb] at hre
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hre ⊢
    nlinarith [hre]
  have habs : |(ℓ : ℝ) - ℓ'| < (n : ℝ) := by
    rw [abs_lt]
    constructor
    · have h1 : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
      have h2 : (ℓ' : ℝ) < (n : ℝ) := by exact_mod_cast hℓ'
      linarith
    · have h1 : (ℓ : ℝ) < (n : ℝ) := by exact_mod_cast hℓ
      have h2 : (0 : ℝ) ≤ (ℓ' : ℝ) := by positivity
      linarith
  have hkn : |(k : ℝ)| * (n : ℝ) < (n : ℝ) := by
    have h := habs
    rw [hkey, abs_mul, abs_of_pos hnR] at h
    exact h
  have hlt : |(k : ℝ)| < 1 := by nlinarith [hkn, hnR]
  have hkabs : -(1 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1 := abs_lt.mp hlt
  have hk0 : k = 0 := by
    have hk_le : k ≤ 0 := by
      by_contra h
      have h1 : (1 : ℤ) ≤ k := by omega
      have h1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
      linarith [hkabs.2]
    have hk_ge : 0 ≤ k := by
      by_contra h
      have h1 : k ≤ -1 := by omega
      have h1R : (k : ℝ) ≤ -1 := by exact_mod_cast h1
      linarith [hkabs.1]
    omega
  subst hk0
  simp only [Int.cast_zero, zero_mul] at hkey
  have hEq : (ℓ : ℝ) = (ℓ' : ℝ) := by linarith
  exact eq_comm.mp (by exact_mod_cast hEq)

/-- Under the generator and character-value hypotheses, a nonzero element has a bounded discrete
logarithm uniquely encoded by the ratio of its Gauss-sum phase to the phase at one. Given
`PhaseAccessModel` and a polylogarithmic per-sample cost, the phase difference has protocols
of arbitrarily small expected absolute error with the stated `sampleCount` cost bound
[VanDamSeroussi2002]. -/
theorem lemma2_dlogReduction {K : Type*} [Field K] [Fintype K] (χ : MultChar K)
    (e : AddChar K) (g : K)
    (hgen : ∀ y : K, y ≠ 0 → ∃ j : ℕ, j < Fintype.card K - 1 ∧ g ^ j = y)
    (hχg : ∀ j : ℕ, j < Fintype.card K - 1 →
      χ.toFun (g ^ j)
        = Complex.exp (((2 * Real.pi * (j : ℝ)) / ((Fintype.card K - 1 : ℕ) : ℝ))
            * Complex.I))
    (hnt : χ.IsNontrivial) {x : K} (hx : x ≠ 0)
    (perSample : ℕ → ℕ) (hper : PolyLog perSample) (M : PhaseAccessModel) :
    ∃ γ : K → ℝ,
      (∀ β : K, β ≠ 0 →
        gaussSum χ.toFun e β
          = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γ β * Complex.I)) ∧
      ∃ ℓ : ℕ, ℓ < Fintype.card K - 1 ∧ g ^ ℓ = x ∧
        Complex.exp (γ x * Complex.I)
          = Complex.exp (γ 1 * Complex.I)
            * Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
                / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) ∧
        (∀ ℓ' : ℕ, ℓ' < Fintype.card K - 1 →
          Complex.exp ((-(2 * Real.pi * (ℓ' : ℝ)
              / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I)
            = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
                / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) →
          ℓ' = ℓ) ∧
        ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ ε : ℝ, 0 < ε →
          ∃ (P : SamplingProtocol) (t : ℕ), 0 < t ∧
            expectedAngularError (γ x - γ 1) P t < ε ∧
            t * perSample (Fintype.card K)
              ≤ C * sampleCount ε * bitLength (Fintype.card K) ^ d := by
  classical
  have hex : ∀ β : K, β ≠ 0 → ∃ γ : ℝ, gaussSum χ.toFun e β
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γ * Complex.I) :=
    fun β hβ => gaussSum_polar χ e hnt hβ
  let γ : K → ℝ := fun β => if h : β = 0 then 0 else Classical.choose (hex β h)
  have hγ : ∀ β : K, β ≠ 0 → gaussSum χ.toFun e β
      = (Real.sqrt (Fintype.card K) : ℂ) * Complex.exp (γ β * Complex.I) := by
    intro β hβ
    have hchoice : γ β = Classical.choose (hex β hβ) := by
      simp only [γ, dif_neg hβ]
    rw [hchoice]
    exact Classical.choose_spec (hex β hβ)
  obtain ⟨ℓ, hℓ, hxℓ⟩ := hgen x hx
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hsqrt_ne : ((Real.sqrt (Fintype.card K) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'
  have hscale : gaussSum χ.toFun e x = χ.toFun x⁻¹ * gaussSum χ.toFun e 1 := by
    simpa using gaussSum_scale χ e (β := x) (δ := (1 : K)) hx
  have hθ : χ.toFun x
      = Complex.exp (((2 * Real.pi * (ℓ : ℝ)) / ((Fintype.card K - 1 : ℕ) : ℝ))
          * Complex.I) := by
    rw [← hxℓ]
    exact hχg ℓ hℓ
  have hχx_inv : χ.toFun x⁻¹
      = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
          / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) := by
    rw [χ.inv_apply hx, hθ, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hkey : Complex.exp (γ x * Complex.I)
      = Complex.exp (γ 1 * Complex.I)
        * Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
            / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) := by
    have hx1 := hγ x hx
    have h11 := hγ 1 one_ne_zero
    have hG := hscale
    rw [hx1, h11, hχx_inv] at hG
    have hc : Complex.exp (γ x * Complex.I)
        = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
            / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I)
          * Complex.exp (γ 1 * Complex.I) := by
      apply mul_left_cancel₀ hsqrt_ne
      rw [hG]
      ring
    calc Complex.exp (γ x * Complex.I)
        = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
            / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I)
          * Complex.exp (γ 1 * Complex.I) := hc
      _ = Complex.exp (γ 1 * Complex.I)
          * Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
              / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) := mul_comm _ _
  have hinj : ∀ ℓ' : ℕ, ℓ' < Fintype.card K - 1 →
      Complex.exp ((-(2 * Real.pi * (ℓ' : ℝ)
          / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I)
        = Complex.exp ((-(2 * Real.pi * (ℓ : ℝ)
            / ((Fintype.card K - 1 : ℕ) : ℝ))) * Complex.I) →
      ℓ' = ℓ :=
    fun ℓ' hℓ' he => exp_neg_two_pi_div_injective (by omega) ℓ ℓ' hℓ hℓ' he
  refine ⟨γ, hγ, ℓ, hℓ, hxℓ, hkey, hinj, ?_⟩
  obtain ⟨C₀, hC₀, hbound⟩ := M.queries_bound
  obtain ⟨c, d, hc, hd, hperb⟩ := hper
  refine ⟨C₀ * c, d, Nat.mul_pos hC₀ hc, hd, ?_⟩
  intro ε hε
  refine ⟨M.protocol ε, M.queries ε, M.queries_pos ε hε,
    M.accuracy (γ x - γ 1) ε hε, ?_⟩
  calc M.queries ε * perSample (Fintype.card K)
      ≤ (C₀ * sampleCount ε) * (c * bitLength (Fintype.card K) ^ d) :=
        Nat.mul_le_mul (hbound ε hε) (hperb _)
    _ = (C₀ * c) * sampleCount ε * bitLength (Fintype.card K) ^ d := by ring

end Qatlib.Papers.GaussSumEst02.MainResults.Claims
