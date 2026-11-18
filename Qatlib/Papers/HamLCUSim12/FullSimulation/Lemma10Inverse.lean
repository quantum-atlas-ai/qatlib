/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Lemma 10 — defect of the normalized correction map `E_k`

Fixed source: Childs and Wiebe, arXiv:1202.5822v1, Lemma 10, Eq. (55):
with `E_k(λ)` the normalized positive-coefficient map of Eq. (53) and
`2 m k (5/3)^{k-1} h λ ≤ 1/2`, one has
`max_ψ ‖(1 − E_k(−λ) E_k(λ)) ψ‖ ≤ (2 m k (5/3)^{k-1} h λ)^{4k+2}`.

The source proof divides by the normalization denominators: the composition
numerator `‖Rem_{4k+1}(Σ_p Σ_q |C_p||C_q| S_k(−λ/ℓ_p)^p S_k(λ/ℓ_q)^q)‖` is
bounded via Lemma 9, the `e^x` factor is cut by `8/3·mk(5/3)^{k-1}hλ ≤ 2/3`,
Stirling's bound converts `(4k+2)!`, and the denominator
`min_φ ‖Σ_p |C_p| S_k(λ/ℓ_p)^p φ‖² ≥ (3/4)²‖C‖₁²` cancels the mass factor.

This module formalizes the normalization step exactly: the composite map
`E_k(−λ) ∘ E_k(λ)` equals `z/‖z‖` with `z = V(−λ)(V(λ)ψ)`, and a vector
within `ν` of a unit vector normalizes to within `2ν`. With the numerator
bound in the source's Stirling-folded form (the `(3/4)²‖C‖₁²` denominator
cancellation folded into the constant `2·(16/9)`), and the certified bounds
`e < 68/25`, `π > 3`, `2mk(5/3)^{k-1}hλ ≤ 1/2`, this yields the printed
bound `(2 m k (5/3)^{k-1} h λ)^{4k+2}`.

This is a conditional normalization estimate. The Taylor composition error
`hnum` is an input, and no Suzuki aggregate, Hamiltonian evolution or
operator-norm estimate for the nonlinear map is constructed here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalization stability: a vector `z` within `ν < 1` of a unit vector
normalizes to a unit vector within `2ν`. -/
theorem norm_div_two (z ψ : E) (ν : ℝ) (hψ : ‖ψ‖ = 1) (hν : ‖z - ψ‖ ≤ ν)
    (hν1 : ν < 1) : ‖ψ - (‖z‖)⁻¹ • z‖ ≤ 2 * ν := by
  have hdge : 1 - ν ≤ ‖z‖ := by
    have h1 : ‖ψ‖ - ‖z‖ ≤ ‖z - ψ‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le ψ z
    rw [hψ] at h1
    have h2 := h1.trans hν
    linarith
  have h1pos : (0 : ℝ) < 1 - ν := by linarith
  have hdpos : 0 < ‖z‖ := h1pos.trans_le hdge
  have hsplit : ψ - (‖z‖)⁻¹ • z = (ψ - z) + (1 - (‖z‖)⁻¹) • z := by
    rw [sub_smul, one_smul, sub_add_sub_cancel]
  have hsecond : ‖(1 - (‖z‖)⁻¹) • z‖ ≤ ν := by
    rw [norm_smul, Real.norm_eq_abs, mul_comm,
      show (1 : ℝ) - (‖z‖)⁻¹ = (‖z‖ - 1) / ‖z‖ by field_simp [ne_of_gt hdpos],
      abs_div, abs_of_pos hdpos]
    rw [show ‖z‖ * (|‖z‖ - 1| / ‖z‖) = |‖z‖ - 1| by field_simp [ne_of_gt hdpos]]
    have habs : |‖z‖ - ‖ψ‖| ≤ ‖z - ψ‖ := by
      refine abs_le.mpr ⟨neg_le.mpr ?_, norm_sub_norm_le z ψ⟩
      have h2 : ‖ψ‖ - ‖z‖ ≤ ‖z - ψ‖ := by
        have h3 := norm_sub_norm_le ψ z
        rwa [norm_sub_rev] at h3
      linarith
    have habs' : |‖z‖ - 1| ≤ ‖z - ψ‖ := by simpa only [hψ] using habs
    exact habs'.trans hν
  calc ‖ψ - (‖z‖)⁻¹ • z‖
      ≤ ‖ψ - z‖ + ‖(1 - (‖z‖)⁻¹) • z‖ := by
          rw [hsplit]
          exact norm_add_le _ _
    _ ≤ ν + ν := add_le_add (by rwa [norm_sub_rev]) hsecond
    _ = 2 * ν := by ring

/-- Eq. (53): the normalized correction map applied to a vector, for the
positive-coefficient aggregate `V s`. -/
def ekMap (V : ℝ → (E →L[ℝ] E)) (s : ℝ) (x : E) : E := (‖V s x‖)⁻¹ • (V s x)

/-- The composite correction map `E_k(−λ) ∘ E_k(λ)` equals `z/‖z‖` for
`z = V(−λ)(V(λ)ψ)`: the inner normalization cancels against the outer one. -/
theorem ek_composition (V : ℝ → (E →L[ℝ] E)) (lam : ℝ) (ψ : E)
    (hd1 : ‖V lam ψ‖ ≠ 0) :
    ekMap V (-lam) (ekMap V lam ψ) =
      (‖V (-lam) (V lam ψ)‖)⁻¹ • (V (-lam) (V lam ψ)) := by
  have hd1pos : 0 < ‖V lam ψ‖ := by
    rcases lt_or_eq_of_le (norm_nonneg (V lam ψ)) with h | h
    · exact h
    · exact absurd h.symm hd1
  have h1 : V (-lam) ((‖V lam ψ‖)⁻¹ • V lam ψ) =
      (‖V lam ψ‖)⁻¹ • (V (-lam) (V lam ψ)) := by
    rw [map_smul]
  simp only [ekMap]
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd1pos), smul_smul]
  simp [mul_inv_rev, hd1]

/-- Normalizing twice cancels the intermediate normalization even when its
denominator vanishes: in that case linearity makes both sides zero. -/
theorem ek_composition_all (V : ℝ → (E →L[ℝ] E)) (lam : ℝ) (ψ : E) :
    ekMap V (-lam) (ekMap V lam ψ) =
      (‖V (-lam) (V lam ψ)‖)⁻¹ • (V (-lam) (V lam ψ)) := by
  by_cases hd : ‖V lam ψ‖ = 0
  · have hz : V lam ψ = 0 := norm_eq_zero.mp hd
    simp [ekMap, hz]
  · exact ek_composition V lam ψ hd

/-- Approximating a pair of inverse contractions within operator error `ε`
bounds the unnormalized composite defect by `2ε + ε²` on every unit vector.
The numerator estimate is derived from the two actual linear maps. -/
theorem composition_defect_of_approx (A B U W : E →L[ℝ] E) (ε : ℝ)
    (hε : 0 ≤ ε) (hA : ‖A - U‖ ≤ ε) (hB : ‖B - W‖ ≤ ε)
    (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hinv : W (U ψ) = ψ) :
    ‖B (A ψ) - ψ‖ ≤ 2 * ε + ε ^ 2 := by
  have hdiff : ‖A ψ - U ψ‖ ≤ ε := by
    calc
      _ = ‖(A - U) ψ‖ := rfl
      _ ≤ ‖A - U‖ * ‖ψ‖ := (A - U).le_opNorm ψ
      _ ≤ ε := by simpa only [hψ, mul_one] using hA
  have hunit : ‖U ψ‖ ≤ 1 := by
    calc
      _ ≤ ‖U‖ * ‖ψ‖ := U.le_opNorm ψ
      _ ≤ 1 := by simpa only [hψ, mul_one] using hU
  have hsize : ‖A ψ‖ ≤ 1 + ε := by
    calc
      _ = ‖U ψ + (A ψ - U ψ)‖ := by congr 1; abel
      _ ≤ ‖U ψ‖ + ‖A ψ - U ψ‖ := norm_add_le _ _
      _ ≤ 1 + ε := add_le_add hunit hdiff
  have hsplit : B (A ψ) - ψ = (B - W) (A ψ) + W (A ψ - U ψ) := by
    simp only [sub_apply, map_sub, hinv]
    abel
  calc
    _ = ‖(B - W) (A ψ) + W (A ψ - U ψ)‖ := congrArg norm hsplit
    _ ≤ ‖(B - W) (A ψ)‖ + ‖W (A ψ - U ψ)‖ := norm_add_le _ _
    _ ≤ ‖B - W‖ * ‖A ψ‖ + ‖W‖ * ‖A ψ - U ψ‖ :=
      add_le_add ((B - W).le_opNorm _) (W.le_opNorm _)
    _ ≤ ε * (1 + ε) + 1 * ε := add_le_add
      (mul_le_mul hB hsize (norm_nonneg _) hε)
      (mul_le_mul hW hdiff (norm_nonneg _) zero_le_one)
    _ = 2 * ε + ε ^ 2 := by ring

/-- A concrete pair of operator approximations to inverse contractions yields
the normalized inverse estimate, without an assumed composition numerator or
nonzero normalization denominator. The small-time input is the explicit
one-step error `0 ≤ ε ≤ 1/4`; no Suzuki remainder theorem is asserted here. -/
theorem normalized_inverse_of_approx (V : ℝ → (E →L[ℝ] E)) (lam : ℝ)
    (U W : E →L[ℝ] E) (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hplus : ‖V lam - U‖ ≤ ε) (hminus : ‖V (-lam) - W‖ ≤ ε)
    (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1)
    (ψ : E) (hψ : ‖ψ‖ = 1) (hinv : W (U ψ) = ψ) :
    ‖ψ - ekMap V (-lam) (ekMap V lam ψ)‖ ≤ 5 * ε := by
  have hnum := composition_defect_of_approx (V lam) (V (-lam)) U W ε
    hε hplus hminus hU hW ψ hψ hinv
  have hsquare : ε ^ 2 ≤ ε / 4 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hsmall)]
  have hlt : 2 * ε + ε ^ 2 < 1 := by nlinarith
  rw [ek_composition_all]
  exact (norm_div_two _ _ _ hψ hnum hlt).trans (by nlinarith)

/-- Lemma 10, Eq. (55): with the source's Stirling-folded numerator bound on
the un-normalized composition (the `(3/4)²‖C‖₁²` denominator cancellation
folded into the constant `2·(16/9)`), and the source regime
`2mk(5/3)^{k-1}hλ ≤ 1/2`, the normalized
composite correction map defects by at most `(2mk(5/3)^{k-1}hλ)^{4k+2}` on
unit vectors. -/
theorem lemma10_inverse_defect (k : ℕ) (hk : 1 ≤ k) (m h lam : ℝ)
    (hm : 1 ≤ m) (hh : 0 ≤ h) (hlam : 0 ≤ lam)
    (hreg : 2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam ≤ 1 / 2)
    (V : ℝ → (E →L[ℝ] E))
    (hnum : ∀ φ : E, ‖φ‖ = 1 → ‖V (-lam) (V lam φ) - φ‖ ≤
      2 * (16 / 9) * ((2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2)
        / (Real.sqrt (12 * Real.pi) * Real.exp (25 / 26)))
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    ‖ψ - ekMap V (-lam) (ekMap V lam ψ)‖ ≤
      (2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2) := by
  have hfivethree : (0 : ℝ) < (5 : ℝ) / 3 := by norm_num
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hXnn : 0 ≤ m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ m)
      (pow_nonneg hfivethree.le _)) hh) hlam
  have hYnn : 0 ≤ 2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := by positivity
  have h2m : 2 * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam ≤
      2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := by
    have hmul := mul_le_mul_of_nonneg_right hkR hXnn
    nlinarith [hmul]
  have hE : Real.exp 1 < 68 / 25 := by
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hsqrt : (6 : ℝ) ≤ Real.sqrt (12 * Real.pi) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have hexp25 : (1 : ℝ) ≤ Real.exp (25 / 26) := Real.one_le_exp (by norm_num)
  set Y : ℝ := 2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam with hY
  set ν : ℝ := 2 * (16 / 9) *
    ((2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2) /
      (Real.sqrt (12 * Real.pi) * Real.exp (25 / 26)) with hν
  have hνψ : ‖V (-lam) (V lam ψ) - ψ‖ ≤ ν := hnum ψ hψ
  have hkey : 2 * ν ≤ Y ^ (4 * k + 2) := by
    have he3 : Real.exp 1 / 3 ≤ 68 / 75 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 75)]
      nlinarith [hE]
    have hprodle : (2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam ≤
        (68 / 75) * Y := by
      have hsplit : (2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam =
          (Real.exp 1 / 3) * (2 * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) := by ring
      rw [hsplit]
      calc (Real.exp 1 / 3) * (2 * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam)
          ≤ (Real.exp 1 / 3) * Y := mul_le_mul_of_nonneg_left h2m (by positivity)
        _ ≤ (68 / 75) * Y := by
            refine mul_le_mul_of_nonneg_right he3 hYnn
    have hnn : 0 ≤ (2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam := by
      have : (0:ℝ) < Real.exp 1 := Real.exp_pos _
      positivity
    have hpowmono : ((2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2) ≤
        ((68 / 75) * Y) ^ (4 * k + 2) :=
      pow_le_pow_left₀ hnn hprodle _
    have hpowsplit : ((68 / 75) * Y) ^ (4 * k + 2) =
        (68 / 75) ^ (4 * k + 2) * Y ^ (4 * k + 2) := mul_pow _ _ _
    have h6 : (6 : ℕ) ≤ 4 * k + 2 := by omega
    have hpowdec : (68 / 75 : ℝ) ^ (4 * k + 2) ≤ (68 / 75) ^ (6 : ℕ) := by
      rw [show 4 * k + 2 = 6 + (4 * k - 4) by omega, pow_add]
      refine mul_le_of_le_one_right (pow_nonneg (by norm_num) _) ?_
      exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 68 / 75) (by norm_num)
    have hconst : 2 * (2 * (16 / 9 : ℝ)) * ((68 / 75) ^ (6 : ℕ)) / 6 ≤ 1 := by norm_num
    have hdenom : (6 : ℝ) ≤ Real.sqrt (12 * Real.pi) * Real.exp (25 / 26) := by
      calc (6 : ℝ) = 6 * 1 := by norm_num
        _ ≤ Real.sqrt (12 * Real.pi) * Real.exp (25 / 26) :=
          mul_le_mul hsqrt hexp25 (by norm_num) (by positivity)
    have hYpow : (0:ℝ) ≤ Y ^ (4 * k + 2) := pow_nonneg hYnn _
    have hdenompos : 0 < Real.sqrt (12 * Real.pi) * Real.exp (25 / 26) := by
      positivity
    have htop : 2 * (2 * (16 / 9 : ℝ)) *
        ((2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2) ≤
        2 * (2 * (16 / 9 : ℝ)) * ((68 / 75 : ℝ) ^ (6 : ℕ) * Y ^ (4 * k + 2)) := by
      calc _ ≤ 2 * (2 * (16 / 9 : ℝ)) * (((68 / 75) * Y) ^ (4 * k + 2)) :=
          mul_le_mul_of_nonneg_left hpowmono (by norm_num)
        _ = 2 * (2 * (16 / 9 : ℝ)) *
            ((68 / 75 : ℝ) ^ (4 * k + 2) * Y ^ (4 * k + 2)) := by rw [hpowsplit]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpowdec hYpow) (by norm_num)
    calc 2 * ν
        = (2 * (2 * (16 / 9 : ℝ)) *
            ((2 * Real.exp 1 / 3) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2)) /
              (Real.sqrt (12 * Real.pi) * Real.exp (25 / 26)) := by rw [hν]; ring
      _ ≤ (2 * (2 * (16 / 9 : ℝ)) *
            ((68 / 75 : ℝ) ^ (6 : ℕ) * Y ^ (4 * k + 2))) /
              (Real.sqrt (12 * Real.pi) * Real.exp (25 / 26)) :=
          div_le_div_of_nonneg_right htop hdenompos.le
      _ ≤ (2 * (2 * (16 / 9 : ℝ)) *
            ((68 / 75 : ℝ) ^ (6 : ℕ) * Y ^ (4 * k + 2))) / 6 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom
      _ = (2 * (2 * (16 / 9 : ℝ)) * ((68 / 75 : ℝ) ^ (6 : ℕ)) / 6) * Y ^ (4 * k + 2) := by
          ring
      _ ≤ 1 * Y ^ (4 * k + 2) := mul_le_mul_of_nonneg_right hconst hYpow
      _ = Y ^ (4 * k + 2) := by ring
  have hνlt : ν < 1 := by
    have hYle : Y ≤ 1 / 2 := hreg
    have hYpowle : Y ^ (4 * k + 2) ≤ (1 / 2) ^ (4 * k + 2) := pow_le_pow_left₀ hYnn hYle _
    have h6pow : ((1 / 2 : ℝ) ^ (4 * k + 2)) ≤ (1 / 2 : ℝ) ^ (6 : ℕ) := by
      rw [show 4 * k + 2 = 6 + (4 * k - 4) by omega, pow_add]
      refine mul_le_of_le_one_right (pow_nonneg (by norm_num) _) ?_
      exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hhalf : (1 / 2 : ℝ) ^ (6 : ℕ) = 1 / 64 := by norm_num
    nlinarith [hkey, hYpowle, h6pow, hhalf]
  have hd2pos : 0 < ‖V (-lam) (V lam ψ)‖ := by
    have h1 : (1 : ℝ) - ν ≤ ‖V (-lam) (V lam ψ)‖ := by
      have hlow : ‖ψ‖ - ‖V (-lam) (V lam ψ)‖ ≤ ‖V (-lam) (V lam ψ) - ψ‖ := by
        rw [← norm_sub_rev]
        exact norm_sub_norm_le ψ _
      rw [hψ] at hlow
      have h2 := hlow.trans hνψ
      linarith
    have hpos : (0 : ℝ) < 1 - ν := by linarith
    exact hpos.trans_le h1
  rw [ek_composition_all V lam ψ]
  calc ‖ψ - (‖V (-lam) (V lam ψ)‖)⁻¹ • (V (-lam) (V lam ψ))‖
      ≤ 2 * ν := norm_div_two _ _ ν hψ hνψ hνlt
    _ ≤ Y ^ (4 * k + 2) := hkey
    _ = (2 * (k : ℝ) * m * ((5 : ℝ) / 3) ^ (k - 1) * h * lam) ^ (4 * k + 2) := by
        rw [hY]

end Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse
