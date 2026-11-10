/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset
open MeasureTheory

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.SpectralHitting

def eigenPhase (E t : ℝ) : ℂ :=
  Complex.exp ((-(E * t)) * Complex.I)

def phaseKernel (θ τ : ℝ) : ℂ :=
  if θ = 0 then (τ : ℂ) else
    (Complex.exp ((θ * τ) * Complex.I) - 1) / (Complex.I * θ)

structure SpectralWalk (n N : ℕ) where

  energy : Fin N → ℝ

  entranceAmp : Fin N → ℝ

  exitAmp : Fin N → ℝ

  entrance_norm : (∑ i, entranceAmp i ^ 2) = 1

  exit_norm : (∑ i, exitAmp i ^ 2) = 1

  reflection : ∀ i, exitAmp i ^ 2 = entranceAmp i ^ 2

  energy_injective : Function.Injective energy

namespace SpectralWalk

variable {n N : ℕ} (S : SpectralWalk n N)

def coefficient (i : Fin N) : ℝ := S.exitAmp i * S.entranceAmp i

def transitionAmplitude (t : ℝ) : ℂ :=
  ∑ i, (S.coefficient i : ℂ) * eigenPhase (S.energy i) t

def exitProbability (t : ℝ) : ℝ := ‖S.transitionAmplitude t‖ ^ 2

def timeAveragedExitProbability (τ : ℝ) : ℝ :=
  (1 / τ) * ∫ t in (0)..τ, S.exitProbability t

def diagonal : ℝ := ∑ i, S.coefficient i ^ 2

def offDiagonalSum (τ : ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    (S.coefficient i * S.coefficient j) *
      (phaseKernel (S.energy i - S.energy j) τ).re

def rawSpectralSum (τ : ℝ) : ℝ :=
  ∑ i, ∑ j, (S.coefficient i * S.coefficient j) *
    (phaseKernel (S.energy i - S.energy j) τ).re

lemma star_mul_self (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  simpa using (Complex.normSq_eq_conj_mul_self (z := z)).symm

lemma star_eigenPhase (E t : ℝ) :
    star (eigenPhase E t) = Complex.exp ((E * t) * Complex.I) := by
  unfold eigenPhase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma star_mul_eigenPhase_pair (a b E F t : ℝ) :
    star ((a : ℂ) * eigenPhase E t) * ((b : ℂ) * eigenPhase F t)
      = ((a * b : ℝ) : ℂ) * Complex.exp (((E - F) * t) * Complex.I) := by
  have hs : star ((a : ℂ) * eigenPhase E t)
      = (a : ℂ) * Complex.exp ((E * t) * Complex.I) := by
    rw [star_mul, star_eigenPhase]
    rw [show star (a : ℂ) = (a : ℂ) from Complex.conj_ofReal a]
    ring
  rw [hs]
  unfold eigenPhase
  rw [show (a : ℂ) * Complex.exp ((E * t) * Complex.I) *
        ((b : ℂ) * Complex.exp ((-(F * t)) * Complex.I))
      = ((a * b : ℝ) : ℂ) * (Complex.exp ((E * t) * Complex.I) *
          Complex.exp ((-(F * t)) * Complex.I)) by
    push_cast
    ring]
  rw [← Complex.exp_add]
  congr 2
  ring

lemma phaseKernel_norm_le (θ τ : ℝ) (hθ : θ ≠ 0) :
    ‖phaseKernel θ τ‖ ≤ 2 / |θ| := by
  unfold phaseKernel
  rw [if_neg hθ, norm_div]
  have hnum : ‖Complex.exp ((θ * τ) * Complex.I) - 1‖ ≤ 2 := by
    calc ‖Complex.exp ((θ * τ) * Complex.I) - 1‖
        ≤ ‖Complex.exp ((θ * τ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          have harg : (↑θ * ↑τ : ℂ) * Complex.I = ((θ * τ : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [harg, Complex.norm_exp_ofReal_mul_I]
          norm_num
  have hden : ‖Complex.I * (θ : ℂ)‖ = |θ| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (abs_nonneg θ)

lemma integral_exp_pos (θ τ : ℝ) :
    (∫ t in (0)..τ, Complex.exp ((θ * t) * Complex.I)) = phaseKernel θ τ := by
  by_cases hθ : θ = 0
  · subst hθ
    simp [phaseKernel]
  · unfold phaseKernel
    rw [if_neg hθ]
    have hc : (θ : ℂ) * Complex.I ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h0 | hI
      · exact hθ (Complex.ofReal_eq_zero.mp h0)
      · exact Complex.I_ne_zero hI
    have hcongr : ∀ t : ℝ, Complex.exp ((θ * t) * Complex.I)
        = Complex.exp (((θ : ℂ) * Complex.I) * (t : ℂ)) := by
      intro t
      congr 1
      ring
    simp_rw [hcongr]
    rw [integral_exp_mul_complex hc]
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hcτ : ((θ : ℂ) * Complex.I) * (τ : ℂ) = ((θ * τ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hcτ]
    ring_nf

lemma integral_exp_re (θ τ : ℝ) :
    (∫ t in (0)..τ, (Complex.exp ((θ * t) * Complex.I)).re) =
      (phaseKernel θ τ).re := by
  have hf : IntervalIntegrable (fun t : ℝ => Complex.exp ((θ * t) * Complex.I))
      volume 0 τ := Continuous.intervalIntegrable (by fun_prop) 0 τ
  have h := intervalIntegral.intervalIntegral_re (μ := volume) hf
  rw [integral_exp_pos] at h
  simpa using h

lemma normSq_transitionAmplitude {N : ℕ} (c E : Fin N → ℝ) (t : ℝ) :
    ‖∑ i, (c i : ℂ) * eigenPhase (E i) t‖ ^ 2
      = ∑ i, ∑ j,
          (star ((c i : ℂ) * eigenPhase (E i) t) *
            ((c j : ℂ) * eigenPhase (E j) t)).re := by
  have h1 : ‖∑ i, (c i : ℂ) * eigenPhase (E i) t‖ ^ 2
      = (star (∑ i, (c i : ℂ) * eigenPhase (E i) t) *
          ∑ i, (c i : ℂ) * eigenPhase (E i) t).re := by
    rw [star_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, star_sum, Finset.sum_mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.re_sum]

lemma exitProbability_eq_double_sum (S : SpectralWalk n N) (t : ℝ) :
    S.exitProbability t
      = ∑ i, ∑ j, (S.coefficient i * S.coefficient j) *
          (Complex.exp (((S.energy i - S.energy j) * t) * Complex.I)).re := by
  unfold exitProbability transitionAmplitude
  rw [normSq_transitionAmplitude]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [star_mul_eigenPhase_pair]
  simp [Complex.mul_re]

lemma integral_exitProbability (S : SpectralWalk n N) (τ : ℝ) :
    (∫ t in (0)..τ, S.exitProbability t) = S.rawSpectralSum τ := by
  have hcont : ∀ (i j : Fin N), Continuous fun t : ℝ =>
      (S.coefficient i * S.coefficient j) *
        (Complex.exp (((S.energy i - S.energy j) * t) * Complex.I)).re := by
    intro i j
    fun_prop
  simp_rw [S.exitProbability_eq_double_sum]
  unfold rawSpectralSum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hfi : IntervalIntegrable
          (fun x : ℝ => Complex.exp (((↑(S.energy i) - ↑(S.energy j)) * ↑x) * Complex.I))
          volume 0 τ := by
        apply Continuous.intervalIntegrable
        fun_prop
      have hi := intervalIntegral.intervalIntegral_re (μ := volume) hfi
      have hA : (∫ x in (0)..τ,
            Complex.exp (((↑(S.energy i) - ↑(S.energy j)) * ↑x) * Complex.I))
          = ∫ x in (0)..τ,
            Complex.exp (((↑(S.energy i - S.energy j)) * ↑x) * Complex.I) := by
        apply intervalIntegral.integral_congr
        intro x _
        push_cast
        try ring
      have hB : (∫ x in (0)..τ,
            Complex.exp (((↑(S.energy i - S.energy j)) * ↑x) * Complex.I))
          = phaseKernel (S.energy i - S.energy j) τ :=
        integral_exp_pos (S.energy i - S.energy j) τ
      rw [hA, hB] at hi
      exact hi
    · intro j _
      exact (hcont i j).intervalIntegrable 0 τ
  · intro i _
    exact Continuous.intervalIntegrable (by fun_prop) 0 τ

lemma card_pos (S : SpectralWalk n N) : 0 < N := by
  by_contra h
  have h0 : N = 0 := Nat.eq_zero_of_not_pos h
  subst h0
  have h1 := S.entrance_norm
  simp at h1

lemma n_pos (S : SpectralWalk n N) (hN : N ≤ 2 * n) : 0 < n := by
  have hNpos : 0 < N := S.card_pos
  omega

lemma diagonal_lower (S : SpectralWalk n N) (hN : N ≤ 2 * n) :
    (1 : ℝ) / (2 * (n : ℝ)) ≤ S.diagonal := by
  have hNpos : 0 < N := S.card_pos
  have hcs : (1 : ℝ) ≤ (N : ℝ) * ∑ i, (S.entranceAmp i ^ 2) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => S.entranceAmp i ^ 2)
    simpa [S.entrance_norm] using h
  have hdiag_eq : S.diagonal = ∑ i, (S.entranceAmp i ^ 2) ^ 2 := by
    unfold diagonal coefficient
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, S.reflection i]
    ring
  rw [hdiag_eq]
  have hD : (1 : ℝ) / (N : ℝ) ≤ ∑ i, (S.entranceAmp i ^ 2) ^ 2 := by
    rw [div_le_iff₀ (by exact_mod_cast hNpos)]
    simpa [mul_comm] using hcs
  have hNle : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hN
  calc (1 : ℝ) / (2 * (n : ℝ)) ≤ 1 / (N : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hNpos) hNle
    _ ≤ ∑ i, (S.entranceAmp i ^ 2) ^ 2 := hD

lemma abs_coefficient_sum_le_one (S : SpectralWalk n N) :
    (∑ i, |S.coefficient i|) ≤ 1 := by
  have hle : ∀ i, |S.coefficient i| ≤
      (S.entranceAmp i ^ 2 + S.exitAmp i ^ 2) / 2 := by
    intro i
    unfold coefficient
    have h1 : |S.exitAmp i * S.entranceAmp i| =
        |S.exitAmp i| * |S.entranceAmp i| := abs_mul _ _
    have h2 : 2 * |S.exitAmp i| * |S.entranceAmp i| ≤
        S.exitAmp i ^ 2 + S.entranceAmp i ^ 2 := by
      nlinarith [sq_nonneg (|S.exitAmp i| - |S.entranceAmp i|),
        sq_abs (S.exitAmp i), sq_abs (S.entranceAmp i)]
    rw [h1]
    nlinarith
  calc (∑ i, |S.coefficient i|) ≤
        ∑ i, (S.entranceAmp i ^ 2 + S.exitAmp i ^ 2) / 2 :=
        Finset.sum_le_sum (fun i _ => hle i)
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, S.entrance_norm, S.exit_norm]
        norm_num

lemma abs_offDiagonal_le (S : SpectralWalk n N) {ΔE : ℝ} (hΔE : 0 < ΔE)
    (hgap : ∀ i j : Fin N, i ≠ j → ΔE ≤ |S.energy i - S.energy j|) (τ : ℝ) :
    |S.offDiagonalSum τ| ≤ 2 / ΔE := by
  have hterm : ∀ i j : Fin N,
      |if i = j then (0 : ℝ) else
        (S.coefficient i * S.coefficient j) *
          (phaseKernel (S.energy i - S.energy j) τ).re|
        ≤ |S.coefficient i| * |S.coefficient j| * (2 / ΔE) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true, abs_zero]
      positivity
    · rw [if_neg hij]
      have hθ : S.energy i - S.energy j ≠ 0 := by
        intro h
        exact hij (S.energy_injective (sub_eq_zero.mp h))
      have hK : |(phaseKernel (S.energy i - S.energy j) τ).re| ≤ 2 / ΔE := by
        calc |(phaseKernel (S.energy i - S.energy j) τ).re|
            ≤ ‖phaseKernel (S.energy i - S.energy j) τ‖ := Complex.abs_re_le_norm _
          _ ≤ 2 / |S.energy i - S.energy j| := phaseKernel_norm_le _ _ hθ
          _ ≤ 2 / ΔE := by
              rw [div_le_div_iff₀ (abs_pos.mpr hθ) hΔE]
              nlinarith [hgap i j hij]
      have hnn : 0 ≤ |S.coefficient i| * |S.coefficient j| := by positivity
      calc |(S.coefficient i * S.coefficient j) *
              (phaseKernel (S.energy i - S.energy j) τ).re|
          = |S.coefficient i| * |S.coefficient j| *
              |(phaseKernel (S.energy i - S.energy j) τ).re| := by
              rw [abs_mul, abs_mul, mul_assoc]
        _ ≤ |S.coefficient i| * |S.coefficient j| * (2 / ΔE) :=
              mul_le_mul_of_nonneg_left hK hnn
  unfold offDiagonalSum
  calc |∑ i, ∑ j, (if i = j then (0 : ℝ) else
          (S.coefficient i * S.coefficient j) *
            (phaseKernel (S.energy i - S.energy j) τ).re)|
      ≤ ∑ i, |∑ j, (if i = j then (0 : ℝ) else
            (S.coefficient i * S.coefficient j) *
              (phaseKernel (S.energy i - S.energy j) τ).re)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |if i = j then (0 : ℝ) else
            (S.coefficient i * S.coefficient j) *
              (phaseKernel (S.energy i - S.energy j) τ).re| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |S.coefficient i| * |S.coefficient j| * (2 / ΔE) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hterm i j
    _ ≤ 2 / ΔE := by
          have hS : (∑ i, |S.coefficient i|) ≤ 1 := S.abs_coefficient_sum_le_one
          have hSnn : 0 ≤ ∑ i, |S.coefficient i| := by positivity
          have hd : 0 ≤ 2 / ΔE := by positivity
          have hprod : (∑ i, ∑ j, |S.coefficient i| * |S.coefficient j| * (2 / ΔE))
              = (2 / ΔE) * ((∑ i, |S.coefficient i|) *
                  (∑ j, |S.coefficient j|)) := by
            calc ∑ i, ∑ j, |S.coefficient i| * |S.coefficient j| * (2 / ΔE)
                = ∑ i, (∑ j, |S.coefficient i| * |S.coefficient j|) * (2 / ΔE) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.sum_mul]
              _ = ∑ i, (|S.coefficient i| * ∑ j, |S.coefficient j|) * (2 / ΔE) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.mul_sum]
              _ = (∑ i, |S.coefficient i| * ∑ j, |S.coefficient j|) * (2 / ΔE) := by
                    rw [← Finset.sum_mul]
              _ = ((∑ i, |S.coefficient i|) * (∑ j, |S.coefficient j|)) *
                    (2 / ΔE) := by
                    rw [← Finset.sum_mul]
              _ = (2 / ΔE) * ((∑ i, |S.coefficient i|) *
                    (∑ j, |S.coefficient j|)) := by ring
          rw [hprod]
          have hSS : (∑ i, |S.coefficient i|) * (∑ j, |S.coefficient j|) ≤ 1 := by
            have hSnn' : 0 ≤ ∑ j, |S.coefficient j| := by positivity
            have h := mul_le_mul hS hS hSnn' (by norm_num : (0:ℝ) ≤ 1)
            simpa using h
          calc (2 / ΔE) * ((∑ i, |S.coefficient i|) *
                  (∑ j, |S.coefficient j|))
              ≤ (2 / ΔE) * 1 := mul_le_mul_of_nonneg_left hSS hd
            _ = 2 / ΔE := by ring

lemma sum_split_diag {N : ℕ} (f : Fin N → Fin N → ℝ) (i : Fin N) :
    (∑ j, f i j) = f i i + ∑ j, (if i = j then 0 else f i j) := by
  have hdiag : f i i = ∑ j, if i = j then f i j else 0 := by
    rw [Finset.sum_ite_eq]
    simp
  rw [hdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j <;> simp [h]

lemma sum_diag_off {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ j, if i = j then 0 else f i j := by
  simp_rw [sum_split_diag f]
  rw [Finset.sum_add_distrib]

lemma rawSpectralSum_diag_off (S : SpectralWalk n N) (τ : ℝ) :
    S.rawSpectralSum τ = τ * S.diagonal + S.offDiagonalSum τ := by
  unfold rawSpectralSum diagonal offDiagonalSum
  rw [sum_diag_off]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [phaseKernel, sub_self, if_true, Complex.ofReal_re]
    ring

theorem lemma1_hitting_probability (S : SpectralWalk n N) (hN : N ≤ 2 * n)
    {ε ΔE τ : ℝ} (hε : 0 < ε) (hΔE : 0 < ΔE)
    (hgap : ∀ i j : Fin N, i ≠ j → ΔE ≤ |S.energy i - S.energy j|)
    (hτ : 4 * (n : ℝ) / (ε * ΔE) ≤ τ) :
    (1 / (2 * (n : ℝ))) * (1 - ε) ≤ S.timeAveragedExitProbability τ := by
  have hnpos : 0 < n := S.n_pos hN
  have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hτpos : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hτne : τ ≠ 0 := ne_of_gt hτpos
  have hdiag : (1 : ℝ) / (2 * (n : ℝ)) ≤ S.diagonal := S.diagonal_lower hN
  have hoff : |S.offDiagonalSum τ| ≤ 2 / ΔE := S.abs_offDiagonal_le hΔE hgap τ
  have hraw : S.rawSpectralSum τ = τ * S.diagonal + S.offDiagonalSum τ :=
    S.rawSpectralSum_diag_off τ
  have htime_eq : S.timeAveragedExitProbability τ =
      S.diagonal + S.offDiagonalSum τ / τ := by
    unfold timeAveragedExitProbability
    rw [S.integral_exitProbability, hraw]
    field_simp [hτne]
  have hcross : 2 / (τ * ΔE) ≤ ε / (2 * (n : ℝ)) := by
    have hεΔE : 0 < ε * ΔE := mul_pos hε hΔE
    have hτΔE : 0 < τ * ΔE := mul_pos hτpos hΔE
    have h4 : 4 * (n : ℝ) ≤ τ * (ε * ΔE) := by
      have := (div_le_iff₀ hεΔE).mp hτ
      linarith
    rw [div_le_div_iff₀ hτΔE (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    nlinarith
  have htime_ge : S.diagonal - 2 / (τ * ΔE) ≤ S.timeAveragedExitProbability τ := by
    rw [htime_eq]
    have hneg : -(|S.offDiagonalSum τ| / τ) ≤ S.offDiagonalSum τ / τ := by
      have h := div_le_div_of_nonneg_right (neg_abs_le (S.offDiagonalSum τ))
        (le_of_lt hτpos)
      rwa [neg_div] at h
    have hle : |S.offDiagonalSum τ| / τ ≤ 2 / (τ * ΔE) := by
      calc |S.offDiagonalSum τ| / τ ≤ (2 / ΔE) / τ :=
            div_le_div_of_nonneg_right hoff (le_of_lt hτpos)
        _ = 2 / (τ * ΔE) := by
            field_simp [hτne, ne_of_gt hΔE]
    linarith
  calc (1 / (2 * (n : ℝ))) * (1 - ε)
      = 1 / (2 * (n : ℝ)) - ε / (2 * (n : ℝ)) := by ring
    _ ≤ S.diagonal - 2 / (τ * ΔE) := by linarith
    _ ≤ S.timeAveragedExitProbability τ := htime_ge

end SpectralWalk

end Qatlib.Papers.QWalkSpeedup02.MainResults.QuantumWalk.SpectralHitting
