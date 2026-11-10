/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteDiscriminantSpectrum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Matrix

namespace Qatlib.Papers.QAnnealing07.MainResults.WalkSpectrum

open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath

theorem bipartitePhase_cos_true (φ : ℝ) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    bipartitePhase (Real.cos φ) true
      = Complex.exp ((-(2 * φ) : ℝ) * Complex.I) := by
  have hsinpos : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsin : Real.sqrt (1 - Real.cos φ ^ 2) = Real.sin φ := by
    have hsq : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      linarith
    rw [hsq]
    exact Real.sqrt_sq hsinpos.le
  have hcos2 : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
  have hsin2 : Real.sin (2 * φ) = 2 * Real.sin φ * Real.cos φ := Real.sin_two_mul φ
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp only [bipartitePhase, ite_true, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, hsin]
    rw [Real.cos_neg, hcos2]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp only [bipartitePhase, ite_true, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, mul_zero, one_mul, hsin]
    rw [Real.sin_neg, hsin2]
    ring

theorem bipartitePhase_cos_false (φ : ℝ) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    bipartitePhase (Real.cos φ) false
      = Complex.exp (((2 * φ) : ℝ) * Complex.I) := by
  have hsinpos : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsin : Real.sqrt (1 - Real.cos φ ^ 2) = Real.sin φ := by
    have hsq : 1 - Real.cos φ ^ 2 = Real.sin φ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      linarith
    rw [hsq]
    exact Real.sqrt_sq hsinpos.le
  have hcos2 : Real.cos (2 * φ) = 2 * Real.cos φ ^ 2 - 1 := Real.cos_two_mul φ
  have hsin2 : Real.sin (2 * φ) = 2 * Real.sin φ * Real.cos φ := Real.sin_two_mul φ
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp only [bipartitePhase, Bool.false_eq_true, ite_false, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, neg_zero, hsin]
    rw [hcos2]
  · rw [Complex.exp_ofReal_mul_I_im]
    simp only [bipartitePhase, Bool.false_eq_true, ite_false, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.neg_im, Complex.I_im, Complex.ofReal_re,
      mul_zero, neg_one_mul, hsin]
    rw [hsin2]
    ring

theorem bipartitePhase_cos_eq_exp (φ : ℝ) (h0 : 0 < φ) (hπ : φ < Real.pi / 2) :
    bipartitePhase (Real.cos φ) true = Complex.exp ((-(2 * φ) : ℝ) * Complex.I) ∧
      bipartitePhase (Real.cos φ) false = Complex.exp (((2 * φ) : ℝ) * Complex.I) :=
  ⟨bipartitePhase_cos_true φ h0 hπ, bipartitePhase_cos_false φ h0 hπ⟩

theorem bipartitePhase_one (s : Bool) : bipartitePhase 1 s = 1 := by
  unfold bipartitePhase
  simp
  norm_num

theorem source_eq14_normalized_eigenpair
    (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (a : QState I) (b : QState J) (φ : ℝ)
    (hA : IsIsometry A) (hB : IsIsometry B) (h0 : 0 < φ) (hπ : φ < Real.pi / 2)
    (hn : Normalized (Sum.elim a b))
    (hab : (Aᴴ * B) *ᵥ b = (Real.cos φ : ℂ) • a)
    (hba : (Bᴴ * A) *ᵥ a = (Real.cos φ : ℂ) • b) :
    ∀ s : Bool, Normalized (bipartiteTau A B a b (Real.cos φ) s) ∧
      bipartiteWalk A B *ᵥ bipartiteTau A B a b (Real.cos φ) s =
        bipartitePhase (Real.cos φ) s • bipartiteTau A B a b (Real.cos φ) s := by
  have hcos0 : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩
  have hcos1 : Real.cos φ < 1 := by
    have hsinpos : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    by_contra hle
    have hc : 1 ≤ Real.cos φ := le_of_not_gt hle
    have hsq := Real.sin_sq_add_cos_sq φ
    nlinarith [sq_nonneg (Real.sin φ), sq_nonneg (Real.cos φ)]
  intro s
  exact ⟨(bipartite_normalized_tau_pair H I J A B a b (Real.cos φ) hA hB hcos0 hcos1
      hn hab hba s).1,
    (bipartite_normalized_tau_pair H I J A B a b (Real.cos φ) hA hB hcos0 hcos1
      hn hab hba s).2.1⟩

theorem inner_eq_zero_of_distinct_unit_eigen
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (hT : ∀ x y : E, inner ℂ (T x) (T y) = inner ℂ x y)
    {ψ φ : E} {lam mu : ℂ} (hlam : ‖lam‖ = 1) (_hmu : ‖mu‖ = 1) (hmulam : mu ≠ lam)
    (hψ : T ψ = lam • ψ) (hφ : T φ = mu • φ) :
    inner ℂ ψ φ = 0 := by
  have h := hT ψ φ
  rw [hψ, hφ, inner_smul_left, inner_smul_right] at h
  have hlamnorm : lam * (starRingEnd ℂ) lam = 1 := by
    have hm := Complex.mul_conj lam
    rw [Complex.normSq_eq_norm_sq, hlam] at hm
    norm_num at hm
    exact hm
  have hfac : (starRingEnd ℂ) lam * mu - 1 ≠ 0 := by
    intro hc
    have h1 : (starRingEnd ℂ) lam * mu = 1 := sub_eq_zero.mp hc
    have hmu_eq : mu = lam := by
      calc mu = (lam * (starRingEnd ℂ) lam) * mu := by rw [hlamnorm, one_mul]
        _ = lam * ((starRingEnd ℂ) lam * mu) := by ring
        _ = lam := by rw [h1, mul_one]
    exact hmulam hmu_eq
  have hzero : ((starRingEnd ℂ) lam * mu - 1) * inner ℂ ψ φ = 0 := by
    rw [sub_mul, one_mul, mul_assoc ((starRingEnd ℂ) lam) mu (inner ℂ ψ φ), h, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hfac

theorem source_eq16_zero_overlap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (u ψ0 : E) (ψp ψm : Fin m → E) (c0 : ℂ) (cj : Fin m → ℂ)
    (hu0 : inner ℂ u ψ0 = 0) (hup : ∀ j, inner ℂ u (ψp j) = 0)
    (hum : ∀ j, inner ℂ u (ψm j) = 0) :
    inner ℂ u (c0 • ψ0 + ∑ j, (cj j / (Real.sqrt 2 : ℂ)) • (ψp j + ψm j)) = 0 := by
  rw [inner_add_right, inner_smul_right, inner_sum, hu0, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [inner_smul_right, inner_add_right, hup j, hum j, add_zero, mul_zero]

theorem source_eq16_zero_overlap_of_walk
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (T : E →L[ℂ] E) (hT : ∀ x y : E, inner ℂ (T x) (T y) = inner ℂ x y)
    (u ψ0 : E) (ψp ψm : Fin m → E) (c0 : ℂ) (cj : Fin m → ℂ)
    {lam mu : ℂ} (ηp ηm : Fin m → ℂ)
    (hlam : ‖lam‖ = 1) (hmu : ‖mu‖ = 1) (hηp : ∀ j, ‖ηp j‖ = 1) (hηm : ∀ j, ‖ηm j‖ = 1)
    (hmulam : mu ≠ lam) (hmηp : ∀ j, mu ≠ ηp j) (hmηm : ∀ j, mu ≠ ηm j)
    (hu : T u = mu • u) (hψ0 : T ψ0 = lam • ψ0)
    (hψp : ∀ j, T (ψp j) = ηp j • ψp j) (hψm : ∀ j, T (ψm j) = ηm j • ψm j) :
    inner ℂ u (c0 • ψ0 + ∑ j, (cj j / (Real.sqrt 2 : ℂ)) • (ψp j + ψm j)) = 0 := by
  apply source_eq16_zero_overlap
  · exact inner_eq_zero_of_distinct_unit_eigen T hT hmu hlam hmulam.symm hu hψ0
  · intro j
    exact inner_eq_zero_of_distinct_unit_eigen T hT hmu (hηp j) (hmηp j).symm hu (hψp j)
  · intro j
    exact inner_eq_zero_of_distinct_unit_eigen T hT hmu (hηm j) (hmηm j).symm hu (hψm j)

end Qatlib.Papers.QAnnealing07.MainResults.WalkSpectrum
