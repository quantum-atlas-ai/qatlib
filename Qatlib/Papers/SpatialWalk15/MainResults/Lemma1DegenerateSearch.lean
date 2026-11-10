/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.RankOneSpectralSearch
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.RankOneSpectralSearch.RankOneSpectralSearch
open scoped Classical BigOperators

namespace Qatlib.Papers.SpatialWalk15.MainResults.Lemma1DegenerateSearch

variable {I : Type} [Fintype I] [DecidableEq I]

theorem exp_neg_half_pi_mul_I : Complex.exp ((-(Real.pi / 2) : ℝ) * Complex.I) = -Complex.I := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  push_cast
  ring

theorem exp_half_pi_mul_I : Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) = Complex.I := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast
  ring

theorem resonant_phase_add (ε : ℝ) (hε0 : 0 < ε) :
    ((-Complex.I*((Real.pi / (2 * ε) : ℝ) : ℂ))*((1+ε : ℝ) : ℂ))
      = (-Complex.I*((Real.pi / (2 * ε) : ℝ) : ℂ)) + (-(Complex.I*((Real.pi / 2 : ℝ) : ℂ))) := by
  have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
  push_cast
  have hae : (↑Real.pi / (2 * ↑ε)) * ↑ε = ↑Real.pi / (2 : ℂ) := by
    field_simp
  calc -Complex.I * (↑Real.pi / (2 * ↑ε)) * (1 + ↑ε)
      = -Complex.I * (↑Real.pi / (2 * ↑ε)) + -Complex.I * ((↑Real.pi / (2 * ↑ε)) * ↑ε) := by ring
    _ = -Complex.I * (↑Real.pi / (2 * ↑ε)) + -(Complex.I * (↑Real.pi / 2)) := by
        rw [hae]; ring

theorem resonant_phase_sub (ε : ℝ) (hε0 : 0 < ε) :
    ((-Complex.I*((Real.pi / (2 * ε) : ℝ) : ℂ))*((1-ε : ℝ) : ℂ))
      = (-Complex.I*((Real.pi / (2 * ε) : ℝ) : ℂ)) + (Complex.I*((Real.pi / 2 : ℝ) : ℂ)) := by
  have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
  push_cast
  have hae : (↑Real.pi / (2 * ↑ε)) * ↑ε = ↑Real.pi / (2 : ℂ) := by
    field_simp
  calc -Complex.I * (↑Real.pi / (2 * ↑ε)) * (1 - ↑ε)
      = -Complex.I * (↑Real.pi / (2 * ↑ε)) + Complex.I * ((↑Real.pi / (2 * ↑ε)) * ↑ε) := by ring
    _ = -Complex.I * (↑Real.pi / (2 * ↑ε)) + Complex.I * (↑Real.pi / 2) := by rw [hae]

omit [DecidableEq I] in

theorem degenerate_search_mulVec_add (s w : QState I) (ε : ℝ)
    (hs : Normalized s) (hw : Normalized w) (hε : Inner w s = (ε : ℂ)) :
    (rankOneProjector s + rankOneProjector w) *ᵥ (s + w) = ((1 + ε : ℝ) : ℂ) • (s + w) := by
  have hε' : Inner s w = (ε : ℂ) := by rw [← inner_conj_state, hε]; simp
  have hss : Inner s s = 1 := (normalized_iff_inner_self s).1 hs
  have hww : Inner w w = 1 := (normalized_iff_inner_self w).1 hw
  rw [Matrix.add_mulVec, Matrix.mulVec_add, Matrix.mulVec_add, rankOneProjector_mulVec,
    rankOneProjector_mulVec, rankOneProjector_mulVec, rankOneProjector_mulVec,
    hss, hww, hε, hε']
  ext i
  simp only [Pi.add_apply, Pi.smul_apply]
  simp
  ring

omit [DecidableEq I] in

theorem degenerate_search_mulVec_sub (s w : QState I) (ε : ℝ)
    (hs : Normalized s) (hw : Normalized w) (hε : Inner w s = (ε : ℂ)) :
    (rankOneProjector s + rankOneProjector w) *ᵥ (s - w) = ((1 - ε : ℝ) : ℂ) • (s - w) := by
  have hε' : Inner s w = (ε : ℂ) := by rw [← inner_conj_state, hε]; simp
  have hss : Inner s s = 1 := (normalized_iff_inner_self s).1 hs
  have hww : Inner w w = 1 := (normalized_iff_inner_self w).1 hw
  rw [Matrix.add_mulVec, Matrix.mulVec_sub, Matrix.mulVec_sub, rankOneProjector_mulVec,
    rankOneProjector_mulVec, rankOneProjector_mulVec, rankOneProjector_mulVec,
    hss, hww, hε, hε']
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply]
  simp
  ring

theorem degenerate_search_exact_amplitude (s w : QState I) (ε : ℝ)
    (hs : Normalized s) (hw : Normalized w) (hε : Inner w s = (ε : ℂ))
    (hε0 : 0 < ε) :
    ‖Inner w (HamiltonianEvolution (rankOneProjector s + rankOneProjector w)
      (Real.pi / (2 * ε)) *ᵥ s)‖ = 1 := by
  set H : Matrix I I ℂ := rankOneProjector s + rankOneProjector w
  set t : ℝ := Real.pi / (2 * ε)
  have hww : Inner w w = 1 := (normalized_iff_inner_self w).1 hw
  have hplus : H *ᵥ (s + w) = ((1 + ε : ℝ) : ℂ) • (s + w) :=
    degenerate_search_mulVec_add s w ε hs hw hε
  have hminus : H *ᵥ (s - w) = ((1 - ε : ℝ) : ℂ) • (s - w) :=
    degenerate_search_mulVec_sub s w ε hs hw hε
  have hsplit : s = (2 : ℂ)⁻¹ • (s + w) + (2 : ℂ)⁻¹ • (s - w) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    simp
    ring
  have hev : HamiltonianEvolution H t *ᵥ s =
      (2 : ℂ)⁻¹ • (Complex.exp ((-Complex.I*(t : ℂ))*((1+ε : ℝ) : ℂ)) • (s + w))
      + (2 : ℂ)⁻¹ • (Complex.exp ((-Complex.I*(t : ℂ))*((1-ε : ℝ) : ℂ)) • (s - w)) := by
    conv_lhs => rw [hsplit]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hamiltonianEvolution_eigenvector H (s + w) (1+ε) t hplus,
      hamiltonianEvolution_eigenvector H (s - w) (1-ε) t hminus]
  have hphase_pos : Complex.exp ((-Complex.I*(t : ℂ))*((1+ε : ℝ) : ℂ)) =
      Complex.exp (-Complex.I*(t : ℂ)) * (-Complex.I) := by
    have harg : (-Complex.I*(t : ℂ))*((1+ε : ℝ) : ℂ) =
        (-Complex.I*(t : ℂ)) + (-(Complex.I*((Real.pi / 2 : ℝ) : ℂ))) := by
      rw [show t = Real.pi / (2 * ε) from rfl]
      exact resonant_phase_add ε hε0
    have hhalf : Complex.exp (-(Complex.I*((Real.pi / 2 : ℝ) : ℂ))) = -Complex.I := by
      rw [show -(Complex.I*((Real.pi / 2 : ℝ) : ℂ)) = (-(Real.pi / 2) : ℝ) * Complex.I by
        push_cast; ring]
      exact exp_neg_half_pi_mul_I
    rw [harg, Complex.exp_add, hhalf]
  have hphase_neg : Complex.exp ((-Complex.I*(t : ℂ))*((1-ε : ℝ) : ℂ)) =
      Complex.exp (-Complex.I*(t : ℂ)) * Complex.I := by
    have harg : (-Complex.I*(t : ℂ))*((1-ε : ℝ) : ℂ) =
        (-Complex.I*(t : ℂ)) + (Complex.I*((Real.pi / 2 : ℝ) : ℂ)) := by
      rw [show t = Real.pi / (2 * ε) from rfl]
      exact resonant_phase_sub ε hε0
    have hhalf : Complex.exp (Complex.I*((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
      rw [show Complex.I*((Real.pi / 2 : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by ring]
      exact exp_half_pi_mul_I
    rw [harg, Complex.exp_add, hhalf]
  have hamp : Inner w (HamiltonianEvolution H t *ᵥ s) =
      (2 : ℂ)⁻¹ * (Complex.exp ((-Complex.I*(t : ℂ))*((1+ε : ℝ) : ℂ)) * ((ε : ℂ) + 1))
      + (2 : ℂ)⁻¹ * (Complex.exp ((-Complex.I*(t : ℂ))*((1-ε : ℝ) : ℂ)) * ((ε : ℂ) - 1)) := by
    rw [hev, inner_add_state, inner_smul_state, inner_smul_state, inner_smul_state,
      inner_smul_state, inner_add_state, inner_sub_state, hε, hww]
  rw [hamp, hphase_pos, hphase_neg]
  have hcollapse : (2 : ℂ)⁻¹ *
        (Complex.exp (-Complex.I*(t : ℂ)) * (-Complex.I) * ((ε : ℂ) + 1))
      + (2 : ℂ)⁻¹ *
        (Complex.exp (-Complex.I*(t : ℂ)) * Complex.I * ((ε : ℂ) - 1))
      = -Complex.I * Complex.exp (-Complex.I*(t : ℂ)) := by
    ring
  rw [hcollapse, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [show -Complex.I*(t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem lemma1_degenerate_calibrated_search (s w : QState I) (ε : ℝ)
    (hs : Normalized s) (hw : Normalized w) (hε : Inner w s = (ε : ℂ))
    (hε0 : 0 < ε) :
    ∃ r : ℝ, -0 / (1 + 0) ≤ r ∧ r ≤ 0 / (1 - 0) ∧
      ∃ t : ℝ, |t| ≤ 4 / (ε * Real.sqrt (spectralGapParam 0)) ∧
        spectralGapParam 0 ≤ ‖Inner w ((HamiltonianEvolution
          ((1 + r) • rankOneProjector s - r • (1 : Matrix I I ℂ) + rankOneProjector w) t) *ᵥ s)‖ ^ 2 := by
  have hgap : spectralGapParam 0 = 1 := by norm_num [spectralGapParam]
  have hexact := degenerate_search_exact_amplitude s w ε hs hw hε hε0
  refine ⟨0, by norm_num, by norm_num, Real.pi / (2 * ε), ?_, ?_⟩
  · rw [hgap, Real.sqrt_one, mul_one, abs_of_pos (by positivity)]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε) hε0]
    nlinarith only [Real.pi_le_four, hε0.le]
  · rw [hgap]
    simp only [zero_smul, one_smul, sub_zero, add_zero]
    rw [hexact]
    norm_num

end Qatlib.Papers.SpatialWalk15.MainResults.Lemma1DegenerateSearch
