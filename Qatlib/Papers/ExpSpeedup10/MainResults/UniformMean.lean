/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.ProbabilityCore.Concentration.SignMoments
public import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceCore

@[expose] public section


/-! # The independent-sign half of source Proposition II.1

The source is arXiv:1010.3654v2 (16 April 2013), Eq. (7). This file uses
its actual normalized sign vectors and acceptance probability. It makes no
claim about the correlated Gaussian expectation of Eq. (8).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Classical BigOperators Matrix
open Qatlib.Foundations.ProbabilityCore.Concentration.SignMoments
open Qatlib.Papers.ExpSpeedup10.MainResults.Model

namespace Qatlib.Papers.ExpSpeedup10.MainResults.UniformMean

/-- Raw matrix amplitude before the source's two square-root normalizations. -/
def rawAmplitude {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) : ℂ :=
  ∑ x, rSign (g x) * (∑ y, U x y * rSign (f y))

/-- Both source square-root factors combine to the actual dimension. -/
theorem sourceAmplitude {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) :
    (∑ x : Fin N, star (sourceSignVec g x) *
      (∑ y : Fin N, U x y * sourceSignVec f y)) =
        rawAmplitude U f g / (N : ℂ) := by
  have hs : (Real.sqrt (N : ℝ) : ℂ) * (Real.sqrt (N : ℝ) : ℂ) = (N : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  change (∑ x, star (rSign (g x) / (Real.sqrt (N : ℝ) : ℂ)) *
    (∑ y, U x y * (rSign (f y) / (Real.sqrt (N : ℝ) : ℂ)))) = _
  simp only [star_div₀, signStar, Complex.star_def, Complex.conj_ofReal]
  simp only [← mul_div_assoc, ← Finset.sum_div, div_mul_eq_mul_div₀, div_div, hs]
  rfl

/-- The literal source acceptance equals the raw squared norm divided by N². -/
theorem acceptanceRaw {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) :
    sourceAcceptance U f g = ‖rawAmplitude U f g‖ ^ 2 / (N : ℝ) ^ 2 := by
  rw [sourceAcceptance, sourceAmplitude, norm_div, div_pow]
  simp

/-- The exact independent-sign mean of any square matrix is its entry energy/N². -/
theorem meanFormula {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    sourceUniformMean U = (∑ x, ∑ y, ‖U x y‖ ^ 2) / (N : ℝ) ^ 2 := by
  have hc : (Fintype.card (Fin N → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hm := matrixMoment U
  change (∑ f : Fin N → Bool, ∑ g : Fin N → Bool,
    ‖rawAmplitude U f g‖ ^ 2) = _ at hm
  rw [sourceUniformMean]
  simp_rw [acceptanceRaw, ← Finset.sum_div]
  rw [hm]
  field_simp [hc]

/-- Row unitarity determines the actual row's sum of squared entry magnitudes. -/
theorem rowEnergy {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * Uᴴ = 1) (x : Fin N) : (∑ y, ‖U x y‖ ^ 2) = 1 := by
  have h := congrArg (fun A : Matrix (Fin N) (Fin N) ℂ => A x x) hU
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    ite_true] at h
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_one]
  simp_rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simpa only [mul_comm, starRingEnd_apply] using h

/-- Source Proposition II.1(i), with the original unitary and positive dimension. -/
theorem uniformMean {N : ℕ} (hN : 0 < N) (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : U * Uᴴ = 1) : sourceUniformMean U = (N : ℝ)⁻¹ := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [meanFormula]
  simp_rw [rowEnergy U hU]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  field_simp

end Qatlib.Papers.ExpSpeedup10.MainResults.UniformMean
