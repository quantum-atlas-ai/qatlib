/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CryptoDisting99.Equivalence.Defs
import Qatlib.Concepts.MixedFidelity.FidelityMetric.ChannelHelpers.FinitePOVMTraceDistance
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
import Mathlib.Analysis.Matrix.Spectrum

/-!
# A two-outcome measurement attaining trace distance

The operator `spectralPlus` selects positive entries of a real diagonal list in a supplied
matrix basis, and `helstromPOVM` uses it and its complement as two measurement effects. The
theorem `helstrom_recordLaw_tv` proves attainability of trace distance by such a finite
measurement, supporting Proposition 1 of [FuchsVanDeGraaf1999].

## Main statements

* `helstrom_record_zero` and `helstrom_record_one`: outcome probability formulas.
* `helstrom_recordLaw_tv`: a two-outcome POVM attains trace distance as classical Kolmogorov
  distance.

## References

* [Fuchs and van de Graaf, 1999][FuchsVanDeGraaf1999]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CryptoDisting99.Equivalence

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence
open Qatlib.Concepts.MixedFidelity.FidelityMetric
open Matrix
open scoped BigOperators
set_option warningAsError false

/-- A finite real list has a common positive lower bound, at most one, on the absolute values of
all its nonzero entries. -/
lemma exists_gamma_le_one {d : ℕ} (x : Fin d → ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∀ j, x j ≠ 0 → γ ≤ |x j| := by
  classical
  by_cases hne : (Finset.univ.filter (fun j => x j ≠ 0)).Nonempty
  · let S' : Finset ℝ := (Finset.univ.filter (fun j => x j ≠ 0)).image (fun j => |x j|)
    have hS' : S'.Nonempty := hne.image _
    refine ⟨min 1 (S'.min' hS'), ?_, min_le_left _ _, fun j hj => ?_⟩
    · have hpos : 0 < S'.min' hS' := by
        by_contra hle
        obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp (S'.min'_mem hS')
        rw [← hbe] at hle
        exact absurd (abs_pos.mpr (Finset.mem_filter.mp hb).2) hle
      exact lt_min_iff.mpr ⟨by norm_num, hpos⟩
    · exact min_le_iff.mpr (Or.inr (S'.min'_le _
        (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩)))
  · refine ⟨1, by norm_num, le_rfl, fun j hj => ?_⟩
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩) (fun hmem => hne ⟨j, hmem⟩)

/-- Defines `V` times the diagonal indicator of positive entries of `x` times `Vᴴ`. -/
noncomputable def spectralPlus {D : ℕ} (V : Operator D) (x : Fin D → ℝ) : Operator D :=
  V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ

/-- Expands `spectralPlus V x` as the conjugated diagonal indicator of the positive entries of
`x`. -/
lemma spectralPlus_eq {D : ℕ} (V : Operator D) (x : Fin D → ℝ) :
    spectralPlus V x = V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ :=
  rfl

/-- The operator `spectralPlus V x` equals its conjugate transpose. -/
lemma spectralPlus_conjTranspose {D : ℕ} (V : Operator D) (x : Fin D → ℝ) :
    (spectralPlus V x)ᴴ = spectralPlus V x := by
  unfold spectralPlus
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose]
  have he : (star (fun j : Fin D => if 0 < x j then (1 : ℂ) else 0)) =
      (fun j => if 0 < x j then (1 : ℂ) else 0) := by
    funext j; by_cases h : 0 < x j <;> simp [h]
  rw [he, Matrix.mul_assoc]

/-- If `Vᴴ * V = 1`, then `spectralPlus V x` is idempotent. -/
lemma spectralPlus_mul_self {D : ℕ} (V : Operator D) (x : Fin D → ℝ) (hV : Vᴴ * V = 1) :
    spectralPlus V x * spectralPlus V x = spectralPlus V x := by
  unfold spectralPlus
  have hd : Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) *
      Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) =
      Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : 0 < x j <;> simp [h]
  calc (V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ) *
        (V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ)
      = V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * (Vᴴ * V) *
          Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ := by
        simp only [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) *
          Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ := by
        rw [hV, Matrix.mul_one]
    _ = V * Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0) * Vᴴ := by
        rw [Matrix.mul_assoc V (Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0))
          (Matrix.diagonal (fun j => if 0 < x j then (1 : ℂ) else 0)), hd]

/-- The complement `1 - spectralPlus V x` equals its conjugate transpose. -/
lemma one_sub_spectralPlus_conjTranspose {D : ℕ} (V : Operator D) (x : Fin D → ℝ) :
    (1 - spectralPlus V x)ᴴ = 1 - spectralPlus V x := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, spectralPlus_conjTranspose]

/-- If `Vᴴ * V = 1`, the complement of `spectralPlus V x` is idempotent. -/
lemma one_sub_spectralPlus_mul_self {D : ℕ} (V : Operator D) (x : Fin D → ℝ)
    (hV : Vᴴ * V = 1) :
    (1 - spectralPlus V x) * (1 - spectralPlus V x) = 1 - spectralPlus V x := by
  have hsq := spectralPlus_mul_self V x hV
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hsq]
  abel

/-- For `Vᴴ * V = 1`, constructs the two-outcome POVM with effects `spectralPlus V x` and its
complement. -/
noncomputable def helstromPOVM {D : ℕ} (V : Operator D) (x : Fin D → ℝ)
    (hV : Vᴴ * V = 1) : FinitePOVM (Fin 2) D where
  effect := fun o => if o = 0 then spectralPlus V x else 1 - spectralPlus V x
  effect_sum := by
    rw [Fin.sum_univ_two]
    simp
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  factor := fun o => if o = 0 then spectralPlus V x else 1 - spectralPlus V x
  effect_eq_factor := by
    intro o
    by_cases ho : o = 0
    · simp only [ho, ↓reduceIte]
      rw [spectralPlus_conjTranspose, spectralPlus_mul_self V x hV]
      simp
    · simp only [ho, if_false]
      rw [one_sub_spectralPlus_conjTranspose, one_sub_spectralPlus_mul_self V x hV]
      simp

/-- The probability of outcome zero in `helstromPOVM` is the real part of the trace of
`spectralPlus V x * ρ`. -/
lemma helstrom_record_zero {D : ℕ} (V : Operator D) (x : Fin D → ℝ) (hV : Vᴴ * V = 1)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (povmRecordLaw (helstromPOVM V x hV) ρ hρ).prob 0 =
      (Matrix.trace (spectralPlus V x * ρ)).re := by
  rw [povmRecordLaw_prob]
  simp [helstromPOVM]

/-- The probability of outcome one in `helstromPOVM` is one minus the real part of the trace of
`spectralPlus V x * ρ`. -/
lemma helstrom_record_one {D : ℕ} (V : Operator D) (x : Fin D → ℝ) (hV : Vᴴ * V = 1)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) :
    (povmRecordLaw (helstromPOVM V x hV) ρ hρ).prob 1 =
      1 - (Matrix.trace (spectralPlus V x * ρ)).re := by
  rw [povmRecordLaw_prob]
  simp only [helstromPOVM, Fin.isValue, reduceIte, Fin.reduceEq]
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hρ.2, Complex.one_re]

/-- For two density operators, there exists a two-outcome POVM whose outcome laws have classical
Kolmogorov distance equal to their trace distance. This supplies the measurement attaining
the bound behind [Fuchs and van de Graaf, Proposition 1][FuchsVanDeGraaf1999]. -/
theorem helstrom_recordLaw_tv {D : ℕ} (ρ σ : Operator D)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    ∃ (E : FinitePOVM (Fin 2) D),
      classicalKolmogorov (povmRecordLaw E ρ hρ) (povmRecordLaw E σ hσ)
        = traceDistance ρ σ := by
  have hΔ : (ρ - σ).IsHermitian := by
    show (ρ - σ)ᴴ = ρ - σ
    rw [Matrix.conjTranspose_sub, hρ.1.1, hσ.1.1]
  let U := hΔ.eigenvectorUnitary
  let V : Operator D := U
  have hVmem : V ∈ Matrix.unitaryGroup (Fin D) ℂ := U.2
  have hV : Vᴴ * V = 1 := by
    have h := Unitary.coe_star_mul_self U
    simpa [V, Matrix.star_eq_conjTranspose] using! h
  have hspec : ρ - σ = V * Matrix.diagonal (fun j => (hΔ.eigenvalues j : ℂ)) * Vᴴ := by
    have h := hΔ.spectral_theorem
    simpa [V, Function.comp_def, Matrix.star_eq_conjTranspose] using! h
  obtain ⟨γ, hγ0, hγ1, hγgap⟩ := exists_gamma_le_one hΔ.eigenvalues
  have hH := Qatlib.Concepts.CopyEvolution.Discriminate.finiteCopyHelstromDiscrimination
    D 2 1 γ ρ σ V hΔ.eigenvalues (by norm_num) (by norm_num) hγ0 hγ1 hρ hσ hVmem hspec hγgap
  refine ⟨helstromPOVM V hΔ.eigenvalues hV, ?_⟩
  let Aplus : Operator D :=
    V * Matrix.diagonal (fun j => if 0 < hΔ.eigenvalues j then (1 : ℂ) else 0) * Vᴴ
  have hscore : ((Matrix.trace (Aplus * ρ)).re + (Matrix.trace ((1 - Aplus) * σ)).re) / 2 =
      1 / 2 + Matrix.traceNorm (ρ - σ) / 4 := hH.2.2.1
  have h0ρ : (povmRecordLaw (helstromPOVM V hΔ.eigenvalues hV) ρ hρ).prob 0 =
      (Matrix.trace (Aplus * ρ)).re := helstrom_record_zero V hΔ.eigenvalues hV ρ hρ
  have h0σ : (povmRecordLaw (helstromPOVM V hΔ.eigenvalues hV) σ hσ).prob 0 =
      (Matrix.trace (Aplus * σ)).re := helstrom_record_zero V hΔ.eigenvalues hV σ hσ
  have h1ρ : (povmRecordLaw (helstromPOVM V hΔ.eigenvalues hV) ρ hρ).prob 1 =
      1 - (Matrix.trace (Aplus * ρ)).re := helstrom_record_one V hΔ.eigenvalues hV ρ hρ
  have h1σ : (povmRecordLaw (helstromPOVM V hΔ.eigenvalues hV) σ hσ).prob 1 =
      1 - (Matrix.trace (Aplus * σ)).re := helstrom_record_one V hΔ.eigenvalues hV σ hσ
  set c : ℝ := (Matrix.trace (Aplus * (ρ - σ))).re with hc
  have hc_eq : c = (Matrix.trace (Aplus * ρ)).re - (Matrix.trace (Aplus * σ)).re := by
    rw [hc, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have h1A : (Matrix.trace ((1 - Aplus) * σ)).re = 1 - (Matrix.trace (Aplus * σ)).re := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, hσ.2, Complex.one_re]
  have hscore' : (1/2 : ℝ) + c/2 = 1/2 + Matrix.traceNorm (ρ - σ) / 4 := by
    rw [hc_eq]
    rw [h1A] at hscore
    linarith
  have hcval : c = Matrix.traceNorm (ρ - σ) / 2 := by linarith
  have hc_nonneg : 0 ≤ c := by
    rw [hcval]
    exact div_nonneg (Matrix.traceNorm_nonneg _) (by norm_num)
  unfold classicalKolmogorov tv
  rw [Fin.sum_univ_two, h0ρ, h0σ, h1ρ, h1σ]
  have hdiff0 : (Matrix.trace (Aplus * ρ)).re - (Matrix.trace (Aplus * σ)).re = c := hc_eq.symm
  have hdiff1 : (1 - (Matrix.trace (Aplus * ρ)).re) - (1 - (Matrix.trace (Aplus * σ)).re) = -c := by
    linarith
  rw [hdiff0, hdiff1]
  unfold traceDistance
  rw [abs_of_nonneg hc_nonneg, abs_neg, abs_of_nonneg hc_nonneg, hcval]
  ring

end Qatlib.Papers.CryptoDisting99.Equivalence
