/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm
public import Qatlib.Concepts.GibbsSource.TraceBounds.ProbabilityClock

@[expose] public section


/-! # Actual three-projector probability-clock trace cap

The original six physical Pauli proposals are retained. Their Gaussian thermal
left and right factors are identified with complete spectral multipliers,
whose Hermitian paired-frequency contraction bounds the actual parent trace
by sixteen. Centering the full complex matrix-unit frame removes the genuine
Gibbs line and gives a positive-mass trial with quotient at most sixteen
fifteenths for every probability clock.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SourceForms
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Qatlib.Concepts.GibbsSource.TraceBounds
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelTraceCap

open ThreeLevelCluster ThreeLevelInvariant
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- The actual left thermal factor from the original source model. -/
def thermalLeft (σ : Perm) (E : Fin 3 → ℝ) (A : Operator 4) : Operator 4 :=
  population σ (fun i => quarterAmplitude (E i)) * spectralFilter σ (gaussianWeights E) A *
    population σ (fun i => (quarterAmplitude (E i))⁻¹)

/-- The actual right thermal factor uses the opposite signed multiplier. -/
def thermalRight (σ : Perm) (E : Fin 3 → ℝ) (A : Operator 4) : Operator 4 :=
  population σ (fun i => (quarterAmplitude (E i))⁻¹) * spectralFilter σ (gaussianWeights E) A *
    population σ (fun i => quarterAmplitude (E i))

/-- The left factor has exactly the signed Gaussian gain on each original spectral block. -/
theorem thermalLeft_eq_multiplier (σ : Perm) (E : Fin 3 → ℝ) (A : Operator 4) :
    thermalLeft σ E A =
      spectralMultiplier (spectralProjectors σ)
        (fun i j => (gaussianGain (-(E i-E j)) : ℂ)) A := by
  unfold thermalLeft
  rw [population_filter_population]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (Real.exp (-E i / 4) : ℂ) * (Real.exp (-(E i-E j)^2/8) : ℂ) *
    (Real.exp (-E j / 4) : ℂ)⁻¹ = (Real.exp (-(-(E i-E j))^2/8+(-(E i-E j))/4) : ℂ)
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The right factor has the opposite gain on every original spectral block. -/
theorem thermalRight_eq_multiplier (σ : Perm) (E : Fin 3 → ℝ) (A : Operator 4) :
    thermalRight σ E A =
      spectralMultiplier (spectralProjectors σ)
        (fun i j => (gaussianGain (E i-E j) : ℂ)) A := by
  unfold thermalRight
  rw [population_filter_population]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change (Real.exp (-E i / 4) : ℂ)⁻¹ * (Real.exp (-(E i-E j)^2/8) : ℂ) *
    (Real.exp (-E j / 4) : ℂ) = (Real.exp (-(E i-E j)^2/8+(E i-E j)/4) : ℂ)
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The original six Pauli proposals are Hermitian in their original four-dimensional carrier. -/
theorem literal_source_isHermitian (k : Fin 6) : (ThreeLevelWordDual.source k).IsHermitian := by
  change (ThreeLevelWordDual.source k)ᴴ = ThreeLevelWordDual.source k
  apply ExchangeCell.liftAlg.injective
  rw [← ExchangeCell.liftAlg_star, ← ThreeLevelWordDual.original_source]
  exact (fullPauliFamily_isHermitian 2 _).eq

/-- Every original Pauli proposal has squared Hilbert--Schmidt mass four. -/
theorem literal_source_hsSquare (k : Fin 6) :
    (hsInner (ThreeLevelWordDual.source k) (ThreeLevelWordDual.source k)).re = 4 := by
  change (hsPair (ThreeLevelWordDual.source k) (ThreeLevelWordDual.source k)).re = 4
  rw [← hsPair_lift, ← ThreeLevelWordDual.original_source,
    (fullPauliFamily_isHermitian 2 _).eq, localPauliMatrix_self_mul]
  norm_num [Matrix.trace, Matrix.diag_apply, fullPauliDim]

/-- The actual Gaussian left factor contracts each Hermitian proposal. -/
theorem thermalLeft_hsSquare_le (σ : Perm) (E : Fin 3 → ℝ)
    (A : Operator 4) (hA : A.IsHermitian) :
    (hsInner (thermalLeft σ E A) (thermalLeft σ E A)).re ≤ (hsInner A A).re := by
  rw [thermalLeft_eq_multiplier]
  simpa only [neg_one_mul] using spectralMultiplier_gaussianGain_hsSquare_le
    (spectralProjectors σ) (fun i => spectralProjectors_adjoint σ i)
    (spectralProjectors_mul σ) (spectralProjectors_sum σ) E (-1) A hA

/-- The opposite Gaussian right factor has the same Hermitian contraction. -/
theorem thermalRight_hsSquare_le (σ : Perm) (E : Fin 3 → ℝ)
    (A : Operator 4) (hA : A.IsHermitian) :
    (hsInner (thermalRight σ E A) (thermalRight σ E A)).re ≤ (hsInner A A).re := by
  rw [thermalRight_eq_multiplier]
  simpa only [one_mul] using spectralMultiplier_gaussianGain_hsSquare_le
    (spectralProjectors σ) (fun i => spectralProjectors_adjoint σ i)
    (spectralProjectors_mul σ) (spectralProjectors_sum σ) E 1 A hA

/-- Both thermal factors preserve exactly the trace of their original proposal. -/
theorem thermal_factor_traces (σ : Perm) (E : Fin 3 → ℝ) (A : Operator 4) :
    Matrix.trace (thermalLeft σ E A) = Matrix.trace A ∧
      Matrix.trace (thermalRight σ E A) = Matrix.trace A := by
  constructor
  · rw [thermalLeft_eq_multiplier]
    apply trace_spectralMultiplier _ (spectralProjectors_mul σ) (spectralProjectors_sum σ)
    intro i
    simp [gaussianGain]
  · rw [thermalRight_eq_multiplier]
    apply trace_spectralMultiplier _ (spectralProjectors_mul σ) (spectralProjectors_sum σ)
    intro i
    simp [gaussianGain]

/-- The complete raw gradient is the actual left-minus-right thermal multiplier. -/
theorem actualGradient_eq_gradientMap (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) :
    actualGradient σ E k X =
      gradientMap (thermalLeft σ E (ThreeLevelWordDual.source k))
        (thermalRight σ E (ThreeLevelWordDual.source k)) X := rfl

/-- The original one-twelfth source mass and all six full Gram operators. -/
def plainParent (σ : Perm) (E : Fin 3 → ℝ) : Operator 4 →ₗ[ℂ] Operator 4 :=
  (((1/12 : ℝ) : ℂ)) • ∑ k : Fin 6,
    gradientGram (thermalLeft σ E (ThreeLevelWordDual.source k))
      (thermalRight σ E (ThreeLevelWordDual.source k))

/-- The full parent quadratic form is exactly the existing plain energy. -/
theorem plainParent_energy (σ : Perm) (S s : ℝ) (X : Operator 4) :
    (hsInner X (plainParent σ (lowEnergies S s) X)).re = plainEnergy σ S s X := by
  simp only [plainParent, LinearMap.smul_apply, LinearMap.sum_apply, hsInner_smul_right,
    hsInner_sum_right, gradientGram_energy, ← actualGradient_eq_gradientMap,
    ofReal_mul_re, Complex.re_sum]
  rfl

/-- The complete original parent is self-adjoint. -/
theorem plainParent_selfAdjoint (σ : Perm) (E : Fin 3 → ℝ) :
    SourceSelfAdjoint (plainParent σ E) := by
  intro X Y
  simp only [plainParent, LinearMap.smul_apply, LinearMap.sum_apply,
    hsInner_smul_left, hsInner_smul_right, star_ofReal, hsInner_sum_left, hsInner_sum_right]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact gradientGram_selfAdjoint _ _ X Y

/-- The complete original parent is positive on the full complex operator space. -/
theorem plainParent_nonneg (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    0 ≤ (hsInner X (plainParent σ E X)).re := by
  simp only [plainParent, LinearMap.smul_apply, LinearMap.sum_apply, hsInner_smul_right,
    hsInner_sum_right, ofReal_mul_re, Complex.re_sum]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => gradientGram_nonneg _ _ _)

/-- The internally derived full-space parent trace is at most sixteen for every spectrum and ordering. -/
theorem plainParent_trace_le_sixteen (σ : Perm) (E : Fin 3 → ℝ) :
    sourceTrace (plainParent σ E) ≤ 16 := by
  rw [plainParent, sourceTrace_real_smul, sourceTrace_sum]
  have hk (k : Fin 6) :
      sourceTrace (gradientGram (thermalLeft σ E (ThreeLevelWordDual.source k))
        (thermalRight σ E (ThreeLevelWordDual.source k))) ≤ 32 := by
    have ht := thermal_factor_traces σ E (ThreeLevelWordDual.source k)
    have hb := gradientGram_trace_le _ _ _ ht.1 ht.2
      (thermalLeft_hsSquare_le σ E _ (literal_source_isHermitian k))
      (thermalRight_hsSquare_le σ E _ (literal_source_isHermitian k))
    norm_num only [literal_source_hsSquare, Nat.cast_ofNat] at hb
    exact hb
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)
  norm_num at h ⊢
  linarith


/-- The full probability-clock trace equals the plain parent trace before any bound is applied. -/
theorem clockEnergy_trace_eq (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∑ i, ∑ j, clockEnergy σ β S s μ (matUnit i j 1)) =
      sourceTrace (plainParent σ (lowEnergies S s)) := by
  have hcont (X : Operator 4) : Continuous (fun t =>
      (hsInner (fullUnitaryConj (timeUnitary σ (physicalEnergies β S s) t) X)
        (plainParent σ (lowEnergies S s)
          (fullUnitaryConj (timeUnitary σ (physicalEnergies β S s) t) X))).re) := by
    simpa only [plainParent_energy, timeConjugation, fullUnitaryConj] using
      continuous_time_plainEnergy σ S s (physicalEnergies β S s) X
  have ht := sum_probabilityClockEnergy_matrixUnits (plainParent σ (lowEnergies S s))
    (plainParent_selfAdjoint σ _) (plainParent_nonneg σ _)
    (fun t => timeUnitary σ (physicalEnergies β S s) t)
    (timeUnitary_star_mul σ _) μ hcont
  simpa only [plainParent_energy, clockEnergy, timeConjugation, fullUnitaryConj] using ht

/-- The real sixteen cap is proved for every probability measure and all six original physical sources. -/
theorem threeLevel_clockEnergy_trace_le_sixteen (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∑ i, ∑ j, clockEnergy σ β S s μ (matUnit i j 1)) ≤ 16 := by
  rw [clockEnergy_trace_eq]
  exact plainParent_trace_le_sixteen σ _

/-- Subtracting the actual Gibbs component leaves the full averaged source energy unchanged. -/
theorem clockEnergy_center (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) (X : Operator 4) :
    clockEnergy σ β S s μ (center (gibbsRoot σ (lowEnergies S s)) X) =
      clockEnergy σ β S s μ X := by
  unfold center
  rw [sourceCenteredProjection_apply]
  simp only [LinearMap.id_apply]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [timeConjugation_sub, timeConjugation_smul]
  rw [show timeConjugation σ (physicalEnergies β S s) t (gibbsRoot σ (lowEnergies S s)) =
      gibbsRoot σ (lowEnergies S s) by
    unfold gibbsRoot
    exact timeConjugation_population σ _ t _]
  simp only [plainEnergy, actualGradient_center]

/-- A genuine full complex Gibbs-orthogonal trial has quotient at most sixteen fifteenths.
For nonzero beta this is the original physical parameterization. At beta zero,
the statement concerns the finite division-totalized clock definition only. -/
theorem threeLevel_clockEnergy_trial (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ X : Operator 4, hsInner (gibbsRoot σ (lowEnergies S s)) X = 0 ∧
      0 < hsSquare X ∧ clockEnergy σ β S s μ X ≤ (16/15 : ℝ) * hsSquare X := by
  have hG : 0 < (hsInner (gibbsRoot σ (lowEnergies S s))
      (gibbsRoot σ (lowEnergies S s))).re := by
    change 0 < (hsPair (gibbsRoot σ (lowEnergies S s))
      (gibbsRoot σ (lowEnergies S s))).re
    rw [hsPair_gibbs]
    exact gibbsMass_pos σ _
  have hn (X : Operator 4) : 0 ≤ clockEnergy σ β S s μ X :=
    integral_nonneg fun t => plainEnergy_nonneg σ S s _
  obtain ⟨X, ho, hp, hb⟩ := exists_centered_trial (by norm_num : 1 < 4)
    (gibbsRoot σ (lowEnergies S s)) hG (clockEnergy σ β S s μ) 16 hn
    (clockEnergy_center σ β S s μ) (threeLevel_clockEnergy_trace_le_sixteen σ β S s μ)
  exact ⟨X, ho, hp, by norm_num [hsSquare] at hb ⊢; exact hb⟩

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelTraceCap
