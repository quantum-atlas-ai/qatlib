/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelTraceCap
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceRayleighMinimum
public import Qatlib.Concepts.GibbsSource.SpectralGeom.ParentSuperoperator
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum

@[expose] public section


/-!
# Exact Rayleigh infima for the three-level probability-clock forms

The gap is defined as the infimum of the original normalized energy on the
complete complex Hilbert--Schmidt unit sphere orthogonal to the actual Gibbs
line. A positive actual scaled-stack certificate makes the attained plain
minimum positive; probability averaging preserves that minimum as a lower
bound. This module does not assume an averaged parent matrix or its spectrum.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Concepts.GibbsSource.SourceForms
open Qatlib.Concepts.GibbsSource.SpectralGeom

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighGap
open ThreeLevelCluster ThreeLevelInvariant

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def unitInputs (σ : Perm) (S s : ℝ) : Set (Operator 4) :=
  {X | hsSquare X = 1 ∧ hsInner (gibbsRoot σ (lowEnergies S s)) X = 0}

def plainGap (σ : Perm) (S s : ℝ) : ℝ :=
  sInf (plainEnergy σ S s '' unitInputs σ S s)

def clockGap (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) : ℝ :=
  sInf (clockEnergy σ β S s μ '' unitInputs σ S s)

def unvec (z : FullCoord 4 → ℂ) : Operator 4 := fun i j => z (i,j)

/-- Full Vec unvec for the stated finite source data. -/
theorem fullVec_unvec (z : FullCoord 4 → ℂ) : fullVec (unvec z) = z := rfl

/-- Unvec full Vec for the stated finite source data. -/
theorem unvec_fullVec (X : Operator 4) : unvec (fullVec X) = X := rfl

/-- Unit Inputs eq image for the stated finite source data. -/
theorem unitInputs_eq_image (σ : Perm) (S s : ℝ) :
    unitInputs σ S s =
      unvec '' fullUnitOrthogonal (fullVec (gibbsRoot σ (lowEnergies S s))) := by
  ext X
  constructor
  · intro hX
    refine ⟨fullVec X, ?_, rfl⟩
    simpa only [fullUnitOrthogonal, Set.mem_ofPred_eq, fullNormSq, fullVec_starDot,
      unitInputs, hsSquare] using hX
  · rintro ⟨z, hz, rfl⟩
    change fullNormSq (fullVec (unvec z)) = 1 ∧
      star (fullVec (gibbsRoot σ (lowEnergies S s))) ⬝ᵥ fullVec (unvec z) = 0 at hz
    simpa only [fullNormSq, fullVec_starDot, unitInputs, Set.mem_ofPred_eq, hsSquare] using hz

/-- Unit Inputs is Compact for the stated finite source data. -/
theorem unitInputs_isCompact (σ : Perm) (S s : ℝ) :
    IsCompact (unitInputs σ S s) := by
  rw [unitInputs_eq_image]
  apply (fullUnitOrthogonal_isCompact _).image
  unfold unvec
  fun_prop

/-- Projector entry zero for the stated finite source data. -/
theorem projector_entry_zero (j : Fin 3) :
    (ThreeLevelWordDual.projectors j) 0 1 = 0 := by
  fin_cases j <;>
    norm_num [ThreeLevelWordDual.projectors, ThreeLevelWordDual.pZero,
      ThreeLevelWordDual.pOne, ThreeLevelWordDual.pTwo, ThreeLevelWordDual.psi]

/-- Gibbs Root entry zero for the stated finite source data. -/
theorem gibbsRoot_entry_zero (σ : Perm) (E : Fin 3 → ℝ) :
    gibbsRoot σ E 0 1 = 0 := by
  simp [gibbsRoot, population, spectralProjectors, Matrix.sum_apply,
    Matrix.smul_apply, projector_entry_zero]

/-- Unit Inputs nonempty for the stated finite source data. -/
theorem unitInputs_nonempty (σ : Perm) (S s : ℝ) :
    (unitInputs σ S s).Nonempty := by
  refine ⟨matUnit 0 1 1, ?_, ?_⟩
  · norm_num [hsSquare, hsInner, Matrix.trace, Matrix.mul_apply,
      Matrix.conjTranspose_apply, matUnit, Fin.sum_univ_succ]
  · rw [hsInner_matUnit_right]
    simp [gibbsRoot_entry_zero]

/-- Plain Energy continuous for the stated finite source data. -/
theorem plainEnergy_continuous (σ : Perm) (S s : ℝ) :
    Continuous (plainEnergy σ S s) := by
  unfold plainEnergy hsSquare hsInner actualGradient thermalGradient Matrix.trace
  fun_prop

/-- Plain Gap attained for the stated finite source data. -/
theorem plainGap_attained (σ : Perm) (S s : ℝ) :
    ∃ X ∈ unitInputs σ S s,
      plainGap σ S s = plainEnergy σ S s X ∧
        ∀ Y ∈ unitInputs σ S s, plainEnergy σ S s X ≤ plainEnergy σ S s Y :=
  (unitInputs_isCompact σ S s).exists_sInf_image_eq_and_le
    (unitInputs_nonempty σ S s) (plainEnergy_continuous σ S s).continuousOn

/-- Plain Energy image bdd Below for the stated finite source data. -/
theorem plainEnergy_image_bddBelow (σ : Perm) (S s : ℝ) :
    BddBelow (plainEnergy σ S s '' unitInputs σ S s) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨X, _, rfl⟩
  exact plainEnergy_nonneg σ S s X

/-- Plain Gap le for the stated finite source data. -/
theorem plainGap_le (σ : Perm) (S s : ℝ) (X : Operator 4)
    (hX : X ∈ unitInputs σ S s) :
    plainGap σ S s ≤ plainEnergy σ S s X :=
  csInf_le (plainEnergy_image_bddBelow σ S s) (Set.mem_image_of_mem _ hX)

/-- Clock Energy nonneg for the stated finite source data. -/
theorem clockEnergy_nonneg (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) (X : Operator 4) :
    0 ≤ clockEnergy σ β S s μ X :=
  integral_nonneg (fun _ => plainEnergy_nonneg σ S s _)

/-- Clock Energy image bdd Below for the stated finite source data. -/
theorem clockEnergy_image_bddBelow (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) :
    BddBelow (clockEnergy σ β S s μ '' unitInputs σ S s) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨X, _, rfl⟩
  exact clockEnergy_nonneg σ β S s μ X

/-- Clock Gap le for the stated finite source data. -/
theorem clockGap_le (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) (X : Operator 4)
    (hX : X ∈ unitInputs σ S s) :
    clockGap σ β S s μ ≤ clockEnergy σ β S s μ X :=
  csInf_le (clockEnergy_image_bddBelow σ β S s μ) (Set.mem_image_of_mem _ hX)

/-- Clock Gap nonneg for the stated finite source data. -/
theorem clockGap_nonneg (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) :
    0 ≤ clockGap σ β S s μ := by
  apply le_csInf ((unitInputs_nonempty σ S s).image _)
  rintro _ ⟨X, _, rfl⟩
  exact clockEnergy_nonneg σ β S s μ X

/-- Clock Gap dirac zero for the stated finite source data. -/
theorem clockGap_dirac_zero (σ : Perm) (β S s : ℝ) :
    clockGap σ β S s (Measure.dirac 0) = plainGap σ S s := by
  simp only [clockGap, plainGap, clockEnergy_dirac_zero]

/-- Unit Inputs not gibbs for the stated finite source data. -/
theorem unitInputs_not_gibbs (σ : Perm) (S s : ℝ) (X : Operator 4)
    (hX : X ∈ unitInputs σ S s) :
    ¬ ∃ c : ℂ, X = c • gibbsRoot σ (lowEnergies S s) := by
  rintro ⟨c, hc⟩
  have hz : hsInner X X = 0 := by
    calc
      hsInner X X = hsInner (c • gibbsRoot σ (lowEnergies S s)) X := by rw [← hc]
      _ = 0 := by rw [hsInner_smul_left, hX.2, mul_zero]
  have hnorm := hX.1
  simp only [hsSquare, hz, Complex.zero_re] at hnorm
  norm_num at hnorm

/-- Plain Gap pos for the stated finite source data. -/
theorem plainGap_pos (σ : Perm) (S s m B : ℝ) (hm : 0 < m)
    (hcert : ScaledStackBounds σ S s m B) :
    0 < plainGap σ S s := by
  obtain ⟨X, hX, he, _⟩ := plainGap_attained σ S s
  rw [he]
  simpa only [clockEnergy_dirac_zero] using
    clockEnergy_pos_of_not_gibbs σ 0 S s m B hm hcert (Measure.dirac 0) X
      (unitInputs_not_gibbs σ S s X hX)

/-- Unit Inputs time Conjugation for the stated finite source data. -/
theorem unitInputs_timeConjugation (σ : Perm) (S s : ℝ)
    (E : Fin 3 → ℝ) (t : ℝ) (X : Operator 4) (hX : X ∈ unitInputs σ S s) :
    timeConjugation σ E t X ∈ unitInputs σ S s := by
  constructor
  · simpa only [hsSquare, hsInner_timeConjugation] using hX.1
  · have h := hsInner_timeConjugation σ E t (gibbsRoot σ (lowEnergies S s)) X
    have hg : timeConjugation σ E t (gibbsRoot σ (lowEnergies S s)) =
        gibbsRoot σ (lowEnergies S s) := by
      rw [gibbsRoot, timeConjugation_population]
    rw [hg, hX.2] at h
    exact h

/-- The attained plain gap is a lower bound for every probability clock.
This uses unitary time conjugation, not a pointwise ordering of clock forms. -/
theorem plainGap_le_clockGap (σ : Perm) (β S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    plainGap σ S s ≤ clockGap σ β S s μ := by
  apply le_csInf ((unitInputs_nonempty σ S s).image _)
  rintro _ ⟨X, hX, rfl⟩
  have h := integral_mono (integrable_const (plainGap σ S s))
    (time_plainEnergy_integrable σ S s m B hcert (physicalEnergies β S s) μ X)
    (fun t => plainGap_le σ S s _ (unitInputs_timeConjugation σ S s
      (physicalEnergies β S s) t X hX))
  simpa only [integral_const, probReal_univ, one_smul, clockEnergy] using h

/-- Clock Gap le mul plain Gap for the stated finite source data. -/
theorem clockGap_le_mul_plainGap (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ (B/m) * plainGap σ S s := by
  obtain ⟨X, hX, he, _⟩ := plainGap_attained σ S s
  have h := clockEnergy_comparison σ β S s m B hm hB hcert (Measure.dirac 0) μ X
  rw [clockEnergy_dirac_zero, ← he] at h
  exact (clockGap_le σ β S s μ X hX).trans h

/-- Clock Gap comparison for the stated finite source data. -/
theorem clockGap_comparison (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap σ S s ∧
      plainGap σ S s ≤ clockGap σ β S s μ ∧
      clockGap σ β S s μ ≤ (B/m) * plainGap σ S s :=
  ⟨plainGap_pos σ S s m B hm hcert,
    plainGap_le_clockGap σ β S s m B hcert μ,
    clockGap_le_mul_plainGap σ β S s m B hm hB hcert μ⟩


/-- Plain Energy smul for the stated finite source data. -/
theorem plainEnergy_smul (σ : Perm) (S s : ℝ) (c : ℂ) (X : Operator 4) :
    plainEnergy σ S s (c • X) = Complex.normSq c * plainEnergy σ S s X := by
  simp only [plainEnergy, actualGradient_smul, hsSquare_smul, ← Finset.mul_sum]
  ring

/-- Clock Energy smul for the stated finite source data. -/
theorem clockEnergy_smul (σ : Perm) (β S s : ℝ) (μ : Measure ℝ)
    (c : ℂ) (X : Operator 4) :
    clockEnergy σ β S s μ (c • X) =
      Complex.normSq c * clockEnergy σ β S s μ X := by
  simp only [clockEnergy, timeConjugation_smul, plainEnergy_smul, integral_const_mul]

/-- Hilbert--Schmidt normalization of a nonzero operator; no ambient sup norm is used. -/
def normalizeInput (X : Operator 4) : Operator 4 :=
  (((Real.sqrt (hsSquare X))⁻¹ : ℝ) : ℂ) • X

/-- Normalize Input mem for the stated finite source data. -/
theorem normalizeInput_mem (σ : Perm) (S s : ℝ) (X : Operator 4)
    (hp : 0 < hsSquare X)
    (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    normalizeInput X ∈ unitInputs σ S s := by
  constructor
  · rw [normalizeInput, hsSquare_smul, Complex.normSq_ofReal, ← pow_two, inv_pow,
      Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  · simp only [normalizeInput, hsInner_smul_right, ho, mul_zero]

/-- Clock Energy normalize Input for the stated finite source data. -/
theorem clockEnergy_normalizeInput (σ : Perm) (β S s : ℝ) (μ : Measure ℝ)
    (X : Operator 4) (hp : 0 < hsSquare X) :
    clockEnergy σ β S s μ (normalizeInput X) =
      (hsSquare X)⁻¹ * clockEnergy σ β S s μ X := by
  rw [normalizeInput, clockEnergy_smul, Complex.normSq_ofReal, ← pow_two, inv_pow, Real.sq_sqrt hp.le]

/-- Every pair of probability clocks has the same certificate ratio bound. -/
theorem clockGap_pairwise_comparison (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hcert : ScaledStackBounds σ S s m B)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    clockGap σ β S s ν ≤ (B/m) * clockGap σ β S s μ := by
  exact (clockGap_le_mul_plainGap σ β S s m B hm hB hcert ν).trans
    (mul_le_mul_of_nonneg_left (plainGap_le_clockGap σ β S s m B hcert μ)
      (div_nonneg hB hm.le))



/-- The actual complete matrix-unit trace trial bounds every finite probability-clock gap. -/
theorem clockGap_le_sixteen_fifteenths (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ (16/15 : ℝ) := by
  obtain ⟨X, ho, hp, hb⟩ := ThreeLevelTraceCap.threeLevel_clockEnergy_trial σ β S s μ
  calc
    _ ≤ clockEnergy σ β S s μ (normalizeInput X) :=
      clockGap_le σ β S s μ _ (normalizeInput_mem σ S s X hp ho)
    _ = (hsSquare X)⁻¹ * clockEnergy σ β S s μ X :=
      clockEnergy_normalizeInput σ β S s μ X hp
    _ ≤ 16/15 := by
      calc
        _ ≤ (hsSquare X)⁻¹ * ((16/15 : ℝ) * hsSquare X) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hp.le)
        _ = _ := by field_simp

/-- The same full trace bound applies to the attained plain Rayleigh infimum. -/
theorem plainGap_le_sixteen_fifteenths (σ : Perm) (S s : ℝ) :
    plainGap σ S s ≤ (16/15 : ℝ) := by
  rw [← clockGap_dirac_zero σ 0 S s]
  exact clockGap_le_sixteen_fifteenths σ 0 S s (Measure.dirac 0)

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighGap
