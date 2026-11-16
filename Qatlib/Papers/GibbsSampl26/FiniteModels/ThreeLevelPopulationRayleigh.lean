/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighGap
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
# Intrinsic population Rayleigh minimum and the factor-twenty gap bridge

The population minimum is defined from the actual invariant mass on the full
complex Gibbs-orthogonal Hilbert--Schmidt unit sphere in the population space.
It is attained and positive. Orthogonal population/fast decomposition supplies
the full-space mass floor. The final gap comparison consumes an actual source
certificate and an actual population energy bound, with no external eigenvalue.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationRayleigh
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

def populationUnitInputs (σ : Perm) (S s : ℝ) : Set (Operator 4) :=
  {X | X ∈ unitInputs σ S s ∧ fastPart σ X = 0}

def populationMinimum (σ : Perm) (S s : ℝ) : ℝ :=
  sInf (invariantMass σ S s '' populationUnitInputs σ S s)

/-- Population Coefficient sub for the stated finite source data. -/
theorem populationCoefficient_sub (σ : Perm) (X Y : Operator 4) :
    populationCoefficient σ (X-Y) =
      fun i => populationCoefficient σ X i - populationCoefficient σ Y i := by
  funext i
  simp [populationCoefficient, hsInner_sub_right, sub_div]

/-- Population Part sub for the stated finite source data. -/
theorem populationPart_sub (σ : Perm) (X Y : Operator 4) :
    populationPart σ (X-Y) = populationPart σ X - populationPart σ Y := by
  simp [populationPart, populationCoefficient_sub, population, sub_smul,
    Finset.sum_sub_distrib]

/-- Fast Part sub for the stated finite source data. -/
theorem fastPart_sub (σ : Perm) (X Y : Operator 4) :
    fastPart σ (X-Y) = fastPart σ X - fastPart σ Y := by
  simp only [fastPart, populationPart_sub]
  abel

/-- Fast Part continuous for the stated finite source data. -/
theorem fastPart_continuous (σ : Perm) : Continuous (fastPart σ) := by
  unfold fastPart populationPart population populationCoefficient hsInner Matrix.trace
  fun_prop

/-- Invariant Mass continuous for the stated finite source data. -/
theorem invariantMass_continuous (σ : Perm) (S s : ℝ) :
    Continuous (invariantMass σ S s) := by
  unfold invariantMass firstCoordinate secondCoordinate hsSquare fastPart populationPart
    population populationCoefficient hsInner Matrix.trace
  fun_prop

/-- Population Unit Inputs is Compact for the stated finite source data. -/
theorem populationUnitInputs_isCompact (σ : Perm) (S s : ℝ) :
    IsCompact (populationUnitInputs σ S s) := by
  change IsCompact (unitInputs σ S s ∩ {X | fastPart σ X = 0})
  exact (unitInputs_isCompact σ S s).inter_right
    (isClosed_eq (fastPart_continuous σ) continuous_const)

/-- Population Coefficient seed Two for the stated finite source data. -/
theorem populationCoefficient_seedTwo (σ : Perm) :
    populationCoefficient σ (seedTwo σ) = ![0,0,1] := by
  rw [← population_seedTwo, populationCoefficient_population]

/-- Centered seed Two ne zero for the stated finite source data. -/
theorem centered_seedTwo_ne_zero (σ : Perm) (S s : ℝ) :
    orthogonalCenter (seedTwo σ) (gibbsRoot σ (lowEnergies S s)) ≠ 0 := by
  intro hz
  let g := gibbsRoot σ (lowEnergies S s)
  let c := hsPair g (seedTwo σ) / hsPair g g
  have he : seedTwo σ = c • g := by
    exact sub_eq_zero.mp hz
  have h0 := congrArg (fun X => populationCoefficient σ X 0) he
  simp only [populationCoefficient_seedTwo, populationCoefficient_smul,
    g, populationCoefficient_gibbs_low, Matrix.cons_val_zero, mul_one] at h0
  have hc : c = 0 := h0.symm
  have h2 := congrArg (fun X => populationCoefficient σ X 2) he
  rw [populationCoefficient_seedTwo, hc] at h2
  norm_num [populationCoefficient, hsInner] at h2

/-- Centered seed Two fast Part for the stated finite source data. -/
theorem centered_seedTwo_fastPart (σ : Perm) (S s : ℝ) :
    fastPart σ (orthogonalCenter (seedTwo σ) (gibbsRoot σ (lowEnergies S s))) = 0 := by
  rw [orthogonalCenter, fastPart_sub, fastPart_gibbs_smul,
    ← population_seedTwo, fastPart_population, sub_zero]

/-- Population Unit Inputs nonempty for the stated finite source data. -/
theorem populationUnitInputs_nonempty (σ : Perm) (S s : ℝ) :
    (populationUnitInputs σ S s).Nonempty := by
  let X := orthogonalCenter (seedTwo σ) (gibbsRoot σ (lowEnergies S s))
  have hp : 0 < hsSquare X := hsInner_self_pos (centered_seedTwo_ne_zero σ S s)
  have ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0 :=
    actual_center_orthogonal σ (lowEnergies S s) (seedTwo σ)
  refine ⟨normalizeInput X, normalizeInput_mem σ S s X hp ho, ?_⟩
  rw [normalizeInput, fastPart_smul, centered_seedTwo_fastPart, smul_zero]

/-- Population Minimum attained for the stated finite source data. -/
theorem populationMinimum_attained (σ : Perm) (S s : ℝ) :
    ∃ X ∈ populationUnitInputs σ S s,
      populationMinimum σ S s = invariantMass σ S s X ∧
        ∀ Y ∈ populationUnitInputs σ S s,
          invariantMass σ S s X ≤ invariantMass σ S s Y :=
  (populationUnitInputs_isCompact σ S s).exists_sInf_image_eq_and_le
    (populationUnitInputs_nonempty σ S s) (invariantMass_continuous σ S s).continuousOn

/-- Population Minimum pos for the stated finite source data. -/
theorem populationMinimum_pos (σ : Perm) (S s : ℝ) :
    0 < populationMinimum σ S s := by
  obtain ⟨X, hX, he, _⟩ := populationMinimum_attained σ S s
  rw [he]
  have hn := invariantMass_nonneg σ S s X
  have hne : invariantMass σ S s X ≠ 0 := by
    intro hz
    exact unitInputs_not_gibbs σ S s X hX.1
      ((invariantMass_eq_zero_iff σ S s X).mp hz)
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- Population Minimum le for the stated finite source data. -/
theorem populationMinimum_le (σ : Perm) (S s : ℝ) (X : Operator 4)
    (hX : X ∈ populationUnitInputs σ S s) :
    populationMinimum σ S s ≤ invariantMass σ S s X := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨Y, _, rfl⟩
    exact invariantMass_nonneg σ S s Y
  · exact Set.mem_image_of_mem _ hX

/-- Invariant Mass normalize Input for the stated finite source data. -/
theorem invariantMass_normalizeInput (σ : Perm) (S s : ℝ)
    (X : Operator 4) (hp : 0 < hsSquare X) :
    invariantMass σ S s (normalizeInput X) =
      (hsSquare X)⁻¹ * invariantMass σ S s X := by
  rw [normalizeInput, invariantMass_smul, Complex.normSq_ofReal, ← pow_two,
    inv_pow, Real.sq_sqrt hp.le]

/-- Population Minimum mul hs Square le for the stated finite source data. -/
theorem populationMinimum_mul_hsSquare_le (σ : Perm) (S s : ℝ) (X : Operator 4)
    (hf : fastPart σ X = 0)
    (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    populationMinimum σ S s * hsSquare X ≤ invariantMass σ S s X := by
  by_cases hz : hsSquare X = 0
  · rw [hz, mul_zero]
    exact invariantMass_nonneg σ S s X
  · have hp : 0 < hsSquare X := lt_of_le_of_ne (hsSquare_nonneg X) (Ne.symm hz)
    have hf' : fastPart σ (normalizeInput X) = 0 := by
      rw [normalizeInput, fastPart_smul, hf, smul_zero]
    have hn := populationMinimum_le σ S s (normalizeInput X)
      ⟨normalizeInput_mem σ S s X hp ho, hf'⟩
    rw [invariantMass_normalizeInput σ S s X hp] at hn
    have hn' : populationMinimum σ S s ≤ invariantMass σ S s X / hsSquare X := by
      simpa only [div_eq_mul_inv, mul_comm] using hn
    exact (le_div_iff₀ hp).mp hn'

/-- Hs Inner add right formula for the stated finite source data. -/
theorem hsInner_add_right_formula (X Y Z : Operator 4) :
    hsInner X (Y+Z) = hsInner X Y + hsInner X Z := by
  simp [hsInner, Matrix.mul_add, Matrix.trace_add]

/-- Hs Square add of orthogonal for the stated finite source data. -/
theorem hsSquare_add_of_orthogonal (X Y : Operator 4) (h : hsInner X Y = 0) :
    hsSquare (X+Y) = hsSquare X + hsSquare Y := by
  have hr : hsInner Y X = 0 := by
    rw [hsInner_conj_swap, h, star_zero]
  have he : hsInner (X+Y) (X+Y) =
      hsInner X X + hsInner X Y + (hsInner Y X + hsInner Y Y) := by
    simp [hsInner, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    ring
  rw [hsSquare, he, h, hr, add_zero, zero_add, Complex.add_re]
  rfl

/-- Hs Square population fast for the stated finite source data. -/
theorem hsSquare_population_fast (σ : Perm) (X : Operator 4) :
    hsSquare X = hsSquare (populationPart σ X) + hsSquare (fastPart σ X) := by
  calc
    hsSquare X = hsSquare (populationPart σ X + fastPart σ X) :=
      congrArg hsSquare (populationPart_add_fastPart σ X).symm
    _ = _ := hsSquare_add_of_orthogonal _ _
      (hsInner_population_fast σ _ _ (fastPart_isFast σ X))

/-- Population Part gibbs orthogonal for the stated finite source data. -/
theorem populationPart_gibbs_orthogonal (σ : Perm) (S s : ℝ) (X : Operator 4)
    (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    hsInner (gibbsRoot σ (lowEnergies S s)) (populationPart σ X) = 0 := by
  have hf : hsInner (gibbsRoot σ (lowEnergies S s)) (fastPart σ X) = 0 :=
    hsInner_population_fast σ _ _ (fastPart_isFast σ X)
  have h := congrArg (fun Y => hsInner (gibbsRoot σ (lowEnergies S s)) Y)
    (populationPart_add_fastPart σ X)
  rw [hsInner_add_right_formula, hf, add_zero, ho] at h
  exact h

/-- Invariant Mass population fast for the stated finite source data. -/
theorem invariantMass_population_fast (σ : Perm) (S s : ℝ) (X : Operator 4) :
    invariantMass σ S s X =
      invariantMass σ S s (populationPart σ X) + hsSquare (fastPart σ X) := by
  simp only [invariantMass, firstCoordinate, secondCoordinate, populationPart,
    populationCoefficient_population, fastPart_population]
  simp [hsSquare, hsInner]

/-- Invariant Mass lower for the stated finite source data. -/
theorem invariantMass_lower (σ : Perm) (S s : ℝ) (X : Operator 4)
    (ho : hsInner (gibbsRoot σ (lowEnergies S s)) X = 0) :
    min (populationMinimum σ S s) 1 * hsSquare X ≤ invariantMass σ S s X := by
  have hp := populationMinimum_mul_hsSquare_le σ S s (populationPart σ X)
    (fastPart_population σ _) (populationPart_gibbs_orthogonal σ S s X ho)
  rw [hsSquare_population_fast σ X, invariantMass_population_fast σ S s X, mul_add]
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hsSquare_nonneg _)).trans hp
  · simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (min_le_right (populationMinimum σ S s) 1)
        (hsSquare_nonneg (fastPart σ X))

/-- Plain Gap lower for the stated finite source data. -/
theorem plainGap_lower (σ : Perm) (S s B : ℝ)
    (hcert : ScaledStackBounds σ S s 1 B) :
    min (populationMinimum σ S s) 1 / 12 ≤ plainGap σ S s := by
  obtain ⟨X, hX, he, _⟩ := plainGap_attained σ S s
  have hm := invariantMass_lower σ S s X hX.2
  rw [hX.1, mul_one] at hm
  have hb := (plainEnergy_bounds σ S s 1 B hcert X).1
  rw [he]
  nlinarith

/-- Time Conjugation eq self of fast Part zero for the stated finite source data. -/
theorem timeConjugation_eq_self_of_fastPart_zero (σ : Perm) (E : Fin 3 → ℝ)
    (t : ℝ) (X : Operator 4) (hf : fastPart σ X = 0) :
    timeConjugation σ E t X = X := by
  have hp : populationPart σ X = X := by
    simpa only [hf, add_zero] using populationPart_add_fastPart σ X
  calc
    timeConjugation σ E t X = timeConjugation σ E t (populationPart σ X) := by rw [hp]
    _ = populationPart σ X := timeConjugation_population σ E t _
    _ = X := hp

/-- Clock Energy eq plain of fast Part zero for the stated finite source data. -/
theorem clockEnergy_eq_plain_of_fastPart_zero (σ : Perm) (β S s : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4)
    (hf : fastPart σ X = 0) :
    clockEnergy σ β S s μ X = plainEnergy σ S s X := by
  simp only [clockEnergy, timeConjugation_eq_self_of_fastPart_zero σ _ _ X hf,
    integral_const, probReal_univ, one_smul]

/-- Clock Gap le population Minimum for the stated finite source data. -/
theorem clockGap_le_populationMinimum (σ : Perm) (β S s : ℝ)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ (5/3 : ℝ) * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ (5/3 : ℝ) * populationMinimum σ S s := by
  obtain ⟨X, hX, he, _⟩ := populationMinimum_attained σ S s
  calc
    clockGap σ β S s μ ≤ clockEnergy σ β S s μ X :=
      clockGap_le σ β S s μ X hX.1
    _ = plainEnergy σ S s X := clockEnergy_eq_plain_of_fastPart_zero σ β S s μ X hX.2
    _ ≤ (5/3 : ℝ) * invariantMass σ S s X := hpop X hX.2
    _ = (5/3 : ℝ) * populationMinimum σ S s := by rw [← he]

/-- Clock Gap le twenty plain Gap for the stated finite source data. -/
theorem clockGap_le_twenty_plainGap (σ : Perm) (β S s B : ℝ)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ (5/3 : ℝ) * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    clockGap σ β S s μ ≤ 20 * plainGap σ S s := by
  have hl := plainGap_lower σ S s B hcert
  by_cases hmin : populationMinimum σ S s ≤ 1
  · rw [min_eq_left hmin] at hl
    have hu := clockGap_le_populationMinimum σ β S s hpop μ
    nlinarith
  · rw [min_eq_right (le_of_not_ge hmin)] at hl
    have hu := clockGap_le_sixteen_fifteenths σ β S s μ
    nlinarith

/-- Clock Gap comparison twenty for the stated finite source data. -/
theorem clockGap_comparison_twenty (σ : Perm) (β S s B : ℝ)
    (hcert : ScaledStackBounds σ S s 1 B)
    (hpop : ∀ X : Operator 4, fastPart σ X = 0 →
      plainEnergy σ S s X ≤ (5/3 : ℝ) * invariantMass σ S s X)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    0 < plainGap σ S s ∧
      plainGap σ S s ≤ clockGap σ β S s μ ∧
      clockGap σ β S s μ ≤ 20 * plainGap σ S s :=
  ⟨plainGap_pos σ S s 1 B (by norm_num) hcert,
    plainGap_le_clockGap σ β S s 1 B hcert μ,
    clockGap_le_twenty_plainGap σ β S s B hcert hpop μ⟩


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationRayleigh
