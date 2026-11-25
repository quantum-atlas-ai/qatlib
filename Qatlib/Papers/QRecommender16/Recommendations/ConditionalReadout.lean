/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRecommender16.Recommendations.RightSingularReadout
public import Qatlib.Papers.QRecommender16.Recommendations.WalkSpectrum
public import Qatlib.Papers.QRecommender16.QramMatrix.WalkEmbedding
public import Qatlib.Concepts.GradientOracle.ReadoutTools.PureStateEventLipschitzOpti
public import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation
public import Qatlib.Foundations.InstrumentCore.Measurement.MeasurementLaws

@[expose] public section

/-!
# Recommendation events after coherent threshold postselection

[KerenidisPrakash2017], Algorithms 5.2 and 6.1, samples the output conditional
on the success flag. The comparison below uses any normalized admissible
retained spectral vector, with the counting register ignored. The probability bound is
uniform over finite target events, so it also applies after grouping target
outcomes by product address. The stored-matrix theorem constructs the walk
spectrum from the right singular basis. The squared component of the user row
in the transition interval adds to the phase-estimation error budget.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec norm_toEuclidean_fromVec_sq)
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GradientOracle.ReadoutTools (pureStateEventLipschitz)
open Qatlib.Concepts.BlockEncoding.Postselection (stateVector_norm_sq)
open Qatlib.Concepts.SketchArith.GramAction (postMeasure_error_of_gap)
open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Papers.QRecommender16.QramMatrix
open Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
open scoped Classical BigOperators Matrix.Norms.Frobenius

/-- A joint success event has the Born weight of the corresponding event in the success slice. -/
private theorem measure_prob_true_slice {I : Type} (ψ : QState (Bool × I)) (event : Finset I) :
    MeasureProb ψ ({true} ×ˢ event) = MeasureProb (fun i => ψ (true, i)) event := by
  simp only [MeasureProb, Finset.sum_product, Finset.sum_singleton, BornProb]

/-- After conditioning on the success flag, a marginal over the target equals the normalized
measurement of the unnormalized success slice. -/
private theorem measure_post_measure_true_marginal {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState (Bool × I)) (event : Finset I)
    (h : 0 < MeasureProb ψ ({true} ×ˢ (Finset.univ : Finset I))) :
    MeasureProb (PostMeasure ψ ({true} ×ˢ (Finset.univ : Finset I))) (Finset.univ ×ˢ event) =
      MeasureProb (PostMeasure (fun i => ψ (true, i)) Finset.univ) event := by
  have hs : 0 < MeasureProb (fun i => ψ (true, i)) Finset.univ := by
    rwa [measure_prob_true_slice] at h
  have hInter : ({true} ×ˢ (Finset.univ : Finset I)) ∩ (Finset.univ ×ˢ event) =
      {true} ×ˢ event := by
    ext p
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_univ, and_true, true_and]
  rw [measureProb_postMeasure h, measureProb_postMeasure hs, hInter, Finset.univ_inter]
  simp only [measure_prob_true_slice]

/-- With a normalized first factor, conditioning a product state on its nonzero
total weight gives the same second-register marginal as conditioning that factor alone. -/
private theorem measure_post_measure_tensor_right {P I : Type}
    [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq I]
    (first : QState P) (second : QState I) (hn : Normalized first) (event : Finset I)
    (h : 0 < MeasureProb second Finset.univ) :
    MeasureProb (PostMeasure (TensorState first second) Finset.univ) (Finset.univ ×ˢ event) =
      MeasureProb (PostMeasure second Finset.univ) event := by
  have hTotal : MeasureProb (TensorState first second) Finset.univ = MeasureProb second Finset.univ := by
    rw [← Finset.univ_product_univ, measureProb_tensorState_right hn]
  have hTensorPos : 0 < MeasureProb (TensorState first second) Finset.univ := by rwa [hTotal]
  simp only [measureProb_postMeasure hTensorPos, measureProb_postMeasure h, Finset.univ_inter,
    measureProb_tensorState_right hn, hTotal]

/-- The ideal retained Born mass is the sum of the squared kept coefficients. -/
theorem spectral_retained_mass {I J : Type} [Fintype I] [Fintype J]
    (v : J → QState I) (c : J → ℂ) (keep : J → Prop)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0) :
    MeasureProb (∑ j, (if keep j then c j else 0) • v j) Finset.univ =
      ∑ j, ‖c j‖ ^ 2 * (if keep j then 1 else 0) := by
  change (∑ i, ‖(∑ j, (if keep j then c j else 0) • v j) i‖ ^ 2) = _
  rw [sum_norm_sq_orthonormal v _ hOrthogonal]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : keep j <;> simp [hj]

/-- If the phase-window error amplitude is smaller than the ideal retained norm, the
actual flag has positive success probability with amplitude bounded below by the retained
norm minus the classification error. Every conditional target event approximates its
probability in the normalized ideal retained state. -/
theorem spectral_threshold_recommendation_error {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (v : J → QState I) (c : J → ℂ) (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1)
    (scale window cutoff halfWidth : ℝ) (hScale : 0 < scale) (hWindow : 1 < window)
    (hResolution : scale * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, scale * foldedCosine (phase j) = value j)
    (keep : J → Prop) (hSelection : IsThresholdSelection value cutoff halfWidth keep)
    (products : Finset I) :
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue scale label
    let result := executeThresholdFlag bits U accepted (∑ j, c j • v j)
    let retained := ∑ j, (if keep j then c j else 0) • v j
    let success := {true} ×ˢ (Finset.univ : Finset (Reg bits × I))
    let retainedMass := ∑ j, ‖c j‖ ^ 2 * (if keep j then 1 else 0)
    let budget := 1 / (2 * (window - 1)) + spectralTransitionMass c value cutoff halfWidth
    let error := Real.sqrt budget
    error < Real.sqrt retainedMass →
      0 < MeasureProb result success ∧
        (Real.sqrt retainedMass - error) ^ 2 ≤ MeasureProb result success ∧
        |MeasureProb (PostMeasure result success) (Finset.univ ×ˢ (Finset.univ ×ˢ products)) -
          MeasureProb (PostMeasure retained Finset.univ) products| ≤ 2 * error / Real.sqrt retainedMass := by
  intro accepted result retained success retainedMass budget error hGap
  let ideal := TensorState (Ket (ZeroStr bits)) retained
  let actual : QState (Reg bits × I) := fun p => result (true, p)
  let event := (Finset.univ : Finset (Reg bits)) ×ˢ products
  have hRetained : MeasureProb retained Finset.univ = retainedMass :=
    spectral_retained_mass v c keep hOrthogonal
  have hKet : Normalized (Ket (ZeroStr bits)) := normalized_ket _
  have hIdeal : MeasureProb ideal Finset.univ = retainedMass := by
    rw [← Finset.univ_product_univ]
    exact (measureProb_tensorState_right hKet retained Finset.univ).trans hRetained
  have hSq : 0 ≤ budget := by
    apply add_nonneg
    · exact div_nonneg zero_le_one (mul_nonneg (by norm_num) (sub_nonneg.mpr hWindow.le))
    · unfold spectralTransitionMass
      refine Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) ?_
      split_ifs <;> norm_num
  have hClose : ‖toEuclidean_fromVec (actual - ideal)‖ ≤ error := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [norm_toEuclidean_fromVec_sq, show error ^ 2 = budget from Real.sq_sqrt hSq]
    exact spectral_threshold_band_error bits U hU v c phase value hOrthogonal hEigen
      hCoefficients scale window cutoff halfWidth hScale hWindow hResolution hValues keep hSelection
  have hIdealPos : 0 < retainedMass :=
    Real.sqrt_pos.mp ((Real.sqrt_nonneg _).trans_lt hGap)
  have hRetainedPos : 0 < MeasureProb retained Finset.univ := by rwa [hRetained]
  have hIdealPos' : 0 < MeasureProb ideal Finset.univ := by rwa [hIdeal]
  obtain ⟨hActualPos, hPost⟩ := postMeasure_error_of_gap ideal actual Finset.univ hClose (by rwa [hIdeal])
  have hFlag : 0 < MeasureProb result success := by
    unfold success
    rw [measure_prob_true_slice]
    exact hActualPos
  have hNorm (ψ : QState (Reg bits × I)) :
      ‖toEuclidean_fromVec ψ‖ = Real.sqrt (MeasureProb ψ Finset.univ) := by
    rw [← stateVector_norm_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hReverse : ‖toEuclidean_fromVec ideal‖ - ‖toEuclidean_fromVec actual‖ ≤
      ‖toEuclidean_fromVec (actual - ideal)‖ := by
    change _ ≤ ‖toEuclidean_fromVec actual - toEuclidean_fromVec ideal‖
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  rw [hNorm ideal, hNorm actual, hIdeal] at hReverse
  have hAmplitude : Real.sqrt retainedMass - error ≤ Real.sqrt (MeasureProb actual Finset.univ) := by
    linarith only [hReverse, hClose]
  have hLower : (Real.sqrt retainedMass - error) ^ 2 ≤ MeasureProb result success := by
    have hSquared := (sq_le_sq₀ (sub_nonneg.mpr hGap.le) (Real.sqrt_nonneg _)).mpr hAmplitude
    rw [Real.sq_sqrt (measureProb_nonneg _ _)] at hSquared
    simpa only [success, measure_prob_true_slice] using hSquared
  refine ⟨hFlag, hLower, ?_⟩
  rw [measure_post_measure_true_marginal result event hFlag,
    ← measure_post_measure_tensor_right _ retained hKet products hRetainedPos]
  have hEvent := pureStateEventLipschitz _ (PostMeasure actual Finset.univ) (PostMeasure ideal Finset.univ)
    (normalized_postMeasure hActualPos) (normalized_postMeasure hIdealPos') event
  rw [hIdeal] at hPost
  exact hEvent.trans hPost

/-- For a QRAM-prepared user row, compare the actual conditional product event with the
normalized squared amplitudes of its ideal retained column vector. The supplied eigenfamily
expands the prepared input and identifies its retained component in the walk image. Its retained
norm minus the phase error also bounds the original success amplitude from below. -/
theorem stored_user_recommendation_event_error {rows columns : ℕ} {J : Type} [Fintype J]
    (storage : MatrixStorage rows columns) (hValid : Valid storage) (hPos : 0 < mass storage)
    (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row)) (user : Address rows)
    (bits : ℕ) (v : J → QState (Fin (2 ^ rows) × Fin (2 ^ columns))) (c : J → ℂ)
    (phase value : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, (bireflectionWalk (storedMatrix storage)).map Complex.ofReal *ᵥ v j =
      Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hExpansion : TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ))
      (fun j => (storedUserAmplitudes storage user j : ℂ)) = ∑ j, c j • v j)
    (window cutoff halfWidth : ℝ) (hWindow : 1 < window)
    (hResolution : ‖storedMatrix storage‖ * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (hValues : ∀ j, ‖storedMatrix storage‖ * foldedCosine (phase j) = value j)
    (keep : J → Prop) (hSelection : IsThresholdSelection value cutoff halfWidth keep)
    (x : Fin (2 ^ columns) → ℝ)
    (hRetained : (∑ j, (if keep j then c j else 0) • v j) =
      fun p => ((isometryQ (storedMatrix storage) *ᵥ x) p : ℂ))
    (products : Finset (Fin (2 ^ columns))) :
    let U := (bireflectionWalk (storedMatrix storage)).map Complex.ofReal
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue ‖storedMatrix storage‖ label
    let input := TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ))
      (fun j => (storedUserAmplitudes storage user j : ℂ))
    let result := executeThresholdFlag bits U accepted input
    let success := {true} ×ˢ (Finset.univ : Finset (Reg bits × (Fin (2 ^ rows) × Fin (2 ^ columns))))
    let error := Real.sqrt (1 / (2 * (window - 1)) + spectralTransitionMass c value cutoff halfWidth)
    error < Real.sqrt (∑ j, x j ^ 2) →
      0 < MeasureProb result success ∧
        (Real.sqrt (∑ j, x j ^ 2) - error) ^ 2 ≤ MeasureProb result success ∧
        |MeasureProb (PostMeasure result success) (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ products))) -
          (∑ j ∈ products, x j ^ 2) / ∑ j, x j ^ 2| ≤ 2 * error / Real.sqrt (∑ j, x j ^ 2) := by
  intro U accepted input result success error hGap
  have hScale : 0 < ‖storedMatrix storage‖ := by
    rw [stored_matrix_frobenius_norm storage hValid]
    exact Real.sqrt_pos_of_pos hPos
  have hRowNorm (i : Fin (2 ^ rows)) : 0 < rowNormSq (storedMatrix storage) i := by
    rw [stored_matrix_row_norm_sq storage hValid]
    exact hRows _
  have hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ rows) × Fin (2 ^ columns)) ℂ :=
    complex_bireflection_walk_unitary _ hRowNorm hScale
  have hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1 := by
    have hn : Normalized (∑ j, c j • v j) := by
      rw [← hExpansion]
      exact normalized_tensorState (stored_row_norm_amplitudes_normalized storage hValid hPos)
        (stored_user_amplitudes_normalized storage hValid user (hRows user))
    change (∑ p, ‖(∑ j, c j • v j) p‖ ^ 2) = 1 at hn
    rwa [sum_norm_sq_orthonormal v c hOrthogonal] at hn
  have hMass : (∑ j, ‖c j‖ ^ 2 * (if keep j then 1 else 0)) = ∑ j, x j ^ 2 := by
    rw [← spectral_retained_mass v c keep hOrthogonal, hRetained,
      stored_walk_image_mass storage hValid hPos]
  have hX : 0 < ∑ j, x j ^ 2 := Real.sqrt_pos.mp ((Real.sqrt_nonneg _).trans_lt hGap)
  have hLaw := spectral_threshold_recommendation_error bits U hU v c phase value hOrthogonal hEigen
    hCoefficients ‖storedMatrix storage‖ window cutoff halfWidth hScale hWindow hResolution
    hValues keep hSelection (Finset.univ ×ˢ products) (by rwa [hMass])
  change 0 < MeasureProb (executeThresholdFlag bits U accepted input) success ∧ _
  unfold result input
  rw [hExpansion]
  obtain ⟨hSuccess, hLower, hEvent⟩ := hLaw
  refine ⟨hSuccess, by simpa only [hMass] using hLower, ?_⟩
  simpa only [hMass, hRetained, stored_walk_product_event storage hValid hPos x hX products] using hEvent

/-- Select a subset of the right singular directions of a real vector. -/
def rightSingularPart {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (x : Fin columns → ℝ) (keep : Fin columns → Prop) : Fin columns → ℝ :=
  ∑ j, (if keep j then x ⬝ᵥ rightSingularVector A j else 0) •
    rightSingularVector A j

/-- The ideal cutoff projects a real column vector onto the retained right singular directions. -/
def rightSingularProjection {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (x : Fin columns → ℝ) (cutoff : ℝ) : Fin columns → ℝ :=
  rightSingularPart A x (fun j => cutoff ≤ rightSingularValue A j)

/-- The squared norm of the user's projection into the right singular transition interval. -/
def rightSingularTransitionMass {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (x : Fin columns → ℝ) (cutoff halfWidth : ℝ) : ℝ :=
  ∑ i, rightSingularPart A x (fun j => thresholdTransition cutoff halfWidth (rightSingularValue A j)) i ^ 2

/-- Separation of the full spectrum from the transition interval gives zero user transition mass. -/
theorem right_singular_transition_mass_eq_zero {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (x : Fin columns → ℝ) (cutoff halfWidth : ℝ)
    (hOutside : ∀ j, rightSingularValue A j < cutoff - 2 * halfWidth ∨ cutoff ≤ rightSingularValue A j) :
    rightSingularTransitionMass A x cutoff halfWidth = 0 := by
  have hNone (j : Fin columns) : ¬ thresholdTransition cutoff halfWidth (rightSingularValue A j) :=
    fun h => (hOutside j).elim (fun hBelow => (not_le_of_gt hBelow) h.1) (fun hAbove => (not_le_of_gt h.2) hAbove)
  simp [rightSingularTransitionMass, rightSingularPart, hNone]

/-- State orthogonality for the walk spectrum with the proposition-based equality decision
used by the generic spectral readout contracts. -/
private theorem readout_walk_orthogonal {rows columns : ℕ} (A : Matrix (Fin rows) (Fin columns) ℝ)
    (hRows : ∀ i, 0 < rowNormSq A i) (hNorm : 0 < ‖A‖) (p q : WalkBranchIndex A) :
    Inner (walkSpectrumVector A p) (walkSpectrumVector A q) =
      @ite ℂ (p = q) (Classical.propDecidable (p = q)) 1 0 := by
  by_cases h : p = q <;> simpa [h] using walk_spectrum_orthonormal A hRows hNorm p q

/-- The tensor product of the stored row-norm amplitudes and a real column input expands
in the actual walk eigenbranches with the corresponding right singular coefficients. -/
private theorem stored_walk_spectral_expansion {rows columns : ℕ} (storage : MatrixStorage rows columns)
    (hValid : Valid storage) (hPos : 0 < mass storage) (hNorm : 0 < ‖storedMatrix storage‖)
    (u : Fin (2 ^ columns) → ℝ) :
    let A := storedMatrix storage
    let d j := u ⬝ᵥ rightSingularVector A j
    TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ)) (fun j => (u j : ℂ)) =
      ∑ p, walkSpectrumCoefficient A d p • walkSpectrumVector A p := by
  intro A d
  have hFull := walk_spectrum_expansion A hNorm d
  have hRight : (∑ j, d j • rightSingularVector A j) = u := right_singular_vector_expansion A u
  rw [hRight] at hFull
  exact (stored_walk_embedding storage hValid hPos u).trans hFull.symm

/-- Keeping whole right singular directions gives the same total mass on the walk branches
as the squared Euclidean norm of the selected column vector. -/
private theorem stored_right_part_spectral_mass {rows columns : ℕ} (storage : MatrixStorage rows columns)
    (hValid : Valid storage) (hPos : 0 < mass storage) (hNorm : 0 < ‖storedMatrix storage‖)
    (hRows : ∀ i, 0 < rowNormSq (storedMatrix storage) i) (u : Fin (2 ^ columns) → ℝ)
    (keep : Fin (2 ^ columns) → Prop) :
    let A := storedMatrix storage
    let d j := u ⬝ᵥ rightSingularVector A j
    (∑ p, ‖walkSpectrumCoefficient A d p‖ ^ 2 * (if keep (walkBranchDirection p) then 1 else 0)) =
      ∑ j, rightSingularPart A u keep j ^ 2 := by
  intro A d
  rw [← spectral_retained_mass (walkSpectrumVector A) _ (fun p => keep (walkBranchDirection p))
    (readout_walk_orthogonal A hRows hNorm)]
  rw [walk_spectrum_retained_expansion A hNorm d keep, stored_walk_image_mass storage hValid hPos, rightSingularPart]

/-- The actual QRAM recommendation flag succeeds with probability at least the hard-cutoff
weight times the phase-estimation success bound. The estimate permits arbitrary mass below
the cutoff, including in the transition interval. -/
theorem stored_recommendation_flag_success_lower {rows columns : ℕ}
    (storage : MatrixStorage rows columns) (hValid : Valid storage) (hPos : 0 < mass storage)
    (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row)) (user : Address rows)
    (bits : ℕ) (window cutoff halfWidth : ℝ) (hWindow : 1 < window)
    (hResolution : ‖storedMatrix storage‖ * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth) :
    let A := storedMatrix storage
    let x := rightSingularProjection A (storedUserAmplitudes storage user) cutoff
    let U := (bireflectionWalk A).map Complex.ofReal
    let accepted := Finset.univ.filter fun label : Reg bits => cutoff - halfWidth ≤ singularReadoutValue ‖A‖ label
    let result := executeThresholdFlag bits U accepted (storedWalkUserInput storage user)
    (1 - 1 / (2 * (window - 1))) * (∑ j, x j ^ 2) ≤
      MeasureProb result ({true} ×ˢ (Finset.univ : Finset (Reg bits × (Fin (2 ^ rows) × Fin (2 ^ columns))))) := by
  intro A x U accepted result
  let u := storedUserAmplitudes storage user
  let d j := u ⬝ᵥ rightSingularVector A j
  have hNorm : 0 < ‖A‖ := by
    change 0 < ‖storedMatrix storage‖
    rw [stored_matrix_frobenius_norm storage hValid]
    exact Real.sqrt_pos.mpr hPos
  have hRowNorm (i : Fin (2 ^ rows)) : 0 < rowNormSq A i := by
    change 0 < rowNormSq (storedMatrix storage) i
    rw [stored_matrix_row_norm_sq storage hValid]
    exact hRows _
  have hInput : storedWalkUserInput storage user = ∑ p, walkSpectrumCoefficient A d p • walkSpectrumVector A p :=
    ((stored_walk_user_preparation storage hValid hPos user (hRows user)).trans
      (stored_walk_embedding storage hValid hPos u).symm).trans
      (stored_walk_spectral_expansion storage hValid hPos hNorm u)
  have hMass : (∑ p, ‖walkSpectrumCoefficient A d p‖ ^ 2 * (if cutoff ≤ walkSpectrumValue A p then 1 else 0)) =
      ∑ j, x j ^ 2 :=
    stored_right_part_spectral_mass storage hValid hPos hNorm hRowNorm u (fun j => cutoff ≤ rightSingularValue A j)
  have hFlag := spectral_threshold_success_lower bits U (complex_bireflection_walk_unitary A hRowNorm hNorm)
    (walkSpectrumVector A) (walkSpectrumCoefficient A d) (walkSpectrumPhase A) (walkSpectrumValue A)
    (readout_walk_orthogonal A hRowNorm hNorm) (fun p => (walk_spectrum_eigenpair A hRowNorm hNorm p).1)
    ‖A‖ window cutoff halfWidth hNorm hWindow hResolution (fun p => (walk_spectrum_eigenpair A hRowNorm hNorm p).2)
  rw [hMass] at hFlag
  unfold result
  rwa [hInput]

/-- The stored matrix determines both the executed walk and the ideal filtered user row.
Whenever the retained norm exceeds the error budget, every conditional product event
approximates the normalized squared-amplitude law of the given admissible selection.
The error includes the phase tail and the transition weight of this user. -/
theorem stored_recommendation_event_error {rows columns : ℕ}
    (storage : MatrixStorage rows columns) (hValid : Valid storage) (hPos : 0 < mass storage)
    (hRows : ∀ row : Address rows, 0 < mass (rowTree storage row)) (user : Address rows)
    (bits : ℕ) (window cutoff halfWidth : ℝ) (hWindow : 1 < window)
    (hResolution : ‖storedMatrix storage‖ * (Real.pi * (window / (2 ^ bits : ℝ))) ≤ halfWidth)
    (keep : Fin (2 ^ columns) → Prop)
    (hSelection : IsThresholdSelection (rightSingularValue (storedMatrix storage)) cutoff halfWidth keep)
    (products : Finset (Fin (2 ^ columns))) :
    let A := storedMatrix storage
    let x := rightSingularPart A (storedUserAmplitudes storage user) keep
    let error := Real.sqrt (1 / (2 * (window - 1)) +
      rightSingularTransitionMass A (storedUserAmplitudes storage user) cutoff halfWidth)
    let U := (bireflectionWalk A).map Complex.ofReal
    let accepted := Finset.univ.filter fun label : Reg bits =>
      cutoff - halfWidth ≤ singularReadoutValue ‖A‖ label
    let input := storedWalkUserInput storage user
    let result := executeThresholdFlag bits U accepted input
    let success := {true} ×ˢ (Finset.univ : Finset (Reg bits × (Fin (2 ^ rows) × Fin (2 ^ columns))))
    error < Real.sqrt (∑ j, x j ^ 2) →
      0 < MeasureProb result success ∧
        (Real.sqrt (∑ j, x j ^ 2) - error) ^ 2 ≤ MeasureProb result success ∧
        |MeasureProb (PostMeasure result success) (Finset.univ ×ˢ (Finset.univ ×ˢ (Finset.univ ×ˢ products))) -
          (∑ j ∈ products, x j ^ 2) / ∑ j, x j ^ 2| ≤
            2 * error / Real.sqrt (∑ j, x j ^ 2) := by
  intro A x error U accepted input result success hGap
  let u := storedUserAmplitudes storage user
  let d : Fin (2 ^ columns) → ℝ := fun j => u ⬝ᵥ rightSingularVector A j
  have hNorm : 0 < ‖A‖ := by
    change 0 < ‖storedMatrix storage‖
    rw [stored_matrix_frobenius_norm storage hValid]
    exact Real.sqrt_pos_of_pos hPos
  have hRowNorm (i : Fin (2 ^ rows)) : 0 < rowNormSq A i := by
    change 0 < rowNormSq (storedMatrix storage) i
    rw [stored_matrix_row_norm_sq storage hValid]
    exact hRows _
  have hExpansion : TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ))
      (fun j => (u j : ℂ)) = ∑ p, walkSpectrumCoefficient A d p • walkSpectrumVector A p :=
    stored_walk_spectral_expansion storage hValid hPos hNorm u
  let keepBranch (p : WalkBranchIndex A) := keep (walkBranchDirection p)
  have hBranchSelection : IsThresholdSelection (walkSpectrumValue A) cutoff halfWidth keepBranch :=
    ⟨fun p hp => hSelection.1 (walkBranchDirection p) hp, fun p hp => hSelection.2 (walkBranchDirection p) hp⟩
  have hRetained : (∑ p, (if keepBranch p then walkSpectrumCoefficient A d p else 0) •
      walkSpectrumVector A p) = fun i => ((isometryQ A *ᵥ x) i : ℂ) :=
    walk_spectrum_retained_expansion A hNorm d keep
  have hBand : spectralTransitionMass (walkSpectrumCoefficient A d) (walkSpectrumValue A) cutoff halfWidth =
      rightSingularTransitionMass A u cutoff halfWidth :=
    stored_right_part_spectral_mass storage hValid hPos hNorm hRowNorm u
      (fun j => thresholdTransition cutoff halfWidth (rightSingularValue A j))
  have hPrepared : input = TensorState (fun i => (storedRowNormAmplitudes storage i : ℂ))
      (fun j => (u j : ℂ)) :=
    (stored_walk_user_preparation storage hValid hPos user (hRows user)).trans
      (stored_walk_embedding storage hValid hPos u).symm
  unfold result
  rw [hPrepared]
  have hLaw := stored_user_recommendation_event_error storage hValid hPos hRows user bits
    (walkSpectrumVector A) (walkSpectrumCoefficient A d) (walkSpectrumPhase A) (walkSpectrumValue A)
    (readout_walk_orthogonal A hRowNorm hNorm)
    (fun p => (walk_spectrum_eigenpair A hRowNorm hNorm p).1)
    hExpansion window cutoff halfWidth hWindow hResolution (fun p => (walk_spectrum_eigenpair A hRowNorm hNorm p).2)
    keepBranch hBranchSelection x hRetained products (by rwa [hBand])
  rwa [hBand] at hLaw

end Qatlib.Papers.QRecommender16.Recommendations
