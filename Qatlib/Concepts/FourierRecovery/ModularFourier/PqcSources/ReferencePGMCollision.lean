/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PureEnsemblePGM
import Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.State
import Qatlib.Concepts.ProbabilityCore.Concentration.FiniteLinearHash
import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashMoment
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Qatlib.Concepts.MbqcFlow.FlowDecision
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic
open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! The actual character-indexed PGM of a fixed public coefficient law.
No efficient character labelling, noisy-source bridge, or gate implementation
is asserted. Random matrices include zero and rank-deficient matrices. -/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open Matrix
open scoped BigOperators ComplexConjugate

/-- Definition of pqc Reference Phase Ensemble in the Modular Fourier construction. -/
noncomputable def pqcReferencePhaseEnsemble
    {K I J : Type} [Field K] [Fintype K] [Fintype I] [Fintype J]
    {D : ℕ} (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D)) :
    Matrix (Fin D) (AddChar (J → K) ℂ) ℂ :=
  fun x χ => (Real.sqrt (p.prob x) : ℂ) * χ (finiteLinearMatrixHash M (enc x))

/-- The actual finite-label construction satisfies `pqc_reference_phase_normalized` with all displayed hypotheses. -/
theorem pqc_reference_phase_normalized
    {K I J : Type} [Field K] [Fintype K] [Fintype I] [Fintype J]
    {D : ℕ} (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) :
    Normalized (fun x => pqcReferencePhaseEnsemble M enc p x χ) := by
  simp only [Normalized, pqcReferencePhaseEnsemble, norm_mul, AddChar.norm_apply,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (p.nonneg _)]
  exact p.sum_one

/-- The actual finite-label construction satisfies `normSq_inner_self_sum` with all displayed hypotheses. -/
private theorem normSq_inner_self_sum
    {X : Type} [Fintype X] (f : X → ℂ) :
    (Inner f f).re = ∑ x, Complex.normSq (f x) := by
  classical
  rw [inner_self, Complex.re_sum]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- The actual finite-label construction satisfies `parseval_counting` with all displayed hypotheses. -/
private theorem parseval_counting
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, Complex.normSq (∑ y : G, conj (χ y) * f y)) =
      (Fintype.card G : ℝ) * ∑ y : G, Complex.normSq (f y) := by
  have h := congrArg Complex.re (Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.inner_fourier f f)
  rw [normSq_inner_self_sum, normSq_inner_self_sum] at h
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : Complex.normSq (Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.fourierScale G) =
      (Fintype.card G : ℝ)⁻¹ := by
    rw [Complex.normSq_eq_norm_sq]
    exact norm_fourierScale_sq
  simp only [Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.fourier_apply,
    Complex.normSq_mul, hs,
    ← Finset.mul_sum] at h
  calc
    _ = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ)⁻¹ *
        ∑ χ : AddChar G ℂ, Complex.normSq (∑ y : G, conj (χ y) * f y)) := by field_simp
    _ = _ := by rw [h]

/-- Definition of pqc Reference Syndrome Mass in the Modular Fourier construction. -/
noncomputable def pqcReferenceSyndromeMass
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype J] {D : ℕ}
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D)) (y : J → K) : ℝ :=
  ∑ x, if finiteLinearMatrixHash M (enc x) = y then p.prob x else 0

section Phase
variable {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [Fintype J] [DecidableEq J] {D : ℕ}

/-- The actual finite-label construction satisfies `syndrome_mass_sum` with all displayed hypotheses. -/
private theorem syndrome_mass_sum
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D)) :
    ∑ y, pqcReferenceSyndromeMass M enc p y = 1 := by
  classical
  unfold pqcReferenceSyndromeMass
  rw [Finset.sum_comm]
  simpa using p.sum_one

/-- The actual finite-label construction satisfies `syndrome_weighted_sum` with all displayed hypotheses. -/
private theorem syndrome_weighted_sum
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (f : (J → K) → ℂ) :
    (∑ y, (pqcReferenceSyndromeMass M enc p y : ℂ) * f y) =
      ∑ x, (p.prob x : ℂ) * f (finiteLinearMatrixHash M (enc x)) := by
  classical
  simp only [pqcReferenceSyndromeMass, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- The actual finite-label construction satisfies `reference_gram_entry` with all displayed hypotheses. -/
private theorem reference_gram_entry
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ η : AddChar (J → K) ℂ) :
    (ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η =
      ∑ y, (pqcReferenceSyndromeMass M enc p y : ℂ) * (conj (χ y) * η y) := by
  classical
  change (∑ x, star (pqcReferencePhaseEnsemble M enc p x χ) *
    pqcReferencePhaseEnsemble M enc p x η) = _
  rw [syndrome_weighted_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hs : (Real.sqrt (p.prob x) : ℂ)^2 = (p.prob x : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (p.nonneg x)]
  simp only [pqcReferencePhaseEnsemble, Complex.star_def, map_mul, Complex.conj_ofReal]
  calc
    _ = (Real.sqrt (p.prob x) : ℂ)^2 * (conj (χ _) * η _) := by ring
    _ = _ := by rw [hs]

/-- The actual finite-label construction satisfies `reference_gram_diagonal` with all displayed hypotheses. -/
private theorem reference_gram_diagonal
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) :
    (ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ χ = 1 := by
  rw [reference_gram_entry]
  have hc (y : J → K) : conj (χ y) * χ y = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  simp_rw [hc, mul_one]
  rw [← Complex.ofReal_sum, syndrome_mass_sum]
  rfl

/-- The actual finite-label construction satisfies `reference_gram_energy` with all displayed hypotheses. -/
private theorem reference_gram_energy
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) :
    (∑ η, Complex.normSq ((ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η)) =
      (Fintype.card (J → K) : ℝ) * ∑ y, pqcReferenceSyndromeMass M enc p y ^ 2 := by
  classical
  let f : (J → K) → ℂ := fun y => (pqcReferenceSyndromeMass M enc p y : ℂ) * χ y
  have he (η : AddChar (J → K) ℂ) :
      conj ((ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η) =
        ∑ y, conj (η y) * f y := by
    rw [reference_gram_entry, map_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply, f]
    ring
  have hnorm (y : J → K) : Complex.normSq (f y) = pqcReferenceSyndromeMass M enc p y ^ 2 := by
    change Complex.normSq ((pqcReferenceSyndromeMass M enc p y : ℂ) * χ y) = _
    rw [Complex.normSq_mul]
    simp [Complex.normSq_eq_norm_sq, AddChar.norm_apply,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ = ∑ η : AddChar (J → K) ℂ, Complex.normSq (∑ y, conj (η y) * f y) := by
      apply Finset.sum_congr rfl
      intro η _
      rw [← he, Complex.normSq_conj]
    _ = _ := by rw [parseval_counting]; simp_rw [hnorm]

/-- The actual finite-label construction satisfies `reference_row_centered_energy` with all displayed hypotheses. -/
private theorem reference_row_centered_energy
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) :
    (∑ η ∈ Finset.univ.erase χ,
      Complex.normSq ((ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η)) =
      (Fintype.card (J → K) : ℝ) *
        ∑ y, (pqcReferenceSyndromeMass M enc p y - (Fintype.card (J → K) : ℝ)⁻¹)^2 := by
  classical
  let N : ℝ := Fintype.card (J → K)
  have hn : N ≠ 0 := by dsimp [N]; exact_mod_cast Fintype.card_ne_zero
  have hmass := syndrome_mass_sum M enc p
  have hcenter :
      N * (∑ y, (pqcReferenceSyndromeMass M enc p y - N⁻¹)^2) =
        N * (∑ y, pqcReferenceSyndromeMass M enc p y ^ 2) - 1 := by
    have hsum : (∑ y, (pqcReferenceSyndromeMass M enc p y - N⁻¹)^2) =
        (∑ y, pqcReferenceSyndromeMass M enc p y ^ 2) - 2*N⁻¹ + N*N⁻¹^2 := by
      simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hmass, mul_one,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N]
    rw [hsum]
    field_simp
    ring
  have henergy := reference_gram_energy M enc p χ
  have hdiag := reference_gram_diagonal M enc p χ
  have herase := Finset.sum_erase_add (Finset.univ : Finset (AddChar (J → K) ℂ))
    (fun η => Complex.normSq ((ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η))
    (Finset.mem_univ χ)
  rw [hdiag] at herase
  norm_num only [Complex.normSq_one] at herase
  rw [hcenter]
  dsimp only [N] at *
  linarith

end Phase

/-- Zero is retained in the averaged matrix family: all its secret columns
coincide, so every entry of its actual Gram matrix is one. -/
theorem pqc_reference_zero_matrix_gram
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype J] [DecidableEq J] {D : ℕ}
    (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ η : AddChar (J → K) ℂ) :
    (ensembleGram (pqcReferencePhaseEnsemble (0 : Matrix I J K) enc p)).mat χ η = 1 := by
  classical
  have hz (x : Fin D) : finiteLinearMatrixHash (0 : Matrix I J K) (enc x) = 0 := by
    funext j
    simp [finiteLinearMatrixHash]
  have hcol (x : Fin D) : pqcReferencePhaseEnsemble (0 : Matrix I J K) enc p x η =
      pqcReferencePhaseEnsemble (0 : Matrix I J K) enc p x χ := by
    simp [pqcReferencePhaseEnsemble, hz]
  change (∑ x, star (pqcReferencePhaseEnsemble (0 : Matrix I J K) enc p x χ) *
      pqcReferencePhaseEnsemble (0 : Matrix I J K) enc p x η) = 1
  simp_rw [hcol]
  exact reference_gram_diagonal (0 : Matrix I J K) enc p χ

/-- The normalized reference columns are consumed by the actual existing PGM
instrument, including its complementary outcome. -/
theorem pqc_reference_pgm_born_contract
    {K I J : Type} [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [Fintype J] [DecidableEq J] {D : ℕ}
    (M : Matrix I J K) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (χ : AddChar (J → K) ℂ) :
    let W := pqcReferencePhaseEnsemble M enc p
    let ρ := outerProduct (fun x => W x χ)
    let Jpgm := Instrument.ofPOVM (prettyGoodPOVM W)
    IsDensityOperator ρ ∧ instrumentProb Jpgm ρ none = 0 ∧
      (∀ η, instrumentProb Jpgm ρ (some η) =
        Complex.normSq ((ensembleGram W).sqrt.mat η χ)) ∧
      1-instrumentProb Jpgm ρ (some χ) ≤
        ∑ η ∈ Finset.univ.erase χ, Complex.normSq ((ensembleGram W).mat χ η) := by
  classical
  exact pure_ensemble_pgm_born_and_row_failure _ _ _
    (pqc_reference_phase_normalized M enc p) χ

/-- Complete random-matrix average of the actual PGM failure probability.
The fixed coefficient embedding may include zero; only injectivity is needed.
No matrix rank, point-output uniformity, positive bucket mass, or minimum
Gram-eigenvalue assumption is imposed. -/
theorem pqc_reference_pgm_average_failure
    (K I J : Type) [Field K] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (D : ℕ) (enc : Fin D → I → K) (p : FinDist (Fin D))
    (hinj : Function.Injective enc) (χ : AddChar (J → K) ℂ) :
    finiteHashAverage (fun M : Matrix I J K =>
      1-instrumentProb
        (Instrument.ofPOVM (prettyGoodPOVM (pqcReferencePhaseEnsemble M enc p)))
        (outerProduct (fun x => pqcReferencePhaseEnsemble M enc p x χ)) (some χ)) ≤
      ((Fintype.card (J → K) : ℝ)-1) * ∑ x : Fin D, p.prob x ^ 2 := by
  classical
  let N : ℝ := Fintype.card (J → K)
  let hash : Matrix I J K → Fin D → (J → K) :=
    fun M x => finiteLinearMatrixHash M (enc x)
  have hn : N ≠ 0 := by dsimp [N]; exact_mod_cast Fintype.card_ne_zero
  have hcast (M : Matrix I J K) (y : J → K) :
      weightedHashBucket hash (fun x => (p.prob x : ℂ)) M y =
        (pqcReferenceSyndromeMass M enc p y : ℂ) := by
    simp [weightedHashBucket, hash, pqcReferenceSyndromeMass,
      Complex.ofReal_sum, apply_ite]
  have htotal : (∑ x : Fin D, (p.prob x : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, p.sum_one]
    rfl
  have hnormalizer : (Fintype.card (J → K) : ℂ)⁻¹ = (N⁻¹ : ℝ) := by
    simp [N]
  have hmoment := weighted_hash_centered_second_moment
    (Matrix I J K) (Fin D) (J → K) hash (fun x => (p.prob x : ℂ))
    (fun x y hxy => finite_linear_matrix_hash_collision K I J (enc x) (enc y)
      (fun h => hxy (hinj h)))
  simp_rw [hcast, htotal, hnormalizer, mul_one, ← Complex.ofReal_sub,
    Complex.normSq_ofReal] at hmoment
  simp only [← pow_two] at hmoment
  have hscale (f : Matrix I J K → ℝ) :
      finiteHashAverage (fun M => N*f M) = N*finiteHashAverage f := by
    simp only [finiteHashAverage, ← Finset.mul_sum]
    ring
  have hfactor : N*(1-N⁻¹) = N-1 := by field_simp
  have hrow :
      finiteHashAverage (fun M : Matrix I J K =>
        ∑ η ∈ Finset.univ.erase χ,
          Complex.normSq ((ensembleGram (pqcReferencePhaseEnsemble M enc p)).mat χ η)) =
        (N-1)*∑ x : Fin D, p.prob x ^ 2 := by
    simp_rw [reference_row_centered_energy]
    change finiteHashAverage (fun M => N*∑ y, (pqcReferenceSyndromeMass M enc p y-N⁻¹)^2) = _
    rw [hscale, hmoment, ← mul_assoc, hfactor]
  change _ ≤ (N-1)*∑ x : Fin D, p.prob x ^ 2
  rw [← hrow]
  unfold finiteHashAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro M _
  exact (pqc_reference_pgm_born_contract M enc p χ).2.2.2

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
