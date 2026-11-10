/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwRecordStatistics
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwSpectralMixture
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors
open Matrix Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped BigOperators Classical
set_option warningAsError false
noncomputable section
set_option linter.unusedSectionVars false

variable {H W : Type} [Fintype H] [DecidableEq H] [Fintype W] [DecidableEq W]

theorem frontier1 (U : Matrix H H ℂ) (S : Finset H) (E : Matrix H W ℂ)
    (hU : U ∈ unitaryGroup H ℂ) (hE : Eᴴ * E = 1) :
    let P := pulledAccept U S
    let Q := cleanProjector E
    ∃ (A : Matrix H (CSProjectorSupport Q (cleanProjector_projector E hE)) ℂ)
      (t : CSProjectorSupport Q (cleanProjector_projector E hE) → ℝ),
      (∀ j, t j ∈ Set.Icc 0 1) ∧ IsIsometry A ∧ A * Aᴴ = Q ∧
      (∀ (w : QState W) (z : List Bool),
        MeasureProb (alternatingState P Q true (outcomeRecord true z) (E *ᵥ w)) Finset.univ =
          ∑ j, ‖(Aᴴ *ᵥ (E *ᵥ w)) j‖ ^ 2 * recordWeight (t j) z) ∧
      (∀ ψ : QState H, ∃ w : QState W, Q *ᵥ ψ = E *ᵥ w) := by
  (try dsimp only)
  let P := pulledAccept U S
  let Q := cleanProjector E
  have hP := pulledAccept_projector U S hU
  have hQ := cleanProjector_projector E hE
  obtain ⟨A, t, ht, hA, hAQ, hdiag⟩ := cs_projector_compressed_eigenframe Q P hQ hP
  refine ⟨A, t, ht, hA, hAQ, ?_, clean_output E⟩
  intro w z
  rw [alternating_eq_branch, agreement_outcome]
  exact clean_record_mixture Q P hQ hP A t hA hAQ hdiag (E *ᵥ w) (clean_embed E hE w) z

theorem clean_event_mixture {J : Type} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (n : ℕ) (event : (Fin n → Bool) → Prop) :
    recordEvent P Q ψ n event =
      ∑ j, ‖(Aᴴ *ᵥ ψ) j‖ ^ 2 * eventMass (recordLaw n (t j) (ht j)) event := by
  unfold recordEvent
  simp_rw [clean_record_mixture Q P hQ hP A t hA hAQ hdiag ψ hψ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  unfold eventMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [recordWeight_ofFn]
  rfl

theorem clean_record_total {J : Type} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ) (n : ℕ) :
    recordEvent P Q ψ n (fun _ => True) = 1 := by
  rw [clean_event_mixture Q P hQ hP A t ht hA hAQ hdiag ψ hψ]
  simp only [eventMass, Finset.filter_true, (recordLaw n _ _).sum_one, mul_one]
  exact (clean_spectral_weights_sum_one Q A hA hAQ ψ hψ hnψ).2

theorem clean_event_bound {J : Type} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ) (n : ℕ)
    (event : (Fin n → Bool) → Prop) (B : ℝ)
    (hB : ∀ j, eventMass (recordLaw n (t j) (ht j)) event ≤ B) :
    recordEvent P Q ψ n event ≤ B := by
  rw [clean_event_mixture Q P hQ hP A t ht hA hAQ hdiag ψ hψ]
  calc
    _ ≤ ∑ j, ‖(Aᴴ *ᵥ ψ) j‖ ^ 2 * B :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hB j) (sq_nonneg _)
    _ = B := by
      rw [← Finset.sum_mul, (clean_spectral_weights_sum_one Q A hA hAQ ψ hψ hnψ).2,
        one_mul]

theorem clean_threshold_soundness {J : Type} [Fintype J] [DecidableEq J]
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ)
    (n : ℕ) (hn : 0 < n) (threshold d : ℝ) (hd : 0 < d)
    (hgap : ∀ j, t j + d ≤ threshold) :
    recordEvent P Q ψ n (fun z => n * threshold ≤ agreements z) ≤
      2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  apply clean_event_bound Q P hQ hP A t ht hA hAQ hdiag ψ hψ hnψ
  intro j
  obtain ⟨hv, hfix, heig⟩ := spectral_frame_columns Q P A t hA hAQ hdiag
  have hvj : Normalized (fun h => A h j) :=
    (normalized_iff_inner_self _).mpr (by simpa using! hv j j)
  rw [← record_event_probability P Q hP hQ (fun h => A h j) (t j) (ht j)
    (hfix j) (heig j) hvj]
  exact threshold_soundness P Q hP hQ _ (t j) (ht j) (hfix j) (heig j) hvj
    n hn threshold d hd (hgap j)

variable {J : Type} [Fintype J] [DecidableEq J]

theorem clean_single_accept_mixture
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) :
    MeasureProb (P *ᵥ ψ) Finset.univ = ∑ j, ‖(Aᴴ *ᵥ ψ) j‖ ^ 2 * t j := by
  simpa [branchState, recordWeight] using!
    clean_record_mixture Q P hQ hP A t hA hAQ hdiag ψ hψ [true]

theorem clean_yes_spectral_index
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ)
    (a : ℝ) (haccept : a ≤ MeasureProb (P *ᵥ ψ) Finset.univ) :
    ∃ j : J, a ≤ t j := by
  have hweights := clean_spectral_weights_sum_one Q A hA hAQ ψ hψ hnψ
  have hJ : (Finset.univ : Finset J).Nonempty := by
    by_contra hempty
    have hu := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsum := hweights.2
    rw [hu, Finset.sum_empty] at hsum
    norm_num at hsum
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ t hJ
  refine ⟨j, haccept.trans ?_⟩
  rw [clean_single_accept_mixture Q P hQ hP A t hA hAQ hdiag ψ hψ]
  calc
    _ ≤ ∑ i, ‖(Aᴴ *ᵥ ψ) i‖ ^ 2 * t j := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ i)) (hweights.1 i)
    _ = t j := by rw [← Finset.sum_mul, hweights.2, one_mul]

theorem clean_yes_eigen_witness
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ)
    (a : ℝ) (haccept : a ≤ MeasureProb (P *ᵥ ψ) Finset.univ) :
    ∃ (φ : QState H) (p : ℝ), p ∈ Set.Icc 0 1 ∧ a ≤ p ∧
      Normalized φ ∧ Q *ᵥ φ = φ ∧ Q *ᵥ (P *ᵥ φ) = (p : ℂ) • φ := by
  obtain ⟨j, hj⟩ := clean_yes_spectral_index Q P hQ hP A t hA hAQ hdiag
    ψ hψ hnψ a haccept
  obtain ⟨hv, hfix, heig⟩ := spectral_frame_columns Q P A t hA hAQ hdiag
  refine ⟨(fun h => A h j), t j, ht j, hj, ?_, hfix j, heig j⟩
  exact (normalized_iff_inner_self _).mpr (by simpa using! hv j j)

theorem clean_no_spectral_bound
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (b : ℝ) (hno : ∀ φ : QState H, Normalized φ → Q *ᵥ φ = φ →
      MeasureProb (P *ᵥ φ) Finset.univ ≤ b) :
    ∀ j, t j ≤ b := by
  obtain ⟨hv, hfix, heig⟩ := spectral_frame_columns Q P A t hA hAQ hdiag
  intro j
  let φ : QState H := fun h => A h j
  have hnφ : Normalized φ :=
    (normalized_iff_inner_self _).mpr (by simpa [φ] using! hv j j)
  have hm : MeasureProb φ Finset.univ = 1 := hnφ
  have hsingle := same_mass Q P hQ hP φ (t j) (hfix j) (heig j)
  rw [hm, mul_one] at hsingle
  rw [← hsingle]
  exact hno φ hnφ (hfix j)

theorem clean_threshold_soundness_of_promise
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (b : ℝ) (hno : ∀ φ : QState H, Normalized φ → Q *ᵥ φ = φ →
      MeasureProb (P *ᵥ φ) Finset.univ ≤ b)
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ)
    (n : ℕ) (hn : 0 < n) (threshold d : ℝ) (hd : 0 < d)
    (hgap : b + d ≤ threshold) :
    recordEvent P Q ψ n (fun z => n * threshold ≤ agreements z) ≤
      2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  apply clean_threshold_soundness Q P hQ hP A t ht hA hAQ hdiag ψ hψ hnψ
    n hn threshold d hd
  intro j
  linarith [clean_no_spectral_bound Q P hQ hP A t hA hAQ hdiag b hno j]

theorem clean_threshold_completeness_of_promise
    (Q P : Matrix H H ℂ) (hQ : IsOrthogonalProjector Q) (hP : IsOrthogonalProjector P)
    (A : Matrix H J ℂ) (t : J → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1)
    (hA : IsIsometry A) (hAQ : A * Aᴴ = Q)
    (hdiag : Aᴴ * P * A = diagonal (fun j => (t j : ℂ)))
    (ψ : QState H) (hψ : Q *ᵥ ψ = ψ) (hnψ : Normalized ψ)
    (a : ℝ) (haccept : a ≤ MeasureProb (P *ᵥ ψ) Finset.univ)
    (n : ℕ) (hn : 0 < n) (threshold d : ℝ) (hd : 0 < d)
    (hgap : threshold + d ≤ a) :
    ∃ φ : QState H, Normalized φ ∧ Q *ᵥ φ = φ ∧
      recordEvent P Q φ n (fun z => agreements z < n * threshold) ≤
        2 * Real.exp (-2 * (n * d) ^ 2 / n) := by
  obtain ⟨φ, p, hp, hap, hnφ, hfix, heig⟩ := clean_yes_eigen_witness
    Q P hQ hP A t ht hA hAQ hdiag ψ hψ hnψ a haccept
  exact ⟨φ, hnφ, hfix, threshold_completeness P Q hP hQ φ p hp hfix heig hnφ
    n hn threshold d hd (hgap.trans hap)⟩

end
end Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors
