/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SublinearPart22.MainResults.PhaseEstimationDistribution
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# The phase-estimation distribution in Equation (13)

Appendix A of arXiv:2207.08643v2 invokes phase estimation at power-of-two
precision. The finite Fourier model of its Born masses makes sense at every
positive precision, including exact grid phases where the sine quotient has
a removable singularity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation
open Qatlib.Papers.SublinearPart22.MainResults

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- Equation (13) agrees with the BHMT Born mass at every outcome, including
circular distance zero. -/
theorem qpeOutcomeProb_eq_outcomeMass (t : ℕ) (ht : 0 < t) (θ : ℝ) (i : Fin t) :
    qpeOutcomeProb t θ i = bhmt11OutcomeMass t θ i := by
  let phase := (i.val : ℝ) / (t : ℝ)
  by_cases hd : bhmt11CircleDist θ phase = 0
  · rw [qpeOutcomeProb, ite_eq_left hd,
      bhmt_phase_estimation_theorem11_mass_expSum t θ ht i,
      bhmt_phase_estimation_theorem11_expSum_distance t phase θ,
      bhmt_phase_estimation_theorem11_distance_symm phase θ, hd,
      bhmt_phase_estimation_theorem11_expSum_zero, Complex.norm_natCast,
      div_self (by positivity : (t : ℝ) ^ 2 ≠ 0)]
  · exact qpeOutcomeProb_eq_outcomeMass_of_pos t θ i ht
      (lt_of_le_of_ne (bhmt_phase_estimation_theorem11_distance_bounds θ phase).1 (Ne.symm hd))

/-- Equation (13) has total mass one over the full outcome register. -/
theorem qpeOutcomeProb_sum_eq_one (t : ℕ) (ht : 0 < t) (θ : ℝ) :
    ∑ i : Fin t, qpeOutcomeProb t θ i = 1 := by
  simp only [qpeOutcomeProb_eq_outcomeMass t ht θ]
  exact bhmt_phase_estimation_theorem11_normalization t θ ht

/-- The finite probability mass function of the outcome index in Lemma A.1. -/
def qpeProbabilityLaw (t : ℕ) (ht : 0 < t) (θ : ℝ) : PMF (Fin t) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (qpeOutcomeProb t θ i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      rw [qpeOutcomeProb_eq_outcomeMass t ht θ i]
      exact bhmt_phase_estimation_theorem11_mass_nonneg t θ i),
      qpeOutcomeProb_sum_eq_one t ht θ, ENNReal.ofReal_one])

/-- Each mass of the law, viewed as a real, is the value of Equation (13). -/
theorem qpeProbabilityLaw_real (t : ℕ) (ht : 0 < t) (θ : ℝ) (i : Fin t) :
    (qpeProbabilityLaw t ht θ i).toReal = qpeOutcomeProb t θ i := by
  rw [qpeProbabilityLaw, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  rw [qpeOutcomeProb_eq_outcomeMass t ht θ i]
  exact bhmt_phase_estimation_theorem11_mass_nonneg t θ i

/-- Corollary A.2 bounds the point masses of the normalized outcome law. -/
theorem corollaryA2_qpe_law_bounds (t : ℕ) (ht : 8 ≤ t) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (i : Fin t) :
    let Δ := bhmt11CircleDist θ ((i.val : ℝ) / (t : ℝ))
    let p := (qpeProbabilityLaw t (by omega) θ i).toReal
    (Δ ≤ 5 / (8 * (t : ℝ)) → (0.22 : ℝ) ≤ p) ∧
    (1 / (t : ℝ) ≤ Δ → p ≤ 0.11) := by
  simpa only [qpeProbabilityLaw_real] using corollaryA2_qpe_probability_bounds t ht θ hθ0 hθ1 i

end Qatlib.Papers.SublinearPart22.MainResults
