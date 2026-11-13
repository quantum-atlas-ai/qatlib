/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Perturbation bounds for postmeasurement states

This module relates `Collapse` and `PostMeasure` to Euclidean projection and normalization, as
used in the measurement formalism of [Watrous2018]. The selected component has norm equal to the
square root of its measurement probability, and selecting a common event does not increase the
distance between unnormalized states.

The theorem `postMeasure_error_of_gap` bounds the distance between normalized postmeasurement
states by `2 * ε / Real.sqrt (MeasureProb ψ S)` when the original error is at most `ε` and this
is smaller than the reference selected norm. The same estimate holds after applying a common
unitary gate.

## Main statements

* `norm_toEuclidean_collapse_eq_sqrt_measureProb`: selected norm and measurement probability.
* `toEuclidean_postMeasure_eq_normalize`: postmeasurement state as Euclidean normalization.
* `postMeasure_error_of_gap`: positivity and normalized state error under a strict gap.
* `postMeasure_applyGate_error_of_gap`: the corresponding bound after a unitary gate.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.SketchArith.GramAction

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- The Euclidean realization of a difference of states is the difference of their Euclidean
realizations. -/
private theorem toEuclidean_sub (ψ φ : QState I) :
    toEuclidean_fromVec (ψ - φ) = toEuclidean_fromVec ψ - toEuclidean_fromVec φ := by
  simp only [toEuclidean_fromVec, WithLp.toLp_sub]

/-- Taking the difference of two states selected on the same event equals selecting their
difference. -/
private theorem collapse_sub (ψ φ : QState I) (S : Finset I) :
    Collapse φ S - Collapse ψ S = Collapse (φ - ψ) S := by
  funext i
  simp only [collapse_apply, Pi.sub_apply]
  split_ifs <;> simp

/-- The Euclidean norm of the component selected by `S` equals the square root of `MeasureProb ψ
S`. -/
theorem norm_toEuclidean_collapse_eq_sqrt_measureProb
    (ψ : QState I) (S : Finset I) :
    ‖toEuclidean_fromVec (Collapse ψ S)‖ = Real.sqrt (MeasureProb ψ S) := by
  rw [← sum_normSq_collapse ψ S, ← norm_toEuclidean_fromVec_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

/-- Selecting the same event in two states does not increase their Euclidean distance. -/
theorem norm_toEuclidean_collapse_sub_le
    (ψ φ : QState I) (S : Finset I) :
    ‖toEuclidean_fromVec (Collapse φ S - Collapse ψ S)‖ ≤
      ‖toEuclidean_fromVec (φ - ψ)‖ := by
  rw [collapse_sub]
  exact norm_toEuclidean_collapse_le (φ - ψ) S

/-- The Euclidean realization of `PostMeasure ψ S` is the normalization of the selected
component `Collapse ψ S`. -/
theorem toEuclidean_postMeasure_eq_normalize
    (ψ : QState I) (S : Finset I) :
    toEuclidean_fromVec (PostMeasure ψ S) =
      NormedSpace.normalize (toEuclidean_fromVec (Collapse ψ S)) := by
  have hmass : MeasureProb (Collapse ψ S) Finset.univ = MeasureProb ψ S := by
    simpa only [MeasureProb, BornProb] using sum_normSq_collapse ψ S
  have hstate : PostMeasure (Collapse ψ S) Finset.univ = PostMeasure ψ S := by
    funext i
    simp [PostMeasure, hmass, collapse_apply]
  change Qatlib.Concepts.BlockEncoding.Postselection.stateVector (PostMeasure ψ S) =
    NormedSpace.normalize
      (Qatlib.Concepts.BlockEncoding.Postselection.stateVector (Collapse ψ S))
  rw [← hstate]
  exact Qatlib.Concepts.BlockEncoding.Postselection.stateVector_postMeasure_univ (Collapse ψ S)

/-- If the state error is at most `ε` and `ε` is smaller than the reference selected norm, the
perturbed event has positive probability and the postmeasurement state error is at most `2 *
ε / Real.sqrt (MeasureProb ψ S)`. -/
theorem postMeasure_error_of_gap
    (ψ φ : QState I) (S : Finset I) {ε : ℝ}
    (hclose : ‖toEuclidean_fromVec (φ - ψ)‖ ≤ ε)
    (hgap : ε < Real.sqrt (MeasureProb ψ S)) :
    0 < MeasureProb φ S ∧
      ‖toEuclidean_fromVec (PostMeasure φ S - PostMeasure ψ S)‖ ≤
        2 * ε / Real.sqrt (MeasureProb ψ S) := by
  have hselected :
      ‖toEuclidean_fromVec (Collapse φ S) - toEuclidean_fromVec (Collapse ψ S)‖ ≤ ε := by
    rw [← toEuclidean_sub]
    exact (norm_toEuclidean_collapse_sub_le ψ φ S).trans hclose
  have hselectedGap : ε < ‖toEuclidean_fromVec (Collapse ψ S)‖ := by
    rw [norm_toEuclidean_collapse_eq_sqrt_measureProb]
    exact hgap
  obtain ⟨hne, herr⟩ :=
      Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap hselected hselectedGap
  have hnorm : 0 < ‖toEuclidean_fromVec (Collapse φ S)‖ := norm_pos_iff.mpr hne
  rw [norm_toEuclidean_collapse_eq_sqrt_measureProb] at hnorm
  refine ⟨Real.sqrt_pos.mp hnorm, ?_⟩
  rw [toEuclidean_sub, toEuclidean_postMeasure_eq_normalize,
    toEuclidean_postMeasure_eq_normalize]
  rwa [norm_toEuclidean_collapse_eq_sqrt_measureProb] at herr

/-- After a common unitary gate, a state perturbation of size at most `ε` gives positive
selected probability and postmeasurement error at most twice `ε` divided by the reference
selected norm, provided the stated strict gap holds. -/
theorem postMeasure_applyGate_error_of_gap
    (U : Matrix I I ℂ) (ψ φ : QState I) (S : Finset I) {ε : ℝ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (hclose : ‖toEuclidean_fromVec (φ - ψ)‖ ≤ ε)
    (hgap : ε < Real.sqrt (MeasureProb (ApplyGate U ψ) S)) :
    0 < MeasureProb (ApplyGate U φ) S ∧
      ‖toEuclidean_fromVec
        (PostMeasure (ApplyGate U φ) S - PostMeasure (ApplyGate U ψ) S)‖ ≤
        2 * ε / Real.sqrt (MeasureProb (ApplyGate U ψ) S) := by
  have hlinear : ApplyGate U φ - ApplyGate U ψ = ApplyGate U (φ - ψ) := by
    exact (Matrix.mulVec_sub U φ ψ).symm
  have hnorm : ‖toEuclidean_fromVec (ApplyGate U φ - ApplyGate U ψ)‖ =
      ‖toEuclidean_fromVec (φ - ψ)‖ := by
    rw [hlinear, ← toEuclideanCLM_applyGate U (φ - ψ)]
    exact norm_toEuclideanCLM_of_mem_unitaryGroup hU _
  exact postMeasure_error_of_gap (ApplyGate U ψ) (ApplyGate U φ) S
    (hnorm ▸ hclose) hgap

end Qatlib.Concepts.SketchArith.GramAction
