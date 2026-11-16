/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervSpeedup20.MainResults.Definitions

@[expose] public section


/-!
# Lemma 14 — reduction to a noisy halfspace learning problem

Fixed source: arXiv:2010.02174 (v1, 5 Oct 2020), Lemma 14, p. 20–21.

The concept-class learning problem of `C` is reduced to the following noisy
halfspace learning problem, which does not depend on the concept:

1. data space `X ⊆ R^{4^n+1}` with `‖x‖₂ = 1` for all `x`, each with a label
   `y ∈ {−1, +1}`;
2. separability: there is a unit-norm hyperplane `w` with
   `Pr_{x∼X}[y⟨w,x⟩ ≥ Δ/√(8+2Δ²)] = 1 − Δ` (eq. (D14));
3. bounded distance: `|y⟨w,x⟩| ≤ Δ/√(8+2Δ²)` for every `x` (eq. (D15));
4. noisy kernel `K' = K + e` with `e_ij ∈ [−1/2,1/2]`, `E[e_ij] = 0` and
   `Var[e_ij] ≤ 1/R`, `R` the number of measurement shots.

The four properties are the fields of `NoisyHalfspaceProblem`; this file proves
the elementary facts used by the reduction (positivity of the margin, the
normalisation of the ground-truth hyperplane of Definition 15) and records the
construction of the problem itself in the audit of `source_lemma14`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SupervSpeedup20.MainResults

open Finset DlogWorld
open scoped BigOperators

namespace DlogWorld

/-- The margin `Δ/√(8+2Δ²)` of Lemma 14, eqs. (D14)–(D15). -/
def marginScale (Δ : ℝ) : ℝ := Δ / Real.sqrt (8 + 2 * Δ ^ 2)

/-- The Lemma 14 margin is nonnegative for `Δ ≥ 0`. -/
theorem marginScale_nonneg {Δ : ℝ} (hΔ : 0 ≤ Δ) : 0 ≤ marginScale Δ := by
  unfold marginScale
  positivity

/-- The Lemma 14 margin is positive for `Δ > 0`. -/
theorem marginScale_pos {Δ : ℝ} (hΔ : 0 < Δ) : 0 < marginScale Δ := by
  unfold marginScale
  positivity

/-- **Lemma 14, property 1 (source p. 20).**  The data vectors of a
`NoisyHalfspaceProblem` have unit norm. -/
theorem lemma14_unit (P : NoisyHalfspaceProblem) :
    ∀ y, (∑ j, P.vec y j ^ 2) = 1 := P.unit

/-- **Lemma 14, property 3 (source p. 21, eq. (D15)).**  Every data point is
within distance `Δ/√(8+2Δ²)` of the ground-truth hyperplane. -/
theorem lemma14_bounded (P : NoisyHalfspaceProblem) :
    ∀ y, |labelOf (P.lab y) * (∑ j, P.w j * P.vec y j)| ≤ marginScale P.Δ :=
  fun y => by simpa [marginScale] using P.bounded y

/-- **Lemma 14, property 4 (source p. 21).**  The kernel-noise variance obeys
`Var[e] ≤ 1/R` with `R` measurement shots. -/
theorem lemma14_noise (P : NoisyHalfspaceProblem) :
    P.noiseBound ≤ (P.shots : ℝ)⁻¹ := P.noiseVariance

/-- **Normalisation of the ground-truth hyperplane (source p. 21).**  Definition
15 introduces the unnormalised hyperplane `w*` with `‖w*‖₂ = O(Δ⁻¹)`; rescaling
by its norm produces the unit-norm hyperplane required by property 2 of
Lemma 14. -/
theorem unit_norm_of_rescale {d : ℕ} (w : Fin d → ℝ)
    (hw : 0 < ∑ j, w j ^ 2) :
    (∑ j, (w j / Real.sqrt (∑ j, w j ^ 2)) ^ 2) = 1 := by
  have hsq : (Real.sqrt (∑ j, w j ^ 2)) ^ 2 = ∑ j, w j ^ 2 :=
    Real.sq_sqrt hw.le
  calc ∑ j, (w j / Real.sqrt (∑ j, w j ^ 2)) ^ 2
      = ∑ j, w j ^ 2 / (Real.sqrt (∑ j, w j ^ 2)) ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [div_pow]
    _ = (∑ j, w j ^ 2) / (Real.sqrt (∑ j, w j ^ 2)) ^ 2 :=
        (Finset.sum_div _ _ _).symm
    _ = 1 := by
        rw [hsq]
        exact div_self hw.ne'

end DlogWorld

end Qatlib.Papers.SupervSpeedup20.MainResults
