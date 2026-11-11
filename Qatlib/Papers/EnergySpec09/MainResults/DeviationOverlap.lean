/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.SuccessProbability

/-!
# Deviations of the initial-state overlap

This module expresses the initial-guess overlap analysis of [WangEtAl2008] using finite quantum
states. The elementary identities `inner_add_right` and `overlap_deviation_decomp` expand a
trial state into a normalized target plus two deviation terms.

The theorem `success_prob_deviation_form` substitutes this expansion into exact phase-estimation
readout under orthonormality and distinct, exactly representable phase labels. The deterministic
limit `exact_guess_success_prob_one` assumes that the trial coefficients select the target
eigenstate exactly.

## Main statements

* `overlap_eq_one_add_deviation`: normalization makes the target's self-overlap equal to one.
* `success_prob_deviation_form`: the readout weight is the squared norm of one plus the two
  deviation overlaps.
* `overlap_eq_one_of_no_deviation` and `exact_guess_success_prob_one`: the corresponding
  unit-overlap and certain-readout limits.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The inner product is additive in its right state argument. -/
theorem inner_add_right (ψ φ₁ φ₂ : QState I) :
    Inner ψ (φ₁ + φ₂) = Inner ψ φ₁ + Inner ψ φ₂ := by
  rw [inner_apply, inner_apply, inner_apply]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The inner product with the zero state in the right argument is zero. -/
@[simp] theorem inner_zero_right (ψ : QState I) : Inner ψ (0 : QState I) = 0 := by
  rw [inner_apply]
  simp

/-- The overlap with a target-plus-deviations state is the sum of the target self-overlap and
the two deviation overlaps. -/
theorem overlap_deviation_decomp {ψ0 ψdev ψp : QState I} :
    Inner ψ0 (ψ0 + ψdev + ψp) = Inner ψ0 ψ0 + Inner ψ0 ψdev + Inner ψ0 ψp := by
  rw [inner_add_right, inner_add_right]

/-- For a normalized target, the target-plus-deviations overlap is one plus the two deviation
overlaps. This supplies the overlap expansion used in the initial-guess analysis of
[WangEtAl2008]. -/
theorem overlap_eq_one_add_deviation {ψ0 ψdev ψp : QState I}
    (hnorm : Normalized ψ0) :
    Inner ψ0 (ψ0 + ψdev + ψp) = 1 + Inner ψ0 ψdev + Inner ψ0 ψp := by
  rw [overlap_deviation_decomp, (normalized_iff_inner_self ψ0).mp hnorm]

/-- Under orthonormality and distinct exact phase labels, a trial state decomposed as the target
plus two deviations has readout weight `‖1 + Inner (φ n) ψdev + Inner (φ n) ψp‖ ^ 2`. This
is the deviation form of the initial-guess overlap relation in [WangEtAl2008]. -/
theorem success_prob_deviation_form {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) {ψdev ψp : QState I}
    (htrial : (∑ i, c i • φ i) = φ n + ψdev + ψp) (hnorm : Normalized (φ n)) :
    MeasureProb (qpeOutput M U (∑ i, c i • φ i))
        ({k n} ×ˢ (Finset.univ : Finset I))
      = ‖1 + Inner (φ n) ψdev + Inner (φ n) ψp‖ ^ 2 := by
  rw [qpe_success_prob_eq_overlap_sq hM U c φ k hOr heig hk n, htrial,
    overlap_eq_one_add_deviation hnorm]

/-- A normalized target has unit overlap with itself plus a zero deviation and a component
orthogonal to it. This gives the no-overlap-error limit of the initial-guess analysis in
[WangEtAl2008]. -/
theorem overlap_eq_one_of_no_deviation {ψ0 ψp : QState I}
    (hnorm : Normalized ψ0) (hp : Inner ψ0 ψp = 0) :
    Inner ψ0 (ψ0 + 0 + ψp) = 1 := by
  rw [overlap_eq_one_add_deviation hnorm, inner_zero_right, hp]
  ring

/-- If the trial coefficients select one orthonormal eigenstate exactly, phase estimation reads
its distinct exact phase label with probability one. This is the deterministic initial-guess
limit of [WangEtAl2008]. -/
theorem exact_guess_success_prob_one {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) (hc : ∀ i, c i = if i = n then 1 else 0) :
    MeasureProb (qpeOutput M U (∑ i, c i • φ i))
        ({k n} ×ˢ (Finset.univ : Finset I)) = 1 := by
  unfold qpeOutput
  rw [tensorState_sum, qpe_success_prob_eq_coeff_sq hM U c φ k hOr heig hk n, hc n,
    if_pos rfl]
  norm_num

end Qatlib.Papers.EnergySpec09.MainResults
