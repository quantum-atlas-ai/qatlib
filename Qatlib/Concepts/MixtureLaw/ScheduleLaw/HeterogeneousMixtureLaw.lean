/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixtureLaw.ScheduleLaw.MixturePowerLawPerturbation
import Qatlib.Concepts.MixtureLaw.ScheduleLaw.MixtureScheduleDefs

/-!
# Perturbing heterogeneous unitary mixture schedules

This module proves trace norm contraction for schedules of unitary mixtures acting with a
reference system. `schedule_law_perturbation` bounds a change of the sampling laws by the sum of
their L1 differences over the schedule, times the input trace norm. Constant schedules reduce to
mixture powers. Unitary mixture channels and trace norms are treated in [Watrous2018].

## Main statements

* `schedule_contraction`: A schedule of unitary mixture maps, extended by an identity reference
  system, does not increase the trace norm of any input operator.
* `schedule_law_perturbation`: Changing the law at each unitary mixture step changes the
  scheduled output by at most the sum of the stepwise L1 law differences times the input trace
  norm.
* `constant_schedule_eq_power`: A schedule with constant sampling law and constant operator
  family equals the corresponding repeated mixture map.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.MixtureLaw.ScheduleLaw
open Matrix
open scoped BigOperators

/-- A schedule of unitary mixture maps, extended by an identity reference system, does not
increase the trace norm of any input operator. -/
theorem schedule_contraction :
    ∀ (J : Type) [Fintype J] [DecidableEq J] (D r n : ℕ)
    (d : ℕ → FinDist J) (U : ℕ → J → Operator D),
    (∀ i j, U i j ∈ Matrix.unitaryGroup (Fin D) ℂ) →
    ∀ (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (referenceMixtureSchedule d U r n ρ) ≤ Matrix.traceNorm ρ := by
  intro J _ _ D r n d U hU ρ
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (finite_reference_mixture_contraction (d n) (U n) r
      (referenceMixtureSchedule d U r n ρ) (hU n)).trans ih

/-- Changing the law at each unitary mixture step changes the scheduled output by at most the
sum of the stepwise L1 law differences times the input trace norm. -/
theorem schedule_law_perturbation
    (J : Type) [Fintype J] [DecidableEq J] (D r n : ℕ)
    (d e : ℕ → FinDist J) (U : ℕ → J → Operator D)
    (hU : ∀ i j, U i j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixtureSchedule d U r n ρ -
      referenceMixtureSchedule e U r n ρ) ≤
      (∑ i ∈ Finset.range n, ∑ j, |(d i).prob j - (e i).prob j|) * Matrix.traceNorm ρ := by
  induction n with
  | zero => simp [referenceMixtureSchedule]
  | succ n ih =>
    have hsplit : referenceMixture (d n) (U n) r (referenceMixtureSchedule d U r n ρ) -
        referenceMixture (e n) (U n) r (referenceMixtureSchedule e U r n ρ) =
        referenceMixture (d n) (U n) r
          (referenceMixtureSchedule d U r n ρ - referenceMixtureSchedule e U r n ρ) +
        (referenceMixture (d n) (U n) r (referenceMixtureSchedule e U r n ρ) -
          referenceMixture (e n) (U n) r (referenceMixtureSchedule e U r n ρ)) := by
      rw [referenceMixture_sub, sub_add_sub_cancel]
    have hfirst := (finite_reference_mixture_contraction (d n) (U n) r
      (referenceMixtureSchedule d U r n ρ - referenceMixtureSchedule e U r n ρ)
      (hU n)).trans ih
    have hsecond := (referenceMixture_law_perturbation (d n) (e n) (U n) (hU n) r
      (referenceMixtureSchedule e U r n ρ)).trans
        (mul_le_mul_of_nonneg_left (schedule_contraction J D r n e U hU ρ)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    simp only [referenceMixtureSchedule]
    rw [hsplit]
    exact (Matrix.traceNorm_add_le _ _).trans
      ((add_le_add hfirst hsecond).trans_eq (by rw [Finset.sum_range_succ]; ring))

/-- A schedule with constant sampling law and constant operator family equals the corresponding
repeated mixture map. -/
theorem constant_schedule_eq_power
    (J : Type) [Fintype J] [DecidableEq J] (D r n : ℕ)
    (d : FinDist J) (U : J → Operator D)
    (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    referenceMixtureSchedule (fun _ => d) (fun _ => U) r n ρ =
      referenceMixturePower d U r n ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change referenceMixture d U r
      (referenceMixtureSchedule (fun _ => d) (fun _ => U) r n ρ) = _
    rw [ih]
    exact (Function.iterate_succ_apply' (referenceMixture d U r) n ρ).symm

/-- The heterogeneous schedule perturbation estimate and the identification of constant
schedules with mixture powers hold together. -/
theorem schedule_law_error :
    (∀ (J : Type) [Fintype J] [DecidableEq J] (D r n : ℕ)
      (d e : ℕ → FinDist J) (U : ℕ → J → Operator D),
      (∀ i j, U i j ∈ Matrix.unitaryGroup (Fin D) ℂ) →
      ∀ (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
        Matrix.traceNorm (referenceMixtureSchedule d U r n ρ -
          referenceMixtureSchedule e U r n ρ) ≤
          (∑ i ∈ Finset.range n, ∑ j, |(d i).prob j - (e i).prob j|) * Matrix.traceNorm ρ) ∧
    (∀ (J : Type) [Fintype J] [DecidableEq J] (D r n : ℕ)
      (d : FinDist J) (U : J → Operator D)
      (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
        referenceMixtureSchedule (fun _ => d) (fun _ => U) r n ρ =
          referenceMixturePower d U r n ρ) :=
  ⟨schedule_law_perturbation, constant_schedule_eq_power⟩

end Qatlib.Concepts.MixtureLaw.ScheduleLaw
