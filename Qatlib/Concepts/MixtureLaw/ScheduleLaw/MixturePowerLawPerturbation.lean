/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError

/-!
# Sampling law perturbations of mixture powers

This module controls changes in unitary mixture maps when their finite sampling law changes.
`referenceMixture_law_perturbation` bounds one step by the L1 law difference times the input
trace norm, and `referenceMixturePower_law_perturbation` multiplies this bound by the number of
steps. The reference system is retained throughout, in the channel framework of [Watrous2018].

## Main statements

* `referenceMixture_law_perturbation`: For unitary branches, the trace norm difference between
  reference extended mixtures with laws `d` and `e` is at most their L1 distance times the input
  trace norm.
* `referenceMixturePower_law_perturbation`: For unitary branches, changing the sampling law in
  an `n` step mixture power costs at most `n` times the L1 law distance times the input trace
  norm.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Concepts.MixtureLaw.ScheduleLaw
open Matrix
open scoped Classical BigOperators

/-- The trace norm of a finite sum of complex square matrices is at most the sum of their trace
norms. -/
private theorem law_traceNorm_sum_le {J N : Type} [Fintype J] [DecidableEq J] [Fintype N]
    (s : Finset J) (f : J → Matrix N N ℂ) :
    Matrix.traceNorm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, Matrix.traceNorm (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [Matrix.traceNorm_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (Matrix.traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-- For unitary branches, the trace norm difference between reference extended mixtures with
laws `d` and `e` is at most their L1 distance times the input trace norm. -/
theorem referenceMixture_law_perturbation {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d e : FinDist J) (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (r : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture d U r ρ-referenceMixture e U r ρ) ≤
      (∑ j, |d.prob j-e.prob j|)*Matrix.traceNorm ρ := by
  rw [referenceMixture_apply, referenceMixture_apply, ← Finset.sum_sub_distrib]
  simp only [← sub_smul, ← Complex.ofReal_sub]
  refine (law_traceNorm_sum_le _ _).trans ?_
  have he (j : J) : Matrix.traceNorm (((d.prob j-e.prob j : ℝ) : ℂ) •
      (TensorGate (U j) (1 : Operator r)*ρ*(TensorGate (U j) (1 : Operator r))ᴴ)) =
      |d.prob j-e.prob j| * Matrix.traceNorm ρ := by
    rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      finite_reference_unitary_traceNorm (U j) r ρ (hU j)]
  simp_rw [he]
  rw [← Finset.sum_mul]

/-- For unitary branches, changing the sampling law in an `n` step mixture power costs at most
`n` times the L1 law distance times the input trace norm. -/
theorem referenceMixturePower_law_perturbation {J : Type} [Fintype J] [DecidableEq J] {D : ℕ}
    (d e : FinDist J) (U : J → Operator D) (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (r n : ℕ) (ρ : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixturePower d U r n ρ-referenceMixturePower e U r n ρ) ≤
      (n : ℝ)*(∑ j, |d.prob j-e.prob j|)*Matrix.traceNorm ρ := by
  induction n with
  | zero => simp [referenceMixturePower]
  | succ n ih =>
    have hd : referenceMixturePower d U r (n+1) ρ =
        referenceMixture d U r (referenceMixturePower d U r n ρ) :=
      Function.iterate_succ_apply' (referenceMixture d U r) n ρ
    have he : referenceMixturePower e U r (n+1) ρ =
        referenceMixture e U r (referenceMixturePower e U r n ρ) :=
      Function.iterate_succ_apply' (referenceMixture e U r) n ρ
    have hsplit : referenceMixture d U r (referenceMixturePower d U r n ρ)-
        referenceMixture e U r (referenceMixturePower e U r n ρ) =
        referenceMixture d U r (referenceMixturePower d U r n ρ-referenceMixturePower e U r n ρ)+
        (referenceMixture d U r (referenceMixturePower e U r n ρ)-
          referenceMixture e U r (referenceMixturePower e U r n ρ)) := by
      rw [referenceMixture_sub, sub_add_sub_cancel]
    have hfirst := (finite_reference_mixture_contraction d U r
      (referenceMixturePower d U r n ρ-referenceMixturePower e U r n ρ) hU).trans ih
    have hsecond := (referenceMixture_law_perturbation d e U hU r
      (referenceMixturePower e U r n ρ)).trans
        (mul_le_mul_of_nonneg_left (referenceMixturePower_contraction e U r n ρ hU)
          (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    rw [hd, he, hsplit]
    exact (Matrix.traceNorm_add_le _ _).trans
        ((add_le_add hfirst hsecond).trans_eq (by push_cast; ring))

end Qatlib.Concepts.MixtureLaw.ScheduleLaw
