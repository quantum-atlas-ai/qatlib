/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Discarded measurements and phase-register marginals

Summing over an unrecorded measurement on one register preserves event probabilities on the
other register. The identities cover computational and arbitrary unitary bases, an additional
linear phase-register gate, and total mass for a normalized input. The mathematical context is
[BrassardHoyerTapp1998Counting].

## Main statements

* `nonselective_before_phase_gate`: After any linear gate on the second register, summing over a
  unitary-basis measurement of the first register preserves the second-register event mass.
* `nonselective_total_one`: For a normalized bipartite state, summing all slice masses after a
  unitary first-register basis change gives one.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.NonSelectiveMeasurement

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

omit [DecidableEq S] [Fintype A] [DecidableEq A] in

/-- Summing the measurement masses of all computational-basis slices of the first register gives
the second-register marginal mass. See [BrassardHoyerTapp1998Counting]. -/
theorem nonselective_computational_marginal (ψ : QState (S × A)) (T : Finset A) :
    (∑ s, MeasureProb (fun a => ψ (s, a)) T)
      = MeasureProb ψ (Finset.univ ×ˢ T) := by
  classical
  unfold MeasureProb BornProb
  rw [Finset.sum_product]

omit [Fintype A] [DecidableEq A] in

/-- A unitary change of measurement basis on the first register preserves the summed
second-register event mass. See [BrassardHoyerTapp1998Counting]. -/
theorem nonselective_basis_marginal (U : Matrix S S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) (ψ : QState (S × A)) (T : Finset A) :
    (∑ k, MeasureProb (fun a => ∑ s, U k s * ψ (s, a)) T)
      = MeasureProb ψ (Finset.univ ×ˢ T) := by
  classical
  unfold MeasureProb BornProb
  have hL : (∑ k, ∑ a ∈ T, ‖∑ s, U k s * ψ (s, a)‖ ^ 2)
      = ∑ a ∈ T, ∑ k, ‖∑ s, U k s * ψ (s, a)‖ ^ 2 :=
    Finset.sum_comm
  have hR : (∑ p ∈ Finset.univ ×ˢ T, ‖ψ p‖ ^ 2)
      = ∑ a ∈ T, ∑ s ∈ Finset.univ, ‖ψ (s, a)‖ ^ 2 := by
    rw [Finset.sum_product, Finset.sum_comm]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hparseval := sum_normSq_mulVec_of_mem_unitaryGroup (U := U) hU (fun s => ψ (s, a))
  simpa [Matrix.mulVec, dotProduct, Complex.normSq_eq_norm_sq] using hparseval

/-- After any linear gate on the second register, summing over a unitary-basis measurement of
the first register preserves the second-register event mass. See
[BrassardHoyerTapp1998Counting]. -/
theorem nonselective_before_phase_gate (U : Matrix S S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) (Q : Matrix A A ℂ) (ψ : QState (S × A))
    (T : Finset A) :
    (∑ k, MeasureProb (fun a => ∑ s, U k s * (∑ a', Q a a' * ψ (s, a'))) T)
      = MeasureProb (fun p : S × A => ∑ a', Q p.2 a' * ψ (p.1, a'))
          (Finset.univ ×ˢ T) :=
  nonselective_basis_marginal U hU (fun p => ∑ a', Q p.2 a' * ψ (p.1, a')) T

/-- For a normalized bipartite state, summing all slice masses after a unitary first-register
basis change gives one. -/
theorem nonselective_total_one (U : Matrix S S ℂ)
    (hU : U ∈ Matrix.unitaryGroup S ℂ) {ψ : QState (S × A)} (hψ : Normalized ψ) :
    (∑ k, MeasureProb (fun a => ∑ s, U k s * ψ (s, a)) Finset.univ) = 1 := by
  rw [nonselective_basis_marginal U hU ψ Finset.univ, Finset.univ_product_univ]
  exact measureProb_univ hψ

end Qatlib.Papers.QCounting98.MainResults.NonSelectiveMeasurement
