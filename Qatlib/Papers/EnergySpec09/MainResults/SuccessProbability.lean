/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EnergySpec09.MainResults.MCSCFPhaseEstimation

/-!
# Success weights from initial-state overlaps

This module proves the squared-overlap readout formula used in the MCSCF phase-estimation scheme
of [WangEtAl2008]. The helpers `tensorState_sum` and `inner_eq_coeff` relate finite state
expansions to tensor products and orthonormal expansion coefficients.

For orthonormal eigenstates with distinct phase labels on the exact phase grid,
`qpe_success_prob_eq_coeff_sq` identifies a label's readout weight with the squared norm of its
coefficient. The theorem `qpe_success_prob_eq_overlap_sq` rewrites that coefficient as an
overlap. The final comparison is conditional on the supplied ordering of overlap norms.

## Main statements

* `qpe_success_prob_eq_coeff_sq`: the selected phase-label weight is `‖c n‖ ^ 2`.
* `qpe_success_prob_eq_overlap_sq`: the same weight is the squared target overlap.
* `success_prob_mono_overlap`: increasing the overlap norm increases its square.

## References

* [Wang et al., 2008][WangEtAl2008]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open scoped BigOperators Classical

namespace Qatlib.Papers.EnergySpec09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

/-- Tensoring a fixed state with a finite linear combination distributes over the sum and
preserves its coefficients. -/
theorem tensorState_sum {J : Type*} [Fintype J] [DecidableEq J]
    {Idx : Type*} [Fintype Idx] (ψ : QState J) (c : Idx → ℂ) (φ : Idx → QState I) :
    TensorState ψ (∑ i, c i • φ i) = ∑ i, c i • TensorState ψ (φ i) := by
  funext p
  obtain ⟨m, j⟩ := p
  simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The overlap with an element of an orthonormal family extracts its coefficient from a finite
expansion in that family. -/
theorem inner_eq_coeff {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0) (n : Idx) :
    Inner (φ n) (∑ i, c i • φ i) = c n := by
  rw [inner_apply]
  have h1 : ∀ j, (∑ i, c i • φ i) j = ∑ i, c i * φ i j := by
    intro j
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  simp_rw [h1]
  have hmul : ∀ j, (starRingEnd ℂ) (φ n j) * (∑ i, c i * φ i j)
      = ∑ i, (starRingEnd ℂ) (φ n j) * (c i * φ i j) := by
    intro j
    rw [Finset.mul_sum]
  simp_rw [hmul]
  rw [Finset.sum_comm]
  have h2 : ∀ i, ∑ j, (starRingEnd ℂ) (φ n j) * (c i * φ i j) = c i * Inner (φ n) (φ i) := by
    intro i
    rw [inner_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h2]
  rw [Finset.sum_eq_single n]
  · rw [hOr n n, if_pos rfl, mul_one]
  · intro i _ hin
    rw [hOr n i, if_neg (fun h : n = i => hin h.symm), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ n) hnot

/-- For orthonormal eigenstates with distinct exact phase labels, the phase-estimation weight of
label `k n` is `‖c n‖ ^ 2`. This is the coefficient form of the initial-guess success
relation in [WangEtAl2008]. -/
theorem qpe_success_prob_eq_coeff_sq {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) :
    MeasureProb
        (ApplyGate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix I I ℂ))
          (ControlledPowers U M *ᵥ (∑ i, c i • TensorState
            (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) (φ i))))
        ({k n} ×ˢ (Finset.univ : Finset I)) = ‖c n‖ ^ 2 := by

  rw [qpe_exact_readout_linear M hM U c φ k heig]

  have hslice : ∀ j : I,
      (∑ i, c i • TensorState (Ket (k i)) (φ i)) (k n, j) = c n * φ n j := by
    intro j
    rw [Finset.sum_apply]
    refine (Finset.sum_eq_single n ?_ ?_).trans ?_
    · intro i _ hin
      have hki : ¬ (k n = k i) := fun h => hin (hk h.symm)
      simp only [Pi.smul_apply, smul_eq_mul, TensorState, Ket, if_neg hki, zero_mul, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ n) hnot
    · simp [TensorState]

  have hmeasure : MeasureProb (∑ i, c i • TensorState (Ket (k i)) (φ i))
      ({k n} ×ˢ (Finset.univ : Finset I)) = ∑ j, ‖c n * φ n j‖ ^ 2 := by
    unfold MeasureProb
    rw [Finset.sum_product, Finset.sum_singleton]
    exact Finset.sum_congr rfl fun j _ => by
      unfold BornProb
      rw [hslice j]
  rw [hmeasure]

  have hnorm : Normalized (φ n) := by
    rw [normalized_iff_inner_self, hOr n n, if_pos rfl]
  calc
    ∑ j, ‖c n * φ n j‖ ^ 2 = ∑ j, ‖c n‖ ^ 2 * ‖φ n j‖ ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_mul, mul_pow]
    _ = ‖c n‖ ^ 2 * ∑ j, ‖φ n j‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = ‖c n‖ ^ 2 := by
      rw [hnorm, mul_one]

/-- For an orthonormal eigenstate expansion with distinct exact phase labels, the weight of the
selected readout label equals the squared overlap with its eigenstate. This formalizes the
initial-guess success relation used in [WangEtAl2008]. -/
theorem qpe_success_prob_eq_overlap_sq {M : ℕ} (hM : 0 < M) (U : Matrix I I ℂ)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (c : Idx → ℂ) (φ : Idx → QState I) (k : Idx → Fin M)
    (hOr : ∀ i j, Inner (φ i) (φ j) = if i = j then 1 else 0)
    (heig : ∀ i, U *ᵥ (φ i) = (primRoot M ^ (((k i).val : ℤ))) • (φ i))
    (hk : Function.Injective k) (n : Idx) :
    MeasureProb (qpeOutput M U (∑ i, c i • φ i))
        ({k n} ×ˢ (Finset.univ : Finset I)) = ‖Inner (φ n) (∑ i, c i • φ i)‖ ^ 2 := by
  unfold qpeOutput
  rw [tensorState_sum]
  rw [qpe_success_prob_eq_coeff_sq hM U c φ k hOr heig hk n, inner_eq_coeff c φ hOr n]

omit [DecidableEq I] in

/-- If the MCSCF overlap norm is at least the Hartree-Fock overlap norm, the same ordering holds
for their squares. This conditional comparison supports the success-probability discussion
in [WangEtAl2008]. -/
theorem success_prob_mono_overlap {ψtarget ψMCSCF ψHF : QState I}
    (h : ‖Inner ψtarget ψHF‖ ≤ ‖Inner ψtarget ψMCSCF‖) :
    ‖Inner ψtarget ψHF‖ ^ 2 ≤ ‖Inner ψtarget ψMCSCF‖ ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) h 2

end Qatlib.Papers.EnergySpec09.MainResults
