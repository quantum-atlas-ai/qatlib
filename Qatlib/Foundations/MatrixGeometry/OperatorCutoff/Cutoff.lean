/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.OperatorCutoff.Contraction

/-!
# Coefficient cutoffs and energy error

Defines a finite operator sum `hamiltonian`, its coefficient-threshold truncation `cutoff`, and
the total discarded coefficient norm `removedMass`. For summands of norm at most one, the
discarded mass bounds both the operator error and the error in real expectations on unit
vectors. See [McCleanEtAl2014] for related background.

## Main statements

* `cutoff_opNorm`: For operators `A i` of norm at most one, the cutoff error has operator norm
  at most `removedMass c δ`.
* `cutoff_energy`: For a unit vector and summand operators of norm at most one, coefficient
  truncation changes the real expectation by at most the discarded mass.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixGeometry.OperatorCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι]

/-- The finite operator sum `∑ i, c i • A i`. -/
def hamiltonian (c : ι → ℂ) (A : ι → E →L[ℂ] E) : E →L[ℂ] E := ∑ i, c i • A i

/-- The operator sum obtained by discarding terms whose coefficient norm is strictly less than
`δ`. -/
def cutoff (c : ι → ℂ) (A : ι → E →L[ℂ] E) (δ : ℝ) : E →L[ℂ] E :=
  ∑ i, if ‖c i‖ < δ then 0 else c i • A i

/-- The sum of the norms of coefficients whose norm is strictly less than `δ`. -/
def removedMass (c : ι → ℂ) (δ : ℝ) : ℝ :=
  ∑ i, if ‖c i‖ < δ then ‖c i‖ else 0

/-- The difference between the full operator sum and its cutoff is exactly the sum of the
discarded terms. -/
theorem subtract_cutoff (c : ι → ℂ) (A : ι → E →L[ℂ] E) (δ : ℝ) :
    hamiltonian c A - cutoff c A δ = ∑ i, if ‖c i‖ < δ then c i • A i else 0 := by
  unfold hamiltonian cutoff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- For operators `A i` of norm at most one, the cutoff error has operator norm at most
`removedMass c δ`. -/
theorem cutoff_opNorm (c : ι → ℂ) (A : ι → E →L[ℂ] E) (δ : ℝ)
    (hA : ∀ i, ‖A i‖ ≤ 1) : ‖hamiltonian c A - cutoff c A δ‖ ≤ removedMass c δ := by
  rw [subtract_cutoff]
  apply (norm_sum_le _ _).trans
  unfold removedMass
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hA i) (norm_nonneg _)).trans_eq (mul_one _)
  · simp

/-- The discarded coefficient mass is nonnegative. -/
theorem removedMass_nonneg (c : ι → ℂ) (δ : ℝ) : 0 ≤ removedMass c δ := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> positivity

/-- The discarded mass is at most the number of discarded coefficients times the threshold `δ`. -/
theorem removedMass_le_count (c : ι → ℂ) (δ : ℝ) :
    removedMass c δ ≤ ((Finset.univ.filter (fun i => ‖c i‖ < δ)).card : ℝ) * δ := by
  classical
  unfold removedMass
  rw [← Finset.sum_filter]
  calc
    ∑ i ∈ Finset.univ.filter (fun i => ‖c i‖ < δ), ‖c i‖ ≤
        ∑ _i ∈ Finset.univ.filter (fun i => ‖c i‖ < δ), δ := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ = _ := by simp

/-- The real part of the expectation `inner ℂ ψ (H ψ)`. -/
def energy (H : E →L[ℂ] E) (ψ : E) : ℝ := (inner ℂ ψ (H ψ)).re

/-- For a unit vector, the absolute difference of real expectations of two operators is at most
their operator-norm distance. -/
theorem energy_sub_le_opNorm (H K : E →L[ℂ] E) (ψ : E) (hψ : ‖ψ‖ = 1) :
    |energy H ψ - energy K ψ| ≤ ‖H - K‖ := by
  have he : energy H ψ - energy K ψ = (inner ℂ ψ ((H - K) ψ)).re := by
    simp only [energy, ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
  rw [he]
  calc
    |(inner ℂ ψ ((H - K) ψ)).re| ≤ ‖inner ℂ ψ ((H - K) ψ)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖(H - K) ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖H - K‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left ((H - K).le_opNorm ψ) (norm_nonneg _)
    _ = ‖H - K‖ := by rw [hψ]; ring

/-- For a unit vector and summand operators of norm at most one, coefficient truncation changes
the real expectation by at most the discarded mass. -/
theorem cutoff_energy (c : ι → ℂ) (A : ι → E →L[ℂ] E) (δ : ℝ)
    (hA : ∀ i, ‖A i‖ ≤ 1) (ψ : E) (hψ : ‖ψ‖ = 1) :
    |energy (hamiltonian c A) ψ - energy (cutoff c A δ) ψ| ≤ removedMass c δ :=
  (energy_sub_le_opNorm _ _ ψ hψ).trans (cutoff_opNorm c A δ hA)
end Qatlib.Foundations.MatrixGeometry.OperatorCutoff
