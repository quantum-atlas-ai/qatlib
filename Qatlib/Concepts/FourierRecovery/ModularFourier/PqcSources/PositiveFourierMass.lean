/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic.Transform

open Qatlib.Concepts.FourierRecovery.ModularFourier.FiniteHarmonic

/-! A positive Fourier spectrum makes the zero-output excess dominate every
finite-group mass deviation. The coefficients are computed from the actual
real-valued mass, using the conjugation convention of `fourier`.
No Fourier positivity, surjectivity, or Gaussian estimate is manufactured here.
The deterministic result needs total mass one but not pointwise positivity;
probability consumers may supply that additional interpretation separately. -/

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources

open scoped BigOperators ComplexConjugate

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Counting-normalized Fourier coefficient of the actual real mass. -/
noncomputable def pqcMassFourierCoefficient (w : G → ℝ) (χ : AddChar G ℂ) : ℂ :=
  ∑ x, (w x : ℂ) * conj (χ x)

/-- Every actual coefficient is real and nonnegative. -/
def pqcMassHasNonnegativeFourier (w : G → ℝ) : Prop :=
  ∀ χ : AddChar G ℂ,
    (pqcMassFourierCoefficient w χ).im = 0 ∧ 0 ≤ (pqcMassFourierCoefficient w χ).re

/-- The counting coefficient agrees with the existing quantum transform. -/
theorem pqc_mass_fourier_coefficient_fourier (w : G → ℝ) (χ : AddChar G ℂ) :
    fourier (fun x => (w x : ℂ)) χ =
      fourierScale G * pqcMassFourierCoefficient w χ := by
  rw [fourier_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- Counting Fourier inversion, obtained from the proved dual orthogonality. -/
theorem pqc_mass_fourier_inversion (w : G → ℝ) (y : G) :
    (∑ χ : AddChar G ℂ, χ y * pqcMassFourierCoefficient w χ) =
      (Fintype.card G : ℂ) * (w y : ℂ) := by
  classical
  calc
    _ = ∑ x : G, (w x : ℂ) * ∑ χ : AddChar G ℂ, χ y * conj (χ x) := by
      unfold pqcMassFourierCoefficient
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by
      simp only [sum_dual_mul_conj, mul_ite, mul_zero]
      simp [mul_comm]

/-- Total mass one fixes the trivial coefficient, rather than assuming it. -/
theorem pqc_mass_fourier_coefficient_zero (w : G → ℝ) (hsum : ∑ x, w x = 1) :
    pqcMassFourierCoefficient w 0 = 1 := by
  classical
  simp only [pqcMassFourierCoefficient, AddChar.zero_apply, map_one, mul_one]
  rw [← Complex.ofReal_sum, hsum]
  rfl

/-- The actual finite-label construction satisfies `mass_deviation_nontrivial_sum` with all displayed hypotheses. -/
private theorem mass_deviation_nontrivial_sum
    (w : G → ℝ) (hsum : ∑ x, w x = 1) (y : G) :
    (∑ χ ∈ Finset.univ.erase (0 : AddChar G ℂ), χ y * pqcMassFourierCoefficient w χ) =
      (Fintype.card G : ℂ) * (w y : ℂ) - 1 := by
  classical
  have h := Finset.sum_erase_add (Finset.univ : Finset (AddChar G ℂ))
    (fun χ => χ y * pqcMassFourierCoefficient w χ) (Finset.mem_univ 0)
  simp only [AddChar.zero_apply, one_mul, pqc_mass_fourier_coefficient_zero w hsum] at h
  rw [pqc_mass_fourier_inversion] at h
  exact eq_sub_of_add_eq h

/-- The actual finite-label construction satisfies `zero_mass_deviation_sum` with all displayed hypotheses. -/
private theorem zero_mass_deviation_sum
    (w : G → ℝ) (hsum : ∑ x, w x = 1) :
    (Fintype.card G : ℝ) * w 0 - 1 =
      ∑ χ ∈ Finset.univ.erase (0 : AddChar G ℂ), (pqcMassFourierCoefficient w χ).re := by
  classical
  have h := congrArg Complex.re (mass_deviation_nontrivial_sum w hsum 0)
  simpa using h.symm

/-- The actual finite-label construction satisfies `mass_coefficient_norm` with all displayed hypotheses. -/
private theorem mass_coefficient_norm
    (w : G → ℝ) (hpos : pqcMassHasNonnegativeFourier w) (χ : AddChar G ℂ) :
    ‖pqcMassFourierCoefficient w χ‖ = (pqcMassFourierCoefficient w χ).re := by
  have heq : pqcMassFourierCoefficient w χ =
      ((pqcMassFourierCoefficient w χ).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (hpos χ).1
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos χ).2]
  rfl

/-- The zero-output excess is nonnegative for an actual positive spectrum. -/
theorem pqc_positive_fourier_mass_nonneg
    (w : G → ℝ) (hsum : ∑ x, w x = 1) (hpos : pqcMassHasNonnegativeFourier w) :
    0 ≤ (Fintype.card G : ℝ) * w 0 - 1 := by
  classical
  rw [zero_mass_deviation_sum w hsum]
  exact Finset.sum_nonneg fun χ _ => (hpos χ).2

/-- One zero-output excess controls every output, without a syndrome union bound. -/
theorem pqc_positive_fourier_mass_deviation
    (w : G → ℝ) (hsum : ∑ x, w x = 1) (hpos : pqcMassHasNonnegativeFourier w) (y : G) :
    |(Fintype.card G : ℝ) * w y - 1| ≤ (Fintype.card G : ℝ) * w 0 - 1 := by
  classical
  calc
    _ = ‖∑ χ ∈ Finset.univ.erase (0 : AddChar G ℂ),
        χ y * pqcMassFourierCoefficient w χ‖ := by
      rw [mass_deviation_nontrivial_sum w hsum]
      have heq : (Fintype.card G : ℂ) * (w y : ℂ) - 1 =
          (((Fintype.card G : ℝ) * w y - 1 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ χ ∈ Finset.univ.erase (0 : AddChar G ℂ),
        ‖χ y * pqcMassFourierCoefficient w χ‖ := norm_sum_le _ _
    _ = ∑ χ ∈ Finset.univ.erase (0 : AddChar G ℂ),
        (pqcMassFourierCoefficient w χ).re := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [norm_mul, AddChar.norm_apply, mass_coefficient_norm w hpos, one_mul]
    _ = _ := (zero_mass_deviation_sum w hsum).symm

end Qatlib.Concepts.FourierRecovery.ModularFourier.PqcSources
