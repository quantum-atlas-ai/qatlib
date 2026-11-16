/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.TraceBounds.GradientTrace

@[expose] public section


/-! # Centered complete-frame Rayleigh trials

Removing a nonzero Gibbs line leaves exactly D² minus one units of squared
frame mass. Finite weighted averaging then supplies a nonzero orthogonal trial.
The energy invariance and complete trace bound are explicit hypotheses here;
physical consumers must derive both from their actual source operators.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.TraceBounds

noncomputable section
variable {D : ℕ}

/-- Orthogonal centering on an arbitrary nonzero source line. -/
def center (G X : Operator D) : Operator D :=
  sourceCenteredProjection LinearMap.id G X

/-- The centered vector is orthogonal to the removed line and realizes the projection pairing. -/
theorem center_properties (G X : Operator D) (hG : 0 < (hsInner G G).re) :
    hsInner G (center G X) = 0 ∧
      hsInner X (center G X) = hsInner (center G X) (center G X) := by
  exact (sourceCenteredProjection_properties LinearMap.id (fun _ _ => rfl)
    (fun _ => rfl) G hG X).2

/-- The trace of the identity on D by D complex matrices is D squared. -/
theorem sourceTrace_identity :
    sourceTrace (LinearMap.id : Operator D →ₗ[ℂ] Operator D) = (D : ℝ)^2 := by
  simp [sourceTrace, sourceSuperMatrix, Matrix.trace, matUnit,
    Fintype.card_prod, pow_two]

/-- Centering the complete matrix-unit frame removes exactly one unit of mass. -/
theorem sum_center_matrixUnit_normSq (G : Operator D) (hG : 0 < (hsInner G G).re) :
    (∑ i, ∑ j, (hsInner (center G (matUnit i j 1))
      (center G (matUnit i j 1))).re) = (D : ℝ)^2 - 1 := by
  simp_rw [← (center_properties G _ hG).2]
  change (∑ i, ∑ j, (hsInner (matUnit i j 1)
    (sourceCenteredProjection LinearMap.id G (matUnit i j 1))).re) = _
  rw [← sourceTrace_eq_matrixUnit_sum, sourceTrace_centered, sourceTrace_identity]
  exact hG

/-- Weighted averaging allows zero weights and requires only nonnegative energies. -/
theorem exists_weighted_trial {ι : Type*} [Fintype ι]
    (weight energy : ι → ℝ) (B : ℝ)
    (hw : ∀ i, 0 ≤ weight i) (he : ∀ i, 0 ≤ energy i)
    (hwpos : 0 < ∑ i, weight i) (hbound : ∑ i, energy i ≤ B) :
    ∃ i, 0 < weight i ∧ energy i ≤ (B / ∑ j, weight j) * weight i := by
  classical
  by_contra hn
  have hstrict (i : ι) (hi : 0 < weight i) :
      (B / ∑ j, weight j) * weight i < energy i :=
    lt_of_not_ge (fun h => hn ⟨i, hi, h⟩)
  have hle (i : ι) : (B / ∑ j, weight j) * weight i ≤ energy i := by
    by_cases hi : 0 < weight i
    · exact (hstrict i hi).le
    · have hz : weight i = 0 := le_antisymm (le_of_not_gt hi) (hw i)
      simpa [hz] using he i
  have hex : ∃ i, 0 < weight i := by
    by_contra! hn
    have hh : ∑ i, weight i ≤ 0 := Finset.sum_nonpos (fun i _ => hn i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hh := Finset.sum_lt_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hle i)
    ⟨i, Finset.mem_univ i, hstrict i hi⟩
  rw [← Finset.mul_sum, div_mul_cancel₀ _ hwpos.ne'] at hh
  exact (not_lt_of_ge hbound) hh


/-- A complete trace cap gives an actual positive-mass trial on the complement of any nonzero kernel line. -/
theorem exists_centered_trial (hD : 1 < D) (G : Operator D)
    (hG : 0 < (hsInner G G).re) (energy : Operator D → ℝ) (B : ℝ)
    (hnonneg : ∀ X, 0 ≤ energy X)
    (hcenter : ∀ X, energy (center G X) = energy X)
    (htrace : (∑ i, ∑ j, energy (matUnit i j 1)) ≤ B) :
    ∃ X : Operator D, hsInner G X = 0 ∧ 0 < (hsInner X X).re ∧
      energy X ≤ (B / ((D : ℝ)^2 - 1)) * (hsInner X X).re := by
  let X := fun a : Fin D × Fin D => center G (matUnit a.1 a.2 1)
  let weight := fun a => (hsInner (X a) (X a)).re
  let E := fun a => energy (X a)
  have hdim : 0 < (D : ℝ)^2 - 1 := by
    have hh : (1 : ℝ) < D := by exact_mod_cast hD
    nlinarith
  have hw : ∑ a, weight a = (D : ℝ)^2 - 1 := by
    simpa only [weight, X, Fintype.sum_prod_type] using sum_center_matrixUnit_normSq G hG
  have he : ∑ a, E a ≤ B := by
    simpa only [E, X, hcenter, Fintype.sum_prod_type] using htrace
  obtain ⟨a, hp, hb⟩ := exists_weighted_trial weight E B
    (fun a => hsInner_self_nonneg _) (fun a => hnonneg _)
    (by rw [hw]; exact hdim) he
  rw [hw] at hb
  exact ⟨X a, (center_properties G _ hG).1, hp, hb⟩

end
end Qatlib.Concepts.GibbsSource.TraceBounds
