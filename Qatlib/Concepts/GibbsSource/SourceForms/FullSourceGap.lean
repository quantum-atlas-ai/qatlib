/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullSourceKernel
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceSechGapTransport
public import Qatlib.Concepts.GibbsSource.SourceForms.FullSpaceGapEigenvalue

@[expose] public section


/-! # Exact positive gaps for the complete finite source parent

The actual plain and damped gaps are attained minima on the full complex
Gibbs-orthogonal unit sphere. Scalar common commutant gives a positive plain
gap. The already proved positive Schur transport gives the damped lower
bound, its exact Gibbs kernel, and the comparison `delta0 <= deltag`.
No uniform positive constant or upper gap comparison is asserted here.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- A literal off-diagonal matrix unit supplies a unit Gibbs-orthogonal
vector whenever the original Hilbert space has at least two levels. -/
theorem fullGibbsUnitOrthogonal_nonempty (hD : 2 ≤ D)
    (lam : Fin D → ℝ) (β : ℝ) :
    (fullUnitOrthogonal (fullGibbsVector lam β)).Nonempty := by
  classical
  let i : Fin D := ⟨0, by omega⟩
  let j : Fin D := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have he := congrArg Fin.val h
    dsimp only [i, j] at he
    omega
  refine ⟨Pi.single (i, j) (1 : ℂ), ?_, ?_⟩
  · simp [fullNormSq_eq_sum, Pi.single_apply]
  · simp [dotProduct, fullGibbsVector, fullVec, fullGibbsMatrix,
      Matrix.diagonal_apply, Pi.single_apply, hij]

noncomputable def fullSourcePlainGap (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) : ℝ :=
  fullRayleighGap (fullGramMatrix lam β (fun _ => 1) A) (fullGibbsVector lam β)

noncomputable def fullSourceDampedGap (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) : ℝ :=
  fullRayleighGap (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A)
    (fullGibbsVector lam β)

variable [Nonempty (Fin D)]

/-- Full Source Plain Gap pos for the stated finite source data. -/
theorem fullSourcePlainGap_pos (hD : 2 ≤ D) (lam : Fin D → ℝ)
    {β : ℝ} (hβ : 0 < β) (A : ι → Operator D)
    (hscalar : ∀ Y : Operator D,
      (∀ P, Y * A P = A P * Y) → ∃ c : ℂ, Y = c • (1 : Operator D)) :
    0 < fullSourcePlainGap lam β A :=
  fullRayleighGap_pos (fullGramMatrix_plain_posSemidef hβ lam A)
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fun z hz => (fullGramMatrix_plain_kernel lam hβ A hscalar z).mp hz)
    (fullGibbsUnitOrthogonal_nonempty hD lam β)

/-- The best plain gap is an actual full matrix lower bound. -/
theorem fullSourcePlainGap_lowerBound (lam : Fin D → ℝ) {β : ℝ}
    (hβ : 0 < β) (A : ι → Operator D) :
    (fullGramMatrix lam β (fun _ => 1) A - (fullSourcePlainGap lam β A : ℂ) •
      fullGibbsComplement (fullGibbsVector lam β)).PosSemidef :=
  fullRayleighGap_lowerBound (fullGramMatrix_plain_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun _ => 1) A)

/-- Actual source damping preserves this optimal plain lower bound. -/
theorem fullSourceDamped_plainGap_lowerBound (lam : Fin D → ℝ) {β : ℝ}
    (hβ : 0 < β) (A : ι → Operator D) :
    (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A -
      (fullSourcePlainGap lam β A : ℂ) •
        fullGibbsComplement (fullGibbsVector lam β)).PosSemidef :=
  fullGramMatrix_damped_lowerBound lam β A (fullSourcePlainGap lam β A)
    (fullSourcePlainGap_lowerBound lam hβ A)

/-- Full Source Gap lower for the stated finite source data. -/
theorem fullSourceGap_lower (hD : 2 ≤ D) (lam : Fin D → ℝ) {β : ℝ}
    (hβ : 0 < β) (A : ι → Operator D) :
    fullSourcePlainGap lam β A ≤ fullSourceDampedGap lam β A :=
  fullLowerBound_le_gap (fullGramMatrix_damped_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullSourcePlainGap lam β A)
    (fullGibbsUnitOrthogonal_nonempty hD lam β)
    (fullSourceDamped_plainGap_lowerBound lam hβ A)

/-- Full Source Damped Gap pos for the stated finite source data. -/
theorem fullSourceDampedGap_pos (hD : 2 ≤ D) (lam : Fin D → ℝ)
    {β : ℝ} (hβ : 0 < β) (A : ι → Operator D)
    (hscalar : ∀ Y : Operator D,
      (∀ P, Y * A P = A P * Y) → ∃ c : ℂ, Y = c • (1 : Operator D)) :
    0 < fullSourceDampedGap lam β A :=
  lt_of_lt_of_le (fullSourcePlainGap_pos hD lam hβ A hscalar)
    (fullSourceGap_lower hD lam hβ A)

/-- Both actual parents have precisely the Gibbs line as kernel. This
damped statement uses the positive plain gap, not an assumed damped kernel. -/
theorem fullGramMatrix_damped_kernel (hD : 2 ≤ D) (lam : Fin D → ℝ)
    {β : ℝ} (hβ : 0 < β) (A : ι → Operator D)
    (hscalar : ∀ Y : Operator D,
      (∀ P, Y * A P = A P * Y) → ∃ c : ℂ, Y = c • (1 : Operator D))
    (z : FullCoord D → ℂ) :
    fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A *ᵥ z = 0 ↔
      ∃ c : ℂ, z = c • fullGibbsVector lam β := by
  constructor
  · intro hz
    have hb := (fullLowerBound_iff_variance
      (fullGramMatrix_damped_posSemidef hβ lam A).isHermitian
      (fullGibbsVector lam β) (fullSourcePlainGap lam β A)).mp
        (fullSourceDamped_plainGap_lowerBound lam hβ A) z
    have hq : fullRayleigh
        (fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A) z = 0 := by
      simp [fullRayleigh, hz]
    rw [hq] at hb
    have hδ := fullSourcePlainGap_pos hD lam hβ A hscalar
    have hv := fullVariance_nonneg (fullGibbsVector lam β) z
      (fullGibbsVector_ne_zero lam β)
    have hv0 : fullVariance (fullGibbsVector lam β) z = 0 := by nlinarith
    exact (fullVariance_eq_zero_iff (fullGibbsVector lam β) z
      (fullGibbsVector_ne_zero lam β)).mp hv0
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, fullGramMatrix_gibbsVector_eq_zero, smul_zero]

/-- The plain gap is a genuine attained eigenvalue. -/
theorem fullSourcePlainGap_eigenvector (hD : 2 ≤ D) (lam : Fin D → ℝ)
    {β : ℝ} (hβ : 0 < β) (A : ι → Operator D) :
    ∃ z ∈ fullUnitOrthogonal (fullGibbsVector lam β),
      fullGramMatrix lam β (fun _ => 1) A *ᵥ z =
        (fullSourcePlainGap lam β A : ℂ) • z :=
  fullRayleighGap_eigenvector (fullGramMatrix_plain_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun _ => 1) A)
    (fullGibbsUnitOrthogonal_nonempty hD lam β)

/-- Full Source Damped Gap eigenvector for the stated finite source data. -/
theorem fullSourceDampedGap_eigenvector (hD : 2 ≤ D) (lam : Fin D → ℝ)
    {β : ℝ} (hβ : 0 < β) (A : ι → Operator D) :
    ∃ z ∈ fullUnitOrthogonal (fullGibbsVector lam β),
      fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A *ᵥ z =
        (fullSourceDampedGap lam β A : ℂ) • z :=
  fullRayleighGap_eigenvector (fullGramMatrix_damped_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) (fullGibbsVector_ne_zero lam β)
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun ω => 2 * phaseKernel β ω) A)
    (fullGibbsUnitOrthogonal_nonempty hD lam β)

/-- Full Source Plain Gap le eigenvalue for the stated finite source data. -/
theorem fullSourcePlainGap_le_eigenvalue (lam : Fin D → ℝ) {β : ℝ}
    (hβ : 0 < β) (A : ι → Operator D) (z : FullCoord D → ℂ) (hz : z ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (he : fullGramMatrix lam β (fun _ => 1) A *ᵥ z = (r : ℂ) • z) :
    fullSourcePlainGap lam β A ≤ r :=
  fullRayleighGap_le_nonzero_eigenvalue
    (fullGramMatrix_plain_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) z
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun _ => 1) A) hz r hr he

/-- Full Source Damped Gap le eigenvalue for the stated finite source data. -/
theorem fullSourceDampedGap_le_eigenvalue (lam : Fin D → ℝ) {β : ℝ}
    (hβ : 0 < β) (A : ι → Operator D) (z : FullCoord D → ℂ) (hz : z ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (he : fullGramMatrix lam β (fun ω => 2 * phaseKernel β ω) A *ᵥ z =
      (r : ℂ) • z) :
    fullSourceDampedGap lam β A ≤ r :=
  fullRayleighGap_le_nonzero_eigenvalue
    (fullGramMatrix_damped_posSemidef hβ lam A).isHermitian
    (fullGibbsVector lam β) z
    (fullGramMatrix_gibbsVector_eq_zero lam β (fun ω => 2 * phaseKernel β ω) A)
    hz r hr he

end Qatlib.Concepts.GibbsSource.SourceForms
