/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullPhysicalSource
public import Qatlib.Concepts.GibbsSource.SourceForms.FullPauliSource

@[expose] public section


/-! # The actual complete Pauli source in physical coordinates

The original Hermitian input selects the same spectral data as the existing
`hermGibbs`. All original local Pauli proposals are reconstructed by their
physical Bohr transitions. The direct physical Gram operator, exact Gibbs
kernel, and normalized source-form gap consumers are connected to the
previous full energy-coordinate theorems without a spectral-choice premise.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds


open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.MainResults

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {n : ℕ}
variable {H : Operator (fullPauliDim n)}

/-- Full Pauli Physical energy Proposal for the stated finite source data. -/
theorem fullPauliPhysical_energyProposal (hH : H.IsHermitian) (P : FullPauliLabel n) :
    fullPhysicalEnergyProposal (hermUnitary H hH) (fullPauliFamily n P) =
      fullPauliHamiltonianFamily hH P := by
  rw [fullPauliHamiltonianFamily_eq]
  simp only [fullPhysicalEnergyProposal, fullUnitaryConj,
    Matrix.conjTranspose_conjTranspose]

/-- Physical Bohr components of the original unscaled local Paulis. -/
noncomputable def fullPauliPhysicalTransition (hH : H.IsHermitian)
    (P : FullPauliLabel n) (a : FullCoord (fullPauliDim n)) : Operator (fullPauliDim n) :=
  fullPhysicalTransition (hermUnitary H hH) (fullPauliFamily n P) a

/-- Full Pauli Physical Transition eq for the stated finite source data. -/
theorem fullPauliPhysicalTransition_eq (hH : H.IsHermitian)
    (P : FullPauliLabel n) (a : FullCoord (fullPauliDim n)) :
    fullPauliPhysicalTransition hH P a =
      hermSpectralBlock H hH a.1 a.2 (fullPauliHamiltonianFamily hH P a.1 a.2) := by
  simp only [fullPauliPhysicalTransition, fullPhysicalTransition,
    fullPauliPhysical_energyProposal, fullTransition, fullUnitaryConj, hermSpectralBlock]

/-- Full Pauli Physical Transition sum for the stated finite source data. -/
theorem fullPauliPhysicalTransition_sum (hH : H.IsHermitian) (P : FullPauliLabel n) :
    ∑ a, fullPauliPhysicalTransition hH P a = fullPauliFamily n P :=
  fullPhysicalTransition_sum _ _ (hermUnitary_star_mul H hH)

/-- Full Pauli Physical Hamiltonian eq for the stated finite source data. -/
theorem fullPauliPhysicalHamiltonian_eq (hH : H.IsHermitian) :
    fullPhysicalHamiltonian (hermUnitary H hH) (fullPauliHamiltonianEigenvalues hH) = H :=
  (fullPauliHamiltonian_reconstruct hH).symm

/-- Full Pauli Physical Transition bohr for the stated finite source data. -/
theorem fullPauliPhysicalTransition_bohr (hH : H.IsHermitian) (P : FullPauliLabel n)
    (a : FullCoord (fullPauliDim n)) :
    H * fullPauliPhysicalTransition hH P a - fullPauliPhysicalTransition hH P a * H =
      (fullNu (fullPauliHamiltonianEigenvalues hH) a : ℂ) •
        fullPauliPhysicalTransition hH P a := by
  have h := fullPhysicalTransition_bohr (hermUnitary H hH) (fullPauliFamily n P)
    (fullPauliHamiltonianEigenvalues hH) (hermUnitary_star_mul H hH) a
  rwa [fullPauliPhysicalHamiltonian_eq hH] at h

/-- Direct physical `W/2` parent, with all original `3n` proposals. -/
noncomputable def fullPauliPhysicalParentOp (hH : H.IsHermitian) (β : ℝ)
    (kern : ℝ → ℝ) : Operator (fullPauliDim n) →ₗ[ℂ] Operator (fullPauliDim n) :=
  fullPhysicalParentOp (hermUnitary H hH) (fullPauliHamiltonianEigenvalues hH)
    β kern (fullPauliFamily n)

/-- Full Pauli Physical Parent Op eq for the stated finite source data. -/
theorem fullPauliPhysicalParentOp_eq (hH : H.IsHermitian) (β : ℝ) (kern : ℝ → ℝ) :
    fullPauliPhysicalParentOp hH β kern =
      ∑ P : FullPauliLabel n,
        parentGramFamOp (fullWeight (fullPauliHamiltonianEigenvalues hH) β kern)
          (hermGibbs H hH β) (fullPauliPhysicalTransition hH P) := rfl

/-- Full Pauli Physical Parent Op conj for the stated finite source data. -/
theorem fullPauliPhysicalParentOp_conj (hH : H.IsHermitian) (β : ℝ)
    (kern : ℝ → ℝ) (X : Operator (fullPauliDim n)) :
    fullPauliPhysicalParentOp hH β kern (fullUnitaryConj (hermUnitary H hH) X) =
      fullUnitaryConj (hermUnitary H hH)
        (fullParentOp (fullPauliHamiltonianEigenvalues hH) β kern
          (fullPauliHamiltonianFamily hH) X) := by
  simpa only [fullPauliPhysicalParentOp, fullPauliPhysical_energyProposal] using
    fullPhysicalParentOp_conj (hermUnitary H hH) (fullPauliHamiltonianEigenvalues hH)
      β kern (fullPauliFamily n) X (hermUnitary_star_mul H hH)

/-- The same exact source gap controls every physical complex operator. -/
theorem fullPauliPhysical_plainGap_form (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β) :
    FormGapAtLeast
      (fun X => ∑ P : FullPauliLabel n,
        (ckgSourcePlainForm β (hermGibbs H hH β)
          (fullNu (fullPauliHamiltonianEigenvalues hH))
          (fullPauliPhysicalTransition hH P) X).re)
      (CFC.sqrt (hermGibbs H hH β)) (fullPauliSourcePlainGap hH β) := by
  simpa only [fullPauliSourcePlainGap, fullPauliPhysical_energyProposal] using!
    fullPhysicalSource_plainGap_form (hermUnitary H hH)
      (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliFamily n)
      (hermUnitary_star_mul H hH)

/-- Full Pauli Physical damped Gap form for the stated finite source data. -/
theorem fullPauliPhysical_dampedGap_form (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β) :
    FormGapAtLeast
      (fun X => ∑ P : FullPauliLabel n,
        (ckgSourceDampedForm β (hermGibbs H hH β)
          (fullNu (fullPauliHamiltonianEigenvalues hH))
          (fullPauliPhysicalTransition hH P) X).re)
      (CFC.sqrt (hermGibbs H hH β)) (fullPauliSourceDampedGap hH β) := by
  simpa only [fullPauliSourceDampedGap, fullPauliPhysical_energyProposal] using!
    fullPhysicalSource_dampedGap_form (hermUnitary H hH)
      (fullPauliHamiltonianEigenvalues hH) hβ (fullPauliFamily n)
      (hermUnitary_star_mul H hH)

noncomputable def fullPauliPhysicalGibbsMatrix (hH : H.IsHermitian) (β : ℝ) :
    Operator (fullPauliDim n) :=
  fullUnitaryConj (hermUnitary H hH) (fullGibbsMatrix (fullPauliHamiltonianEigenvalues hH) β)

/-- Full Pauli Physical Gibbs Matrix eq smul sqrt for the stated finite source data. -/
theorem fullPauliPhysicalGibbsMatrix_eq_smul_sqrt (hH : H.IsHermitian) (β : ℝ) :
    fullPauliPhysicalGibbsMatrix hH β =
      (Real.sqrt (fullGibbsPartition (fullPauliHamiltonianEigenvalues hH) β) : ℂ) •
        CFC.sqrt (hermGibbs H hH β) := by
  rw [fullPauliPhysicalGibbsMatrix, fullGibbsMatrix_eq_smul_sqrt]
  have he := fullPhysicalGibbs_sqrt (hermUnitary H hH)
    (fullPauliHamiltonianEigenvalues hH) β (hermUnitary_star_mul H hH)
  change CFC.sqrt (hermGibbs H hH β) = _ at he
  rw [he]
  simp only [fullUnitaryConj, Matrix.mul_smul, Matrix.smul_mul]

/-- Exact operator-kernel transport, retaining all physical coordinates. -/
theorem fullPauliPhysicalParentOp_zero_iff (hH : H.IsHermitian) (β : ℝ)
    (kern : ℝ → ℝ) (X : Operator (fullPauliDim n)) :
    fullPauliPhysicalParentOp hH β kern X = 0 ↔
      fullPauliSourceMatrix hH β kern *ᵥ
        fullVec (fullUnitaryConj (hermUnitary H hH)ᴴ X) = 0 := by
  have ha := fullPhysicalParentOp_apply (hermUnitary H hH)
    (fullPauliHamiltonianEigenvalues hH) β kern (fullPauliFamily n) X
    (hermUnitary_star_mul H hH)
  simp only [fullPauliPhysical_energyProposal] at ha
  change fullPauliPhysicalParentOp hH β kern X = _ at ha
  rw [ha, fullUnitaryConj_eq_zero _ _ (hermUnitary_star_mul H hH)]
  rw [fullPauliSourceMatrix, fullGramMatrix_mulVec]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    ext i j
    exact congrFun h (i, j)

/-- Full Pauli Physical gibbs line for the stated finite source data. -/
private theorem fullPauliPhysical_gibbs_line (hH : H.IsHermitian) (β : ℝ)
    (X : Operator (fullPauliDim n)) :
    (∃ c : ℂ, fullVec (fullUnitaryConj (hermUnitary H hH)ᴴ X) =
      c • fullPauliSourceGibbsVector hH β) ↔
      ∃ c : ℂ, X = c • fullPauliPhysicalGibbsMatrix hH β := by
  constructor
  · rintro ⟨c, hc⟩
    have hm : fullUnitaryConj (hermUnitary H hH)ᴴ X =
        c • fullGibbsMatrix (fullPauliHamiltonianEigenvalues hH) β := by
      ext i j
      exact congrFun hc (i, j)
    refine ⟨c, ?_⟩
    calc
      X = fullUnitaryConj (hermUnitary H hH)
          (fullUnitaryConj (hermUnitary H hH)ᴴ X) :=
        (fullUnitaryConj_inverse _ _ (hermUnitary_star_mul H hH)).symm
      _ = _ := by rw [hm]; simp only [fullPauliPhysicalGibbsMatrix, fullUnitaryConj,
        Matrix.mul_smul, Matrix.smul_mul]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    have hc : fullUnitaryConj (hermUnitary H hH)ᴴ
        (c • fullPauliPhysicalGibbsMatrix hH β) =
        c • fullGibbsMatrix (fullPauliHamiltonianEigenvalues hH) β := by
      calc
        _ = c • fullUnitaryConj (hermUnitary H hH)ᴴ
            (fullPauliPhysicalGibbsMatrix hH β) := by
          simp only [fullUnitaryConj, Matrix.mul_smul, Matrix.smul_mul]
        _ = _ := by rw [fullPauliPhysicalGibbsMatrix,
          fullUnitaryConj_leftInverse _ _ (hermUnitary_star_mul H hH)]
    rw [hc]
    rfl

/-- Full Pauli Physical plain kernel for the stated finite source data. -/
theorem fullPauliPhysical_plain_kernel (hH : H.IsHermitian) {β : ℝ} (hβ : 0 < β)
    (X : Operator (fullPauliDim n)) :
    fullPauliPhysicalParentOp hH β (fun _ => 1) X = 0 ↔
      ∃ c : ℂ, X = c • fullPauliPhysicalGibbsMatrix hH β := by
  rw [fullPauliPhysicalParentOp_zero_iff, fullPauliSource_plain_kernel hH hβ,
    fullPauliPhysical_gibbs_line]

/-- Full Pauli Physical damped kernel for the stated finite source data. -/
theorem fullPauliPhysical_damped_kernel (hn : 0 < n) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) (X : Operator (fullPauliDim n)) :
    fullPauliPhysicalParentOp hH β (fun ω => 2 * phaseKernel β ω) X = 0 ↔
      ∃ c : ℂ, X = c • fullPauliPhysicalGibbsMatrix hH β := by
  rw [fullPauliPhysicalParentOp_zero_iff, fullPauliSource_damped_kernel hn hH hβ,
    fullPauliPhysical_gibbs_line]

/-- Full Physical hs Inner vec for the stated finite source data. -/
private theorem fullPhysical_hsInner_vec {D : ℕ} (X Y : Operator D) :
    hsInner X Y = star (fullVec X) ⬝ᵥ fullVec Y := by
  simp only [hsInner_eq_sum, dotProduct, fullVec, Pi.star_apply, Fintype.sum_prod_type]

/-- Full Pauli Physical eigenvector lift for the stated finite source data. -/
private theorem fullPauliPhysical_eigenvector_lift (hH : H.IsHermitian) (β : ℝ)
    (kern : ℝ → ℝ) (r : ℝ) (z : FullCoord (fullPauliDim n) → ℂ)
    (hz : z ∈ fullUnitOrthogonal (fullPauliSourceGibbsVector hH β))
    (he : fullPauliSourceMatrix hH β kern *ᵥ z = (r : ℂ) • z) :
    ∃ X : Operator (fullPauliDim n),
      (hsInner X X).re = 1 ∧ hsInner (fullPauliPhysicalGibbsMatrix hH β) X = 0 ∧
        fullPauliPhysicalParentOp hH β kern X = (r : ℂ) • X := by
  let Z : Operator (fullPauliDim n) := fun i j => z (i, j)
  refine ⟨fullUnitaryConj (hermUnitary H hH) Z, ?_, ?_, ?_⟩
  · rw [fullUnitaryConj_hsInner _ Z Z (hermUnitary_star_mul H hH),
      fullPhysical_hsInner_vec]
    exact hz.1
  · rw [fullPauliPhysicalGibbsMatrix,
      fullUnitaryConj_hsInner _ _ Z (hermUnitary_star_mul H hH), fullPhysical_hsInner_vec]
    exact hz.2
  · have heZ : fullParentOp (fullPauliHamiltonianEigenvalues hH) β kern
        (fullPauliHamiltonianFamily hH) Z = (r : ℂ) • Z := by
      have he' : fullGramMatrix (fullPauliHamiltonianEigenvalues hH) β kern
          (fullPauliHamiltonianFamily hH) *ᵥ fullVec Z = (r : ℂ) • fullVec Z := he
      rw [fullGramMatrix_mulVec] at he'
      ext i j
      exact congrFun he' (i, j)
    rw [fullPauliPhysicalParentOp_conj, heZ]
    simp only [fullUnitaryConj, Matrix.mul_smul, Matrix.smul_mul]

/-- Both existing exact gaps are attained in the complete physical operator
space by unit HS eigenvectors orthogonal to the actual Gibbs line. Together
with the physical FormGap bounds, this identifies the same optimal gaps. -/
theorem fullPauliPhysical_gap_eigenvectors (hn : 0 < n) (hH : H.IsHermitian)
    {β : ℝ} (hβ : 0 < β) :
    (∃ X : Operator (fullPauliDim n),
      (hsInner X X).re = 1 ∧ hsInner (fullPauliPhysicalGibbsMatrix hH β) X = 0 ∧
        fullPauliPhysicalParentOp hH β (fun _ => 1) X =
          (fullPauliSourcePlainGap hH β : ℂ) • X) ∧
    (∃ X : Operator (fullPauliDim n),
      (hsInner X X).re = 1 ∧ hsInner (fullPauliPhysicalGibbsMatrix hH β) X = 0 ∧
        fullPauliPhysicalParentOp hH β (fun ω => 2 * phaseKernel β ω) X =
          (fullPauliSourceDampedGap hH β : ℂ) • X) := by
  obtain ⟨h0, hg⟩ := fullPauliSource_gap_eigenvectors hn hH hβ
  obtain ⟨z0, hz0, he0⟩ := h0
  obtain ⟨zg, hzg, heg⟩ := hg
  exact ⟨fullPauliPhysical_eigenvector_lift hH β (fun _ => 1)
      (fullPauliSourcePlainGap hH β) z0 hz0 he0,
    fullPauliPhysical_eigenvector_lift hH β (fun ω => 2 * phaseKernel β ω)
      (fullPauliSourceDampedGap hH β) zg hzg heg⟩

end Qatlib.Papers.GibbsSampl26.MainResults
