/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.FullUnitaryTransport
public import Qatlib.Concepts.GibbsSource.SourceForms.FullMonomialDomination

@[expose] public section


/-! # Complete source operators in the original physical coordinates

The proposals in this module are physical matrices. Their actual spectral
transitions are obtained from a specified diagonalizing unitary and then
transported back. The resulting family reconstructs the original proposal
and satisfies its Bohr equation for the same physical Hamiltonian.

The complete physical parent is assembled from the library thermal factors,
with every transition, repeated frequency, complex direction, and `W/2`
coefficient retained. Its action, forms, and normalized variance agree with
the existing energy-coordinate construction by exact unitary transport.
No statement identifies two independently chosen diagonalizations here.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds



namespace Qatlib.Concepts.GibbsSource.SourceForms

open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

variable {D : ℕ}

/-- The physical Hamiltonian represented by the supplied real energies. -/
noncomputable def fullPhysicalHamiltonian (U : Operator D) (lam : Fin D → ℝ) :
    Operator D := fullUnitaryConj U (Matrix.diagonal fun i => (lam i : ℂ))

noncomputable def fullPhysicalGibbs (U : Operator D) (lam : Fin D → ℝ) (β : ℝ) :
    Operator D := fullUnitaryConj U (gibbsDiag lam β)

/-- The actual original proposal in the supplied energy coordinates. -/
noncomputable def fullPhysicalEnergyProposal (U A : Operator D) : Operator D :=
  fullUnitaryConj Uᴴ A

/-- Spectral transition of a physical proposal, back in physical coordinates. -/
noncomputable def fullPhysicalTransition (U A : Operator D) (a : FullCoord D) :
    Operator D := fullUnitaryConj U (fullTransition (fullPhysicalEnergyProposal U A) a)

/-- Full Physical Transition sum for the stated finite source data. -/
theorem fullPhysicalTransition_sum (U A : Operator D) (hU : Uᴴ * U = 1) :
    ∑ a, fullPhysicalTransition U A a = A := by
  classical
  simp only [fullPhysicalTransition, fullUnitaryConj, ← Matrix.sum_mul,
    ← Matrix.mul_sum, fullTransition_sum]
  exact fullUnitaryConj_inverse U A hU

/-- Every retained transition is a Bohr component of the original Hamiltonian. -/
theorem fullPhysicalTransition_bohr (U A : Operator D) (lam : Fin D → ℝ)
    (hU : Uᴴ * U = 1) (a : FullCoord D) :
    fullPhysicalHamiltonian U lam * fullPhysicalTransition U A a -
      fullPhysicalTransition U A a * fullPhysicalHamiltonian U lam =
        (fullNu lam a : ℂ) • fullPhysicalTransition U A a := by
  simp only [fullPhysicalHamiltonian, fullPhysicalTransition,
    fullUnitaryConj_mul U _ _ hU]
  have h := congrArg (fullUnitaryConj U)
    (fullTransition_bohr lam (fullPhysicalEnergyProposal U A) a)
  simpa only [fullUnitaryConj, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul] using h

/-- Full Physical Gibbs sqrt for the stated finite source data. -/
theorem fullPhysicalGibbs_sqrt (U : Operator D) (lam : Fin D → ℝ) (β : ℝ)
    (hU : Uᴴ * U = 1) :
    CFC.sqrt (fullPhysicalGibbs U lam β) =
      fullUnitaryConj U (CFC.sqrt (gibbsDiag lam β)) :=
  CFC_sqrt_conj U _ hU (gibbsDiag_nonneg lam β)

variable {ι : Type*} [Fintype ι]

/-- Actual full physical parent, directly assembled from physical transitions. -/
noncomputable def fullPhysicalParentOp (U : Operator D) (lam : Fin D → ℝ)
    (β : ℝ) (kern : ℝ → ℝ) (A : ι → Operator D) :
    Operator D →ₗ[ℂ] Operator D :=
  ∑ P, parentGramFamOp (fullWeight lam β kern) (fullPhysicalGibbs U lam β)
    (fullPhysicalTransition U (A P))

/-- Full Physical Parent Op conj for the stated finite source data. -/
theorem fullPhysicalParentOp_conj [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (X : Operator D) (hU : Uᴴ * U = 1) :
    fullPhysicalParentOp U lam β kern A (fullUnitaryConj U X) =
      fullUnitaryConj U (fullParentOp lam β kern
        (fun P => fullPhysicalEnergyProposal U (A P)) X) := by
  simp only [fullPhysicalParentOp, LinearMap.sum_apply]
  calc
    _ = ∑ P, fullUnitaryConj U
        (parentGramFamOp (fullWeight lam β kern) (gibbsDiag lam β)
          (fullTransition (fullPhysicalEnergyProposal U (A P))) X) := by
      exact Finset.sum_congr rfl fun P _ => fullUnitaryConj_parentGramFamOp
        U (gibbsDiag lam β) (fullWeight lam β kern)
          (fullTransition (fullPhysicalEnergyProposal U (A P))) X hU
          (fullGibbsDiag_posDef lam β)
    _ = _ := by
      simp only [fullParentOp_apply, fullUnitaryConj, Matrix.mul_sum, Matrix.sum_mul]

/-- Action formula for an arbitrary physical input. -/
theorem fullPhysicalParentOp_apply [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) (β : ℝ) (kern : ℝ → ℝ)
    (A : ι → Operator D) (X : Operator D) (hU : Uᴴ * U = 1) :
    fullPhysicalParentOp U lam β kern A X =
      fullUnitaryConj U (fullParentOp lam β kern
        (fun P => fullPhysicalEnergyProposal U (A P)) (fullUnitaryConj Uᴴ X)) := by
  have h := fullPhysicalParentOp_conj U lam β kern A (fullUnitaryConj Uᴴ X) hU
  rwa [fullUnitaryConj_inverse U X hU] at h

/-- Full Physical Source plain Form conj for the stated finite source data. -/
theorem fullPhysicalSource_plainForm_conj [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (X : Operator D) (hU : Uᴴ * U = 1) :
    (∑ P, (ckgSourcePlainForm β (fullPhysicalGibbs U lam β) (fullNu lam)
      (fullPhysicalTransition U (A P)) (fullUnitaryConj U X)).re) =
      ∑ P, (ckgSourcePlainForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (fullPhysicalEnergyProposal U (A P))) X).re := by
  exact Finset.sum_congr rfl fun P _ => congrArg Complex.re
    (fullUnitaryConj_sourcePlainForm U (gibbsDiag lam β) β (fullNu lam)
      (fullTransition (fullPhysicalEnergyProposal U (A P))) X hU
      (fullGibbsDiag_posDef lam β))

/-- Full Physical Source damped Form conj for the stated finite source data. -/
theorem fullPhysicalSource_dampedForm_conj [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) (β : ℝ)
    (A : ι → Operator D) (X : Operator D) (hU : Uᴴ * U = 1) :
    (∑ P, (ckgSourceDampedForm β (fullPhysicalGibbs U lam β) (fullNu lam)
      (fullPhysicalTransition U (A P)) (fullUnitaryConj U X)).re) =
      ∑ P, (ckgSourceDampedForm β (gibbsDiag lam β) (fullNu lam)
        (fullTransition (fullPhysicalEnergyProposal U (A P))) X).re := by
  exact Finset.sum_congr rfl fun P _ => congrArg Complex.re
    (fullUnitaryConj_sourceDampedForm U (gibbsDiag lam β) β (fullNu lam)
      (fullTransition (fullPhysicalEnergyProposal U (A P))) X hU
      (fullGibbsDiag_posDef lam β))

/-- The same exact energy-coordinate gap bounds the physical normalized form. -/
theorem fullPhysicalSource_plainGap_form [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) {β : ℝ} (hβ : 0 < β)
    (A : ι → Operator D) (hU : Uᴴ * U = 1) :
    FormGapAtLeast
      (fun X => ∑ P, (ckgSourcePlainForm β (fullPhysicalGibbs U lam β) (fullNu lam)
        (fullPhysicalTransition U (A P)) X).re)
      (CFC.sqrt (fullPhysicalGibbs U lam β))
      (fullSourcePlainGap lam β (fun P => fullPhysicalEnergyProposal U (A P))) := by
  intro X
  have hg := fullSourcePlainGap_sourceForm lam hβ
    (fun P => fullPhysicalEnergyProposal U (A P)) (fullUnitaryConj Uᴴ X)
  have he := fullPhysicalSource_plainForm_conj U lam β A (fullUnitaryConj Uᴴ X) hU
  rw [fullUnitaryConj_inverse U X hU] at he
  dsimp only at hg
  rw [← he] at hg
  have hv := fullUnitaryConj_hsVar U (CFC.sqrt (gibbsDiag lam β))
    (fullUnitaryConj Uᴴ X) hU
  rw [fullUnitaryConj_inverse U X hU, ← fullPhysicalGibbs_sqrt U lam β hU] at hv
  rwa [hv]

/-- Full Physical Source damped Gap form for the stated finite source data. -/
theorem fullPhysicalSource_dampedGap_form [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) {β : ℝ} (hβ : 0 < β)
    (A : ι → Operator D) (hU : Uᴴ * U = 1) :
    FormGapAtLeast
      (fun X => ∑ P, (ckgSourceDampedForm β (fullPhysicalGibbs U lam β) (fullNu lam)
        (fullPhysicalTransition U (A P)) X).re)
      (CFC.sqrt (fullPhysicalGibbs U lam β))
      (fullSourceDampedGap lam β (fun P => fullPhysicalEnergyProposal U (A P))) := by
  intro X
  have hg := fullSourceDampedGap_sourceForm lam hβ
    (fun P => fullPhysicalEnergyProposal U (A P)) (fullUnitaryConj Uᴴ X)
  have he := fullPhysicalSource_dampedForm_conj U lam β A (fullUnitaryConj Uᴴ X) hU
  rw [fullUnitaryConj_inverse U X hU] at he
  dsimp only at hg
  rw [← he] at hg
  have hv := fullUnitaryConj_hsVar U (CFC.sqrt (gibbsDiag lam β))
    (fullUnitaryConj Uᴴ X) hU
  rw [fullUnitaryConj_inverse U X hU, ← fullPhysicalGibbs_sqrt U lam β hU] at hv
  rwa [hv]

/-- The established monomial theorem applies in an actual chosen energy basis;
the conclusion is a physical-coordinate form inequality for the original family. -/
theorem fullPhysicalSource_monomial_domination [Nonempty (Fin D)]
    (U : Operator D) (lam : Fin D → ℝ) (β : ℝ) (A : ι → Operator D)
    (hU : Uᴴ * U = 1)
    (hA : ∀ P, fullMatrixOneSparse (fullPhysicalEnergyProposal U (A P)))
    (X : Operator D) :
    (∑ P, (ckgSourceDampedForm β (fullPhysicalGibbs U lam β) (fullNu lam)
      (fullPhysicalTransition U (A P)) X).re) ≤
      3 / 2 * ∑ P, (ckgSourcePlainForm β (fullPhysicalGibbs U lam β) (fullNu lam)
        (fullPhysicalTransition U (A P)) X).re := by
  have he0 := fullPhysicalSource_plainForm_conj U lam β A (fullUnitaryConj Uᴴ X) hU
  have heg := fullPhysicalSource_dampedForm_conj U lam β A (fullUnitaryConj Uᴴ X) hU
  rw [fullUnitaryConj_inverse U X hU] at he0 heg
  rw [he0, heg, Finset.mul_sum]
  exact Finset.sum_le_sum fun P _ => fullMonomial_sourceDomination lam β
    (fullPhysicalEnergyProposal U (A P)) (hA P) (fullUnitaryConj Uᴴ X)

end Qatlib.Concepts.GibbsSource.SourceForms
