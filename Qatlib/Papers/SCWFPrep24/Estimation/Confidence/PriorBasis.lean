/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
import Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PairedPrior

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

/-!
# Prior Basis

A known full address bijection bijectively relabels the same physical phase assignments.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix ComplexOrder
namespace Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.GridMatching
open Qatlib.Papers.SCWFPrep24.Estimation.Confidence.CoherentInput
open Qatlib.Concepts.SpinorSampling.NativeRecords.CountCohorts
open Qatlib.Concepts.SpinorSampling.NativeRecords.SharedCopyPhases

/-- A known full address bijection bijectively relabels the same physical phase assignments. -/
def phaseAssignmentEquiv {A B : Type*} (e : A ≃ B) (Q : ℕ) : (A → Fin (Q+1)) ≃ (B → Fin (Q+1)) where
  toFun ω := fun b => ω (e.symm b)
  invFun θ := fun a => θ (e a)
  left_inv ω := by funext a; simp
  right_inv θ := by funext b; simp

/-- The known phase-label permutation has its literal source-coordinate action. -/
theorem phaseAssignment_apply {A B : Type*} (e : A ≃ B) (Q : ℕ) (ω : A → Fin (Q+1)) (b : B) :
    phaseAssignmentEquiv e Q ω b=ω (e.symm b) := rfl

/-- The complete shared-phase quantum prior is unchanged by a known complete address relabeling. -/
theorem phaseMean_address_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (Q : ℕ) (f : (B → Fin (Q+1)) → ℂ) :
    phaseMean Q (fun ω : A → Fin (Q+1) => f (phaseAssignmentEquiv e Q ω))=phaseMean Q f := by
  simp only [phaseMean,Finset.prod_const,Finset.card_univ,Fintype.card_congr e]
  exact Equiv.sum_comp (phaseAssignmentEquiv e Q)
    (fun θ => (1/(Q+1 : ℕ) : ℂ)^(Fintype.card B)*f θ)

/-- All complete original Q-copy basis labels are relabeled by the same address bijection and the identity spin map. -/
def copyBasisEquiv {A B : Type*} (e : A ≃ B) (Q : ℕ) :
    (Fin Q → A × Bool) ≃ (Fin Q → B × Bool) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr e (Equiv.refl Bool))

/-- Every complete original input coordinate keeps all spin labels and changes only its known address name. -/
theorem copyBasis_apply {A B : Type*} (e : A ≃ B) (Q : ℕ) (x : Fin Q → A × Bool) :
    copyBasisEquiv e Q x=(fun j => (e (x j).1,(x j).2)) := by
  funext j
  rfl

/-- The same realized original input vector is preserved, with its actual shared phase assignment, at every complete Q-copy coordinate. -/
theorem copies_realization_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (ψ : B → Bool → ℂ) (Q : ℕ) (ω : A → Fin (Q+1)) (x : Fin Q → A × Bool) :
    originalSuppliedCopies (fun a => ψ (e a)) Q ω x=
      originalSuppliedCopies ψ Q (phaseAssignmentEquiv e Q ω) (copyBasisEquiv e Q x) := by
  simpa only [phaseAssignment_apply,Equiv.symm_apply_apply,copyBasis_apply] using
    original_copies_address_equiv e ψ Q (phaseAssignmentEquiv e Q ω) x

/-- Complete original shared-phase density entries, including every unmeasured address and spin register, agree under the known full basis permutation. -/
theorem shared_density_address_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (ψ : B → Bool → ℂ) (Q : ℕ) (x y : Fin Q → A × Bool) :
    phaseMean Q (fun ω => originalSuppliedCopies (fun a => ψ (e a)) Q ω x*
      star (originalSuppliedCopies (fun a => ψ (e a)) Q ω y))=
    phaseMean Q (fun θ => originalSuppliedCopies ψ Q θ (copyBasisEquiv e Q x)*
      star (originalSuppliedCopies ψ Q θ (copyBasisEquiv e Q y))) := by
  simp_rw [copies_realization_equiv e ψ Q]
  exact phaseMean_address_equiv e Q (fun θ => originalSuppliedCopies ψ Q θ (copyBasisEquiv e Q x)*
    star (originalSuppliedCopies ψ Q θ (copyBasisEquiv e Q y)))

/-- The literal original-grid input prior chooses one actual pair-sign field and one original phase field across all Q copies. -/
def priorOnGrid {A E : Type} [Fintype A] [Fintype E] [DecidableEq E]
    (e : A ≃ E × Bool) (b ρ : ℝ) (Q : ℕ) : Matrix (Fin Q → A × Bool) (Fin Q → A × Bool) ℂ :=
  fun x y => ∑ κ : E → Fin 4,(pairedSignLaw ρ κ : ℂ)*phaseMean Q
    (fun ω => originalSuppliedCopies (fun a => pairedWeakSpin b κ (e a)) Q ω x*
      star (originalSuppliedCopies (fun a => pairedWeakSpin b κ (e a)) Q ω y))

/-- The actual original-grid quantum prior is the same complete matching prior in a known full basis, rather than a measured-address marginal. -/
theorem priorOnGrid_entry {A E : Type} [Fintype A] [Fintype E] [DecidableEq E]
    (e : A ≃ E × Bool) (b ρ : ℝ) (Q : ℕ) (x y : Fin Q → A × Bool) :
    priorOnGrid e b ρ Q x y=physicalPrior b ρ Q (copyBasisEquiv e Q x) (copyBasisEquiv e Q y) := by
  simp only [priorOnGrid,physicalPrior]
  simp_rw [shared_density_address_equiv e]

/-- A complete finite basis for the original grid prior retains all coordinates; only known basis names are chosen. -/
def encodedGridPrior {A E : Type} [Fintype A] [Fintype E] [DecidableEq E]
    (e : A ≃ E × Bool) (b ρ : ℝ) (Q : ℕ) :
    Qatlib.Foundations.PureStateMath.Operator (Fintype.card (Fin Q → (E × Bool) × Bool)) :=
  (priorOnGrid e b ρ Q).submatrix
    ((copyBasisEquiv e Q).symm ∘ (Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm)
    ((copyBasisEquiv e Q).symm ∘ (Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm)

/-- The actual whole original-grid prior equals the proved matching prior after a complete known finite coordinate bijection. -/
theorem encodedGridPrior_eq {A E : Type} [Fintype A] [Fintype E] [DecidableEq E]
    (e : A ≃ E × Bool) (b ρ : ℝ) (Q : ℕ) : encodedGridPrior e b ρ Q=encodedPhysicalPrior (E := E) b ρ Q := by
  ext i j
  simp only [encodedGridPrior,Matrix.submatrix_apply,Function.comp_apply,priorOnGrid_entry,
    Equiv.apply_symm_apply,encodedPhysicalPrior]

/-- The source's actual complete original-grid input priors retain the full original all-Q squared-fidelity bound, without a preliminary address observation. -/
theorem original_grid_full_fidelity {A E : Type} [Fintype A] [Fintype E] [DecidableEq E] [Nonempty E]
    (e : A ≃ E × Bool) (N Q : ℕ) (hN : 256≤N) :
    Real.exp (-(216/7 : ℝ)*(128/((N : ℝ)^2))*
      min (Q : ℝ) ((Q : ℝ)*((Q : ℝ)-1)/(Fintype.card A : ℝ)))≤
    (Qatlib.Concepts.MixedFidelity.FidelityMetric.Froot
      (encodedGridPrior e (128/((N : ℝ)^2)) (3/4) Q)
      (encodedGridPrior e (128/((N : ℝ)^2)) (-3/4) Q))^2 := by
  rw [encodedGridPrior_eq,encodedGridPrior_eq,Fintype.card_congr e]
  exact original_weak_full_fidelity N Q hN

/-- The actual complete original-grid prior is a legal density operator, derived from its same physical source and complete basis bijection. -/
theorem encodedGridPrior_legal {A E : Type} [Fintype A] [Fintype E] [DecidableEq E] [Nonempty E]
    (e : A ≃ E × Bool) (b ρ : ℝ) (Q : ℕ) (hb0 : 0≤b) (hb1 : b≤1) (hlo : -1≤ρ) (hhi : ρ≤1) :
    Qatlib.Foundations.PureStateMath.IsDensityOperator (encodedGridPrior e b ρ Q) := by
  rw [encodedGridPrior_eq]
  have hp := physicalPrior_legal (E := E) b ρ Q hb0 hb1 hlo hhi
  refine ⟨hp.1.submatrix _,?_⟩
  change (∑ i,physicalPrior (E := E) b ρ Q
    ((Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm i)
    ((Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm i))=1
  exact (Equiv.sum_comp (Fintype.equivFin (Fin Q → (E × Bool) × Bool)).symm
    (fun x => physicalPrior (E := E) b ρ Q x x)).trans hp.2

end Qatlib.Papers.SCWFPrep24.Estimation.Confidence.PriorBasis
