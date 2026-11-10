/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.Entanglement.Separability.EntanglementLOCCDefs
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.Entanglement.Separability

open Qatlib
open scoped BigOperators ComplexOrder

variable {D E n : ℕ}

noncomputable def secondMarginal {D E : ℕ} (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Operator E :=
  fun i j => ∑ a : Fin D, A (a, i) (a, j)

noncomputable def secondMarginalState {D E : ℕ} (ψ : QState (Fin D × Fin E)) : Operator E :=
  secondMarginal (outerProduct ψ)

theorem secondMarginal_hermitian {D E : ℕ} {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hA : A.IsHermitian) : (secondMarginal A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h : ∀ a : Fin D, (starRingEnd ℂ) (A (a, j) (a, i)) = A (a, i) (a, j) := by
    intro a
    simpa [RCLike.star_def] using hA.apply (a, i) (a, j)
  simp only [secondMarginal, RCLike.star_def]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => h a

theorem secondMarginalState_hermitian {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    (secondMarginalState ψ).IsHermitian := by
  exact secondMarginal_hermitian (outerProduct_isHermitian ψ)

theorem partialTranspose_hermitian {D E : ℕ}
    {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ} (hA : A.IsHermitian) :
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.PartialTranspose A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h : star (A (j.1, i.2) (i.1, j.2)) = A (i.1, j.2) (j.1, i.2) :=
    hA.apply (i.1, j.2) (j.1, i.2)
  simp only [Qatlib.Concepts.FiniteLocc.LOCCProgram.PartialTranspose, Matrix.of_apply]
  exact h

theorem partialTrace_outerProduct_hermitian {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    (PartialTrace (outerProduct ψ)).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [PartialTrace, outerProduct_apply, RCLike.star_def]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul]
  have h2 : (starRingEnd ℂ) ((starRingEnd ℂ) (ψ (i, a))) = ψ (i, a) := by
    simp
  rw [h2]
  ring

structure KrausInstrument (D n : ℕ) where

  op : Fin n → Operator D

  hcomplete : ∑ i, (op i).conjTranspose * (op i) = 1

noncomputable def krausBranch {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (K.op i) (1 : Operator E)) ψ

noncomputable def krausBranchMass {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : ℝ :=
  ∑ j, ‖krausBranch ψ K i j‖ ^ 2

noncomputable def krausBranchReduced {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : Operator D :=
  PartialTrace (outerProduct (krausBranch ψ K i))

theorem krausBranchReduced_hermitian {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) :
    (krausBranchReduced ψ K i).IsHermitian :=
  partialTrace_outerProduct_hermitian (krausBranch ψ K i)

noncomputable def krausAverageState {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  ∑ i, outerProduct (krausBranch ψ K i)

noncomputable def krausBranchSpectrum {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : Fin D → ℝ :=
  (krausBranchReduced_hermitian ψ K i).eigenvalues

noncomputable def secondMarginalSpectrum {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    Fin E → ℝ :=
  (secondMarginalState_hermitian ψ).eigenvalues

noncomputable def feedbackUnitary {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    Matrix.unitaryGroup (Fin E) ℂ :=
  (secondMarginalState_hermitian ψ).eigenvectorUnitary

noncomputable def feedbackState {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (1 : Operator D) (feedbackUnitary ψ).val) ψ

noncomputable def partialTransposeEigenvalues {D E : ℕ}
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : ρ.IsHermitian) :
    Fin D × Fin E → ℝ :=
  (partialTranspose_hermitian hρ).eigenvalues

noncomputable def negativity {D E : ℕ}
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  ∑ j, max (-(partialTransposeEigenvalues ρ hρ j)) 0

end Qatlib.Concepts.Entanglement.Separability
