/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Entanglement.Separability.EntanglementLOCC
import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance

/-!
# Kraus branches and partial-transpose negativity

This module defines the second marginal, complete finite `KrausInstrument` families, their
unnormalized branch states and masses, and the averaged output operator. Hermiticity results
support eigenvalue definitions for branch reduced operators and second marginals. The
local-operation setting is standard in [Wilde2017].

`feedbackUnitary` and `feedbackState` select a right-local unitary from the spectral
decomposition of the second marginal. `partialTransposeEigenvalues` and `negativity` define the
sum of the negative parts of the partial-transpose spectrum, as in [VidalWerner2002].

## Main statements

* `KrausInstrument`: a finite operator family with the Kraus completeness relation.
* `krausBranchMass`: the squared norm of an unnormalized branch.
* `krausAverageState`: the sum of branch outer products.
* `negativity`: the negative spectral mass of the partial transpose.

## References

* [Wilde, 2017][Wilde2017]
* [Vidal and Werner, 2002][VidalWerner2002]
-/

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

/-- The second-subsystem marginal of a bipartite matrix, obtained by summing over the first
subsystem's diagonal indices. -/
noncomputable def secondMarginal {D E : ℕ} (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    Operator E :=
  fun i j => ∑ a : Fin D, A (a, i) (a, j)

/-- The second marginal of the outer product of a bipartite pure-state vector. -/
noncomputable def secondMarginalState {D E : ℕ} (ψ : QState (Fin D × Fin E)) : Operator E :=
  secondMarginal (outerProduct ψ)

/-- Taking the second marginal preserves Hermiticity. -/
theorem secondMarginal_hermitian {D E : ℕ} {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ}
    (hA : A.IsHermitian) : (secondMarginal A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h : ∀ a : Fin D, (starRingEnd ℂ) (A (a, j) (a, i)) = A (a, i) (a, j) := by
    intro a
    simpa [RCLike.star_def] using hA.apply (a, i) (a, j)
  simp only [secondMarginal, RCLike.star_def]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => h a

/-- The second marginal of a pure-state outer product is Hermitian. -/
theorem secondMarginalState_hermitian {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    (secondMarginalState ψ).IsHermitian := by
  exact secondMarginal_hermitian (outerProduct_isHermitian ψ)

/-- Partial transposition preserves Hermiticity of a bipartite matrix. -/
theorem partialTranspose_hermitian {D E : ℕ}
    {A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ} (hA : A.IsHermitian) :
    (Qatlib.Concepts.FiniteLocc.LOCCProgram.PartialTranspose A).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  have h : star (A (j.1, i.2) (i.1, j.2)) = A (i.1, j.2) (j.1, i.2) :=
    hA.apply (i.1, j.2) (j.1, i.2)
  simp only [Qatlib.Concepts.FiniteLocc.LOCCProgram.PartialTranspose, Matrix.of_apply]
  exact h

/-- The first marginal of a pure-state outer product is Hermitian. -/
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

/-- A finite family of local operators satisfying the completeness relation `∑ i, (op
i).conjTranspose * op i = 1`. -/
structure KrausInstrument (D n : ℕ) where

  op : Fin n → Operator D

  hcomplete : ∑ i, (op i).conjTranspose * (op i) = 1

/-- The unnormalized branch vector obtained by applying Kraus operator `i` to the left
subsystem. -/
noncomputable def krausBranch {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (K.op i) (1 : Operator E)) ψ

/-- The sum of squared amplitude norms of an unnormalized Kraus branch. -/
noncomputable def krausBranchMass {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : ℝ :=
  ∑ j, ‖krausBranch ψ K i j‖ ^ 2

/-- The first reduced operator of the outer product of an unnormalized Kraus branch. -/
noncomputable def krausBranchReduced {D E : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : Operator D :=
  PartialTrace (outerProduct (krausBranch ψ K i))

/-- The first reduced operator of a Kraus branch is Hermitian. -/
theorem krausBranchReduced_hermitian {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) :
    (krausBranchReduced ψ K i).IsHermitian :=
  partialTrace_outerProduct_hermitian (krausBranch ψ K i)

/-- The sum of the outer products of all unnormalized Kraus branch vectors. -/
noncomputable def krausAverageState {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
  ∑ i, outerProduct (krausBranch ψ K i)

/-- The real eigenvalues of the first reduced operator of an unnormalized Kraus branch. -/
noncomputable def krausBranchSpectrum {D E n : ℕ} (ψ : QState (Fin D × Fin E))
    (K : KrausInstrument D n) (i : Fin n) : Fin D → ℝ :=
  (krausBranchReduced_hermitian ψ K i).eigenvalues

/-- The real eigenvalues of the second marginal of a pure-state outer product. -/
noncomputable def secondMarginalSpectrum {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    Fin E → ℝ :=
  (secondMarginalState_hermitian ψ).eigenvalues

/-- The eigenvector unitary of the Hermitian second marginal. -/
noncomputable def feedbackUnitary {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    Matrix.unitaryGroup (Fin E) ℂ :=
  (secondMarginalState_hermitian ψ).eigenvectorUnitary

/-- The state obtained by applying the second marginal's eigenvector unitary to the right
subsystem. -/
noncomputable def feedbackState {D E : ℕ} (ψ : QState (Fin D × Fin E)) :
    QState (Fin D × Fin E) :=
  ApplyGate (TensorGate (1 : Operator D) (feedbackUnitary ψ).val) ψ

/-- The real eigenvalues of the partial transpose of a Hermitian bipartite operator. -/
noncomputable def partialTransposeEigenvalues {D E : ℕ}
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : ρ.IsHermitian) :
    Fin D × Fin E → ℝ :=
  (partialTranspose_hermitian hρ).eigenvalues

/-- The sum of the negative parts of the eigenvalues of the partial transpose. This is the
negativity measure on density operators [VidalWerner2002]. -/
noncomputable def negativity {D E : ℕ}
    (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (hρ : ρ.IsHermitian) : ℝ :=
  ∑ j, max (-(partialTransposeEigenvalues ρ hρ j)) 0

end Qatlib.Concepts.Entanglement.Separability
